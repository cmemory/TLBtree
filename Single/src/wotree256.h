/*
    log free wbtree with 256B nodesize, nonclass version of wbtree_slotonly
    Copyright(c) Luo Yongping. THIS SOFTWARE COMES WITH NO WARRANTIES, 
    USE AT YOUR OWN RISK!
*/

#ifndef __WOTREE256__
#define __WOTREE256__

#include <cstdint>
#include <cstring>
#include <string>
#include <cstdio>

#include "flush.h"
#include "pmallocator.h"

namespace wotree256 {
using std::string;
constexpr int CARDINALITY = 13;
constexpr int UNDERFLOW_CARD = 4;

struct state_t {
    struct statefield_t { // totally 8 bytes
        // 用于排序的slot数组，每个slot占用4位表示第几个slot，这里一共可以存储13个slot。
        uint64_t slotArray       : 52;
        // slotArray中元素个数，也代表后面slot槽位占用个数。
        uint64_t count           : 4;
        uint64_t sibling_version : 1;
        uint64_t latch           : 1;
        uint64_t node_version    : 6; 
    };
    // the real data field of state
    union {
        uint64_t pack;      // to do 8 bytes assignment
        statefield_t unpack;// to facilite accessing subfields
    };
    
public:
    state_t(uint64_t s = 0): pack(s) {}

    // 读取slotArray第idx个的数值，这个值代表后面是第几个slot。
    inline int8_t read(int8_t idx) const {
        // slotArray左移到高52位
        uint64_t p = this->unpack.slotArray << 12;
        // 取第几个4位的值。如idx=0，则0xf向左移60位，构造最高4位为1的掩码；然后与p与操作提取，再右移60位，从而提取第0个数值代表的槽位。
        return (p & ((uint64_t)0xf << ((15 - idx) * 4))) >> ((15 - idx) * 4);
    }

    // 非线程安全
    inline int8_t alloc() {
        // 初始化 occupy 数组，大小为 CARDINALITY，初值为 0，用于跟踪每个槽位是否被占用。
        int8_t occupy[CARDINALITY] = {0};
        // 根据slotArray判断后面对应槽位是否被占用
        for(int64_t i = 0; i < unpack.count; i++) {
            occupy[read(i)] = 1; 
        }
        // 选择后面第一个未被占用的槽分配
        for(int i = 0; i < CARDINALITY; i++) {
            if(occupy[i] == 0) return i;
        }
        #ifdef DEBUG
            assert(false);
        #endif
        // 如果槽都被占用了返回这个。理论上不会走到这里
        return CARDINALITY; // never be here
    }

    // 参数：slot表示后面数据是第几个槽位。idx表示槽位下标索引放在 slotArray 哪个位置上。
    inline uint64_t add(int8_t idx, int8_t slot) {
        // 使用当前状态 this->pack 构建影子 new_state，不影响当前状态下操作。
        state_t new_state(this->pack);

        // update bit fields
        uint64_t p      = this->unpack.slotArray << 12;
        uint64_t mask   = 0xffffffffffffffff >> (idx * 4);
        // slot 移动到 指定idx的位置上。
        uint64_t add_value = (uint64_t)slot << ((15 - idx) * 4);
        // (p & (~mask) 表示高位，(p & mask) >> 4 低位
        // 实际上是在idx插入4位的索引元素，前面不动，idx后面的向后移4位，腾出空间来写新的元素
        new_state.unpack.slotArray = ((p & (~mask)) + add_value + ((p & mask) >> 4)) >> 12;
        new_state.unpack.count++;

        return new_state.pack;
    }

    inline uint64_t remove(int idx) { // delete a slot id at position idx
        state_t new_state(this->pack);
        // update bit fields
        uint64_t p      = this->unpack.slotArray << 12;
        uint64_t mask   = 0xffffffffffffffff >> (idx * 4);
        // remove就是把idx后面的数据往前挪4位覆盖掉idx值。
        new_state.unpack.slotArray = ((p & ~mask) + ((p & (mask>>4)) << 4)) >> 12;
        new_state.unpack.count--;

        return new_state.pack;
    }

    // 更add操作一样，只是最后不更新count的数量。
    inline uint64_t append(int8_t idx, int8_t slot) {
        // Append the record at slotid, append the slotArray entry, but DO NOT modify the count
        state_t new_state(this->pack);

        // update bit fields
        uint64_t p      = this->unpack.slotArray << 12;
        uint64_t mask   = 0xffffffffffffffff >> (idx * 4);
        uint64_t add_value = (uint64_t)slot << ((15 - idx) * 4);
        new_state.unpack.slotArray = ((p & (~mask)) + add_value + ((p & mask) >> 4)) >> 12;

        return new_state.pack;
    }
};

// 一个节点占用256字节
//
class Node {
public:
    // First Cache Line
    // 8字节
    state_t state_;      // a very complex and compact state field
    // 8字节指针，指向当前节点最小的那个key？
    char * leftmost_ptr_;// the left most child of current node
    // Record，key和val指针各8字节，这里数组32字节
    Record siblings_[2]; // shadow sibling of current node
    // Slots
    // 16*13= 208字节
    // 13个记录构造成14叉树，最左子树指针由 leftmost_ptr_ 指向，后面指针依次存储在 recs_ 中。
    Record recs_[CARDINALITY];

    friend class wbtree;

public:
    Node(bool isleaf = false): state_(0), leftmost_ptr_(NULL) {
        siblings_[0] = {MAX_KEY, NULL};
        siblings_[1] = {MAX_KEY, NULL};
    }

    // new操作符重载，自定义内存分配，用于PM分配
    void *operator new(size_t size) {
        void * ret = galc->malloc(size);
        return ret;
    }

    // 当前节点中插入kv，有split则返回true，以及 split_k 和 split_node
    bool store(_key_t k, uint64_t v, _key_t & split_k, Node * & split_node) {
        // 如果当前节点满了，则需要split
        if(state_.unpack.count == CARDINALITY) { // should split the node
            // split后两个节点各一半元素（6个），最中间的元素及为返回的split_k
            uint64_t m = state_.unpack.count / 2;
            split_k = recs_[state_.read(m)].key;

            // copy half of the records into split node
            int8_t j = 0;
            state_t new_state = state_;
            if(leftmost_ptr_ == NULL) {
                // leftmost_ptr_ 为空，表示叶子节点，split后还是叶子节点，不需要设置？
                // 创建新节点，把后面半数slot数据读出来写入，读出来有序的，所以直接顺序写入（0号位置写0，1号位置写1）
                split_node = new Node();
                for(int i = m; i < state_.unpack.count; i++) {
                    int8_t slotid = state_.read(i);
                    split_node->append(recs_[slotid], j, j);
                    j += 1;
                }

                // 原节点移除了部分元素，更新原节点count。
                new_state.unpack.count -= j;
            } else {
                // leftmost_ptr_ 不为空，split后也不是叶子节点，所有要设置？
                int8_t slotid = state_.read(m);
                split_node = new Node();
                split_node->leftmost_ptr_ = recs_[slotid].val;

                for(int i = m + 1; i < state_.unpack.count; i++) {
                    slotid = state_.read(i);
                    split_node->append(recs_[slotid], j, j);
                    j += 1;
                }

                new_state.unpack.count -= (j + 1);
            }
            split_node->state_.unpack.count = j;
            // 设置新节点的 兄弟节点 版本（有两个版本0和1循环用，用于查询？）
            split_node->state_.unpack.sibling_version = 0;
            // the sibling node of current node pointed by split_node
            // 当前节点的影子兄弟节点赋给新节点（就是在链表两个节点间加入新节点串起来，这里改指针）
            split_node->siblings_[0] = siblings_[state_.unpack.sibling_version];
            // 使用 clwb 函数将分裂节点的头部和记录持久化到存储中。
            // clwb 确保这些数据被写入到非易失性存储，以防数据丢失。
            // 64 表示持久化头部的大小+第一个record的大小，sizeof(Record) * (j - 1) 持久化了新节点中剩余记录。
            clwb(split_node, 64); // persist header
            clwb(&split_node->recs_[1], sizeof(Record) * (j - 1)); // persist all the inserted records
            
            // the split node is installed as the shadow sibling of current node
            // 新节点数据持久话后，更新当前节点的兄弟节点为新节点
            siblings_[(state_.unpack.sibling_version + 1) % 2] = {split_k, (char *)galc->relative(split_node)};
            // persist_assign the state field
            // 更新新节点状态版本，类似于两阶段提交？所以搞两个sibling版本，中间过程失败对原数据无影响。
            new_state.unpack.sibling_version = (state_.unpack.sibling_version + 1) % 2;

            // 使用 mfence 函数作为内存屏障，确保内存屏障之前的所有写操作都已完成并持久化到存储中。确保数据一致性和持久性。
            mfence(); // a barrier here to make sure all the update is persisted to storage

            // 持久化状态，状态写完表示split完成
            persist_assign(&(state_.pack), new_state.pack);
            
            // go on the insertion
            if(k < split_k) {
                // 插入的节点小于 split_k，则在原节点（即当前节点）插入
                insertone(k, (char *)v);
            } else {
                // 插入的节点大于 split_k，则在新节点 split_node 插入
                split_node->insertone(k, (char *)v);
            }
            // 插入成功，有节点split，最终返回true，同时返回 split_k 和 split_node
            return true;
        } else {
            // 无节点拆分，直接当前节点插入，返回false。
            insertone(k, (char *)v);
            return false;
        }
    }

    // 根据给定的键 k 查找对应的子节点或记录值，当前节点中寻找记录，没有则找子节点递归处理
    char * get_child(_key_t k) {
        // split过有兄弟节点，如果k >= sibling.key，则递归取兄弟节点找
        Record &sibling = siblings_[state_.unpack.sibling_version];

        if(k >= sibling.key) { // if the node has splitted and k to find is in next node
            // 相对地址转绝对地址
            Node * sib_node = (Node *)galc->absolute(sibling.val);
            return sib_node->get_child(k);
        }

        if(leftmost_ptr_ == NULL) {
            // 为空说明是叶节点，直接当前节点找
            // 遍历找到第一个>=k的位置
            int8_t slotid = 0;
            for(int i = 0; i < state_.unpack.count; i++) {
                slotid = state_.read(i);
                if(recs_[slotid].key >= k) {
                    break;
                }
            }

            // 找到数据返回，没找到则说明没有返回NULL。
            if (recs_[slotid].key == k && state_.unpack.count > 0)
                return recs_[slotid].val;
            else 
                return NULL;
        } else {
            // 非空，不是叶子节点，有左最小子节点
            // 找到第一个大于k的位置
            int8_t slotid = 0, pos = state_.unpack.count;
            for(int i = 0; i < state_.unpack.count; i++) {
                slotid = state_.read(i);
                if(recs_[slotid].key > k) {
                    pos = i;
                    break;
                }
            }

            if (pos == 0) // all the key is bigger than k
                // 所有key都>k，则返回左最小子节点，后面递归往下找
                return leftmost_ptr_;
            else
                // 找到了第一个>k的位置，则前面位置的指针指向的子节点即为递归查找的子节点。
                return recs_[state_.read(pos - 1)].val;
        }
    }

    bool update(_key_t k, uint64_t v) {
        // 遍历找到第一个>=k的位置。
        uint64_t slotid = 0;
        for(int i = 0; i < state_.unpack.count; i++) {
            slotid = state_.read(i);
            if(recs_[slotid].key >= k) {
                break;
            }
        }

        // 如果找到的位置key==k，则更新并持久化，并返回true，否则返回false
        if (recs_[slotid].key == k) {
            recs_[slotid].val = (char *)v;
            clwb(&recs_[slotid], sizeof(Record));
            return true;
        } else {
            return false;
        }
    }

    bool remove(_key_t k) {
        // Non-SMO delete takes only one clwb
        // 有分裂的兄弟节点，且删除的k在后面兄弟节点中，则兄弟节点中递归处理删除。
        Record &sibling = siblings_[state_.unpack.sibling_version];
        if(k >= sibling.key) { // if the node has splitted and k to find is in next node 
            Node * sib_node = (Node *)galc->absolute(sibling.val);
            return sib_node->remove(k);
        }

        if(leftmost_ptr_ == NULL) {
            // 为空，叶子节点
            // 遍历找到第一个>=k的位置
            int8_t idx, slotid;
            for(idx = 0; idx < state_.unpack.count; idx++) {
                slotid = state_.read(idx);
                if(recs_[slotid].key >= k)
                    break;
            }

            // 找到了，删除并原子持久化。数据未删，后面写可直接覆盖。
            if(recs_[slotid].key == k) {
                uint64_t newpack = state_.remove(idx);
                persist_assign(&(state_.pack), newpack);
                return true;
            } else {
                return false;
            }
        } else {
            // 非空，中间节点，不需要递归处理删除？
            int8_t idx;
            for(idx = 0; idx < state_.unpack.count; idx++) {
                int8_t slotid = state_.read(idx);
                if(recs_[slotid].key > k) 
                    break;
            }
            /* NOTICE: 
                * We will never remove the leftmost child in our wbtree design
                * So the idx here must be larger than 0
                */
            // 根据设计，不会删除左最小子节点。因此，idx 一定大于 0？
            uint64_t newpack = state_.remove(idx - 1);
            persist_assign(&(state_.pack), newpack);

            return true;
        }
    }

    void print(string prefix, bool recursively) const {
        printf("%s[%lx(%ld) ", prefix.c_str(), state_.unpack.slotArray, state_.unpack.count);

        for(int i = 0; i < state_.unpack.count; i++) {
            printf("%d ", state_.read(i));
        }

        for(int i = 0; i < state_.unpack.count; i++) {
            int8_t slotid = state_.read(i);
            printf("(%ld 0x%lx) ", recs_[slotid].key, (uint64_t)recs_[slotid].val);
        }
        printf("]\n");

        if(recursively && leftmost_ptr_ != NULL) {
            Node * child = (Node *)galc->absolute(leftmost_ptr_);
            child->print(prefix + "    ", recursively);

            for(int i = 0; i < state_.unpack.count; i++) {
                Node * child = (Node *)galc->absolute(recs_[state_.read(i)].val);
                child->print(prefix + "    ", recursively);
            }
        }
    }

    // 获取兄弟节点
    void get_sibling(_key_t & k, Node ** &sibling) {
        // 根据版本取兄弟节点记录，然后根据val指针取对应节点数据。
        Record &sib = siblings_[state_.unpack.sibling_version];
        k = sib.key;
        sibling = (Node **)&(sib.val);
    }

public:
    void insertone(_key_t key, char * right) {
        // 遍历 slotArray 找到第一个大于key的位置，即为key插入位置。
        int8_t idx;
        for(idx = 0; idx < state_.unpack.count; idx++) {
            int8_t slotid = state_.read(idx);
            if(key < recs_[slotid].key) {
                break;
            }
        }
        
        // insert and flush the kv
        // 在后面slot中找第一个空的槽用于写record
        int8_t slotid = state_.alloc(); // alloc a slot in the node
        // 写record并持久化
        recs_[slotid] = {key, (char *) right};
        clwb(&recs_[slotid], sizeof(Record));
        mfence();

        //write_version++;

        // atomically update the state
        // slotid 写入排序的 slotArray 中并持久化（copy后原子更新）
        uint64_t new_pack = state_.add(idx, slotid);
        persist_assign(&(state_.pack), new_pack);
    }

    // 记录写入 slot 及 slotArray
    void append(Record r, int8_t slotid, int8_t pos) {
        recs_[slotid] = r;
        // slotid 插入到 slotArray 的 pos 位置，没有更新count
        state_.pack = state_.append(pos, slotid);
    }

    // 将 right 节点的数据和状态合并到 left 节点，更新 left 节点的状态，并释放 right 节点。
    static void merge(Node * left, Node * right) {
        // 有右边节点往左合并，则 left 的 sibling 必然不为空。
        // 这里 sibling 实际上就是 right 最左节点吧？
        Record & sibling = left->siblings_[left->state_.unpack.sibling_version];

        state_t new_state = left->state_;
        // 这里应该是 right->leftmost_ptr_ != NULL ？
        if(left->leftmost_ptr_ != NULL) { // insert the leftmost_ptr of the right node
            // 如果 leftmost_ptr_ 不为空，非叶子节点，处理节点合并
            int8_t slotid = new_state.alloc();
            // sibling.key 实际上是 right 最左节点的key吧，所以这里直接构造加入
            left->append({sibling.key, right->leftmost_ptr_}, slotid, new_state.unpack.count);
            new_state.pack = new_state.add(new_state.unpack.count, slotid);
        }
        // right 的 recs_ 数组指向的节点合并到left中
        for(int i = 0; i < right->state_.unpack.count; i++) {
            int8_t slotid = new_state.alloc();
            left->append(right->recs_[right->state_.read(i)], slotid, new_state.unpack.count);
            new_state.pack = new_state.add(new_state.unpack.count, slotid);;
        }

        // right的兄弟节点赋值给left的兄弟节点
        Record tmp = right->siblings_[right->state_.unpack.sibling_version];
        left->siblings_[(left->state_.unpack.sibling_version + 1) % 2] = tmp;
        new_state.unpack.sibling_version = (left->state_.unpack.sibling_version + 1) % 2;

        // 持久化处理
        clwb(left, sizeof(Node)); // persist the whole leaf node

        // persist_assign the state_ field
        mfence();
        // head更新并持久化
        left->state_.pack = new_state.pack;
        clwb(left, 64);

        // 释放空间，会有PM泄漏
        galc->free(right); // WARNING: persistent memory leak here
    }

    // 当前节点中，获取 k对应节点的 左右孩子节点（保证返回的左节点元素都小于k，右节点元素都大于k）
    void get_lrchild(_key_t k, Node * & left, Node * & right) {
        int16_t i = 0;
        // 遍历 slotArray，根据 slotid 查询到对应记录的key，找到第一个大于k的slot
        for( ; i < state_.unpack.count; i++) {
            int8_t slotid = state_.read(i);
            if(recs_[slotid].key > k)
                break;
        }

        if(i == 0) {
            // i=0，说明所有的key都>k，即没有左孩子
            left = NULL;
        } else if(i == 1) {
            // i=1，只有一个比k小，直接指向最左边的子孩子即可
            left = (Node *)galc->absolute(leftmost_ptr_);
        } else {
            // i对应的是第一个比k大的元素的右子树，i-1对应的是前一个元素的右子树，
            // 前一个元素一定比k小，所以前一个元素的右子树中有可能有大于k的元素，
            // 但是前一个元素的左子树即i-2对应的树所有元素一定都比k小。
            left = (Node *)galc->absolute(recs_[state_.read(i - 2)].val);
        }

        if(i == state_.unpack.count) {
            // 所有key都<k，没有右孩子
            right = NULL;
        } else {
            // 第一个比k大的slot即i指向的
            right = (Node *)galc->absolute(recs_[state_.read(i)].val);
        }
    }
};

extern bool insert_recursive(Node * n, _key_t k, uint64_t v, _key_t &split_k, 
                                Node * &split_node, int8_t &level);
extern bool remove_recursive(Node * n, _key_t k);
extern bool find(Node ** rootPtr, _key_t key, uint64_t &val);
extern res_t insert(Node ** rootPtr, _key_t key, uint64_t val, int threshold);
extern bool update(Node ** rootPtr, _key_t key, uint64_t val);
extern bool remove(Node ** rootPtr, _key_t key);
extern void printAll(Node ** rootPtr);

}
#endif // __WOTREE256__