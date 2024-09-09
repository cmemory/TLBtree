/*  fixtree.h - A search-optimized fixed tree
    Copyright(c) 2020 Luo Yongping. THIS SOFTWARE COMES WITH NO WARRANTIES, 
    USE AT YOUR OWN RISK!
*/

#ifndef __FIXTREE__
#define __FIXTREE__

#include <cstdio>
#include <cstdint>
#include <cmath>
#include <vector>
#include <cassert>
#include <cstring>

#include "flush.h"
#include "pmallocator.h"

namespace fixtree {
    const int INNER_CARD = 32; // node size: 256B, the fanout of inner node is 32
    const int LEAF_CARD = 16;  // node size: 256B, the fanout of leaf node is 16
    const int LEAF_REBUILD_CARD = 8;
    const int MAX_HEIGHT = 10;

    // the entrance of fixtree that stores its persistent tree metadata
    struct entrance_t {
        void * leaf_buff;
        void * inner_buff;
        uint32_t height; // the tree height
        uint32_t leaf_cnt; 
    };

/*  Fixtree: 
        a search-optimized linearize tree structure which can absort moderate insertions: 
*/
class Fixtree {
    public:
        struct INNode { // inner node is packed keys, which is very compact
            _key_t keys[INNER_CARD];
        } __attribute__((aligned(CACHE_LINE_SIZE)));

        struct LFNode { // leaf node is packed key-ptr along with a header. 
                        // leaf node has some gap to absort insert
            _key_t keys[LEAF_CARD];
            char * vals[LEAF_CARD];
        } __attribute__((aligned(CACHE_LINE_SIZE)));

    public:
        // volatile structures
        INNode * inner_nodes_;
        LFNode * leaf_nodes_;
        uint32_t height_;
        uint32_t leaf_cnt_;
        entrance_t * entrance_;
        uint32_t level_offset_[MAX_HEIGHT];
    
    public:
        Fixtree(entrance_t * ent) { // recovery the tree from the entrance
            inner_nodes_ = (INNode *)galc->absolute(ent->inner_buff);
            leaf_nodes_ = (LFNode *)galc->absolute(ent->leaf_buff);
            height_ = ent->height;
            leaf_cnt_ = ent->leaf_cnt;
            entrance_ = ent;

            uint32_t tmp = 0;
            for(int l = 0; l < height_; l++) {
                level_offset_[l] = tmp;
                tmp += std::pow(INNER_CARD, l);
            }
            level_offset_[height_] = tmp;
        }

        // 这里要求传入的 record 有序
        Fixtree(std::vector<Record> records) {
            const int lfary = LEAF_REBUILD_CARD;
            int record_count = records.size();

            // 叶节点每个8条记录，计算总的叶节点数。
            uint32_t lfnode_cnt = std::ceil((float)record_count / lfary);
            // 为所有叶节点分配空间
            leaf_nodes_ = (LFNode *) galc->malloc(std::max((size_t)4096, lfnode_cnt * sizeof(LFNode)));

            // 树的高度（内部节点高度），O(log M为底N的对数)，即最大 logN/logM
            height_ = std::ceil(std::log(std::max((uint32_t)INNER_CARD, lfnode_cnt)) / std::log(INNER_CARD));
            // 内部节点的数量 1+M+M^2+...+M^(l-1) 求和为 (M^l-1)/(M-1)
            uint32_t innode_cnt = (std::pow(INNER_CARD, height_) - 1) / (INNER_CARD - 1);
            // 内部节点分配空间
            inner_nodes_ = (INNode *) galc->malloc(std::max((size_t)4096, innode_cnt * sizeof(INNode)));

            // fill leaf nodes
            // 外层循环遍历节点，内层遍历处理节点内部
            for(int i = 0; i < lfnode_cnt; i++) {
                for(int j = 0; j < lfary; j++) {
                    // 计算idx，填充叶节点的kv
                    auto idx = i * lfary + j;
                    leaf_nodes_[i].keys[j] = idx < record_count ? records[idx].key : MAX_KEY; 
                    leaf_nodes_[i].vals[j] = idx < record_count ? records[idx].val : 0;
                }
                // 新建树，每个节点只用一半（8个）位置，剩余一半初始化为MAX_KEY后面好判断
                for(int j = lfary; j < LEAF_CARD; j++) { // intialized key
                    leaf_nodes_[i].keys[j] = MAX_KEY;
                }
                // 单个节点处理完后持久化
                clwb(leaf_nodes_ + i, sizeof(LFNode));
            }
            
            int cur_level_cnt = lfnode_cnt;
            // 叶节点上一层父节点的起始offset，实际上=(M^(l-1)-1)/(M-1) = (M^l-1)/(M-1) - M^(l-1)
            int cur_level_off = innode_cnt - std::pow(INNER_CARD, height_ - 1);
            int last_level_off = 0;
            
            // fill parent innodes of leaf nodes
            for(int i = 0; i < cur_level_cnt; i++)
                // 第一个参数定位节点idx，第二个参数定位节点内部的offset，第三个参数即为内部节点存储的下一级节点的第一个key
                inner_insert(cur_level_off + i / INNER_CARD, i % INNER_CARD, leaf_nodes_[i].keys[0]);
            if(cur_level_cnt % INNER_CARD)
                // 如果最后一个节点没有用完，剩余部分初始化为 MAX_KEY 作为标识（只写一个就可以了，遇到MAX_KEY说明后面都无效）
                inner_insert(cur_level_off + cur_level_cnt / INNER_CARD, cur_level_cnt % INNER_CARD, MAX_KEY);
            // 持久化
            clwb(&inner_nodes_[cur_level_off], sizeof(INNode) * (cur_level_cnt / INNER_CARD + 1));

            // 内部节点都是满的，往上直接除 INNER_CARD 计算得到
            cur_level_cnt = std::ceil((float)cur_level_cnt / INNER_CARD);
            // 用于定位子节点，即上一波处理的节点，关联到当前节点
            last_level_off = cur_level_off;
            // 计算当前处理层的offset
            cur_level_off = cur_level_off - std::pow(INNER_CARD, height_ - 2);

            // fill other inner nodes
            // 每一层处理，向上遍历
            for(int l = height_ - 2; l >= 0; l--) { // level by level
                // 当前处理层内，遍历节点处理
                for(int i = 0; i < cur_level_cnt; i++)
                    inner_insert(cur_level_off + i / INNER_CARD, i % INNER_CARD, inner_nodes_[last_level_off + i].keys[0]);
                if(cur_level_cnt % INNER_CARD)
                    inner_insert(cur_level_off + cur_level_cnt / INNER_CARD, cur_level_cnt % INNER_CARD, MAX_KEY);
                clwb(&inner_nodes_[cur_level_off], sizeof(INNode) * (cur_level_cnt / INNER_CARD + 1));

                // 下一轮循环，元数据初始化
                cur_level_cnt = std::ceil((float)cur_level_cnt / INNER_CARD);
                last_level_off = cur_level_off;
                cur_level_off = cur_level_off - std::pow(INNER_CARD, l - 1);
            }
            
            leaf_cnt_ = lfnode_cnt;
            entrance_ = (entrance_t *)galc->malloc(4096); // the allocator is not thread_safe, allocate a large entrance
            uint32_t tmp = 0;
            for(int l = 0; l < height_; l++) {
                // 每一层节点的offset
                level_offset_[l] = tmp;
                tmp += std::pow(INNER_CARD, l);
            }
            level_offset_[height_] = tmp;

            // 持久化各个数据
            persist_assign(&(entrance_->leaf_buff), (void *) galc->relative(leaf_nodes_));
            persist_assign(&(entrance_->inner_buff), (void *) galc->relative(inner_nodes_));
            persist_assign(&(entrance_->height), height_);
            persist_assign(&(entrance_->leaf_cnt), lfnode_cnt);

            return ;
        }

    public:
    // 每一级向下找，到叶子节点后，从叶节点中查询对应key
        char ** find_lower(_key_t key) { 
            /* linear search, return the position of the stored value */
            // 内部节点中向下找key
            int cur_idx = level_offset_[0];
            for(int l = 0; l < height_; l++) {
                #ifdef DEBUG
                    INNode * inner = inner_nodes_ + cur_idx; 
                #endif
                // 当前层对应节点的idx = 当前层起始offset + 上一层对应节点前面的节点树*每个节点元素个数 + 上一层对应节点内部元素位置
                cur_idx = level_offset_[l + 1] + (cur_idx - level_offset_[l]) * INNER_CARD + inner_search(cur_idx, key);
            }
            // 叶子节点层单独的数组，是从0开始的。这里cur_idx前面计算时，加上了内部节点当前层的offset，所以要减去。
            cur_idx -= level_offset_[height_];

            // 叶子节点中搜索key
            return leaf_search(cur_idx, key);
        }

        // 插入kv元素，如果在key对应叶节点中成功插入（有空地），返回true，否则返回false，插入失败。
        bool insert(_key_t key, uint64_t val) {
            // 前面根据key找叶节点 和 find_lower 一样
            uint32_t cur_idx = level_offset_[0];
            for(int l = 0; l < height_; l++) {
                #ifdef DEBUG
                    INNode * inner = inner_nodes_ + cur_idx; 
                #endif
                cur_idx = level_offset_[l + 1] + (cur_idx - level_offset_[l]) * INNER_CARD + inner_search(cur_idx, key);
            }
            cur_idx -= level_offset_[height_];

            // 定位到叶节点
            LFNode * cur_leaf = leaf_nodes_ + cur_idx;

            // 遍历叶节点内部数组，如果找到key=MAX_KEY，则说明是空的slot，插入元素。
            for(int i = 0; i < LEAF_CARD; i++) {
                if (cur_leaf->keys[i] == MAX_KEY) { // empty slot
                    leaf_insert(cur_idx, i, {key, (char *)val});
                    return true;
                }
            }
            return false;
        }

        // key一定存在
        bool try_remove(_key_t key) {
            // 先根据key找对应叶节点，逻辑跟前面 find_lower 一样
            int cur_idx = level_offset_[0];
            for(int l = 0; l < height_; l++) {
                #ifdef DEBUG
                    INNode * inner = inner_nodes_ + cur_idx; 
                #endif
                cur_idx = level_offset_[l + 1] + (cur_idx - level_offset_[l]) * INNER_CARD + inner_search(cur_idx, key);
            }
            cur_idx -= level_offset_[height_];

            // 定位到叶节点
            LFNode * cur_leaf = leaf_nodes_ + cur_idx;

            // 遍历该叶节点，找到<=key的最大key。
            _key_t max_leqkey = cur_leaf->keys[0];
            int8_t max_leqi = 0;
            int8_t rec_cnt = 1;
            for(int i = 1; i < LEAF_CARD; i++) {
                if(cur_leaf->keys[i] != MAX_KEY) {
                    rec_cnt += 1;
                    if (cur_leaf->keys[i] <= key && cur_leaf->keys[i] > max_leqkey) {
                        max_leqkey = cur_leaf->keys[i];
                        max_leqi = i;
                    }
                }
            }

            /* There are three cases:
                  1. | k1 | --- | kx |, delete k1, leaf is not empty if k1 is deleted (fail)
                  2. | k1 | ---      |, delete k1, leaf is empty if k1 is deleted (success)
                  3. | k1 | --- | kx |, delete kx, leaf is not empty if kx is deleted (success)
            */
            if(max_leqi == 0 && rec_cnt > 1) { // case 1
                return false;
            } else { // case 2, 3
                // 删除key就是把指定位置设置为MAX_KEY标识
                persist_assign(&(cur_leaf->keys[max_leqi]), MAX_KEY);
                return true;
            }
        }

        void printAll() {
            for(int l = 0; l < height_; l++) {
                printf("level: %d =>", l);
                
                for(int i = level_offset_[l]; i < level_offset_[l + 1]; i++) {
                    inner_print(i);
                }
                printf("\n");
            }

            printf("leafs");

            for(int i = 0; i < leaf_cnt_; i++) {
                leaf_print(i);
            }
        }

        // 叶节点第一个节点
        char ** find_first() {
            return (char **)&(leaf_nodes_[0].vals[0]);
        }

        // 将两个树合并，in合并到out
        void merge(std::vector<Record> & in, std::vector<Record> & out) { // merge the records with in to out
            uint32_t insize = in.size();

            uint32_t incur = 0, innode_pos = 0, cur_lfcnt = 0;
            Record tmp[LEAF_CARD];
            load_node(tmp, &leaf_nodes_[0]);
            _key_t k1 = in[0].key, k2 = tmp[0].key;
            while(incur < insize && cur_lfcnt < leaf_cnt_) {
                if(k1 == k2) { 
                    out.push_back(in[incur]);

                    incur += 1;
                    innode_pos += 1;
                    if(innode_pos == LEAF_CARD || tmp[innode_pos].key == MAX_KEY) {
                        cur_lfcnt += 1;
                        load_node(tmp, &leaf_nodes_[cur_lfcnt]);
                        innode_pos = 0;
                    }

                    k1 = in[incur].key;
                    k2 = tmp[innode_pos].key;
                } else if(k1 > k2) {
                    out.push_back(tmp[innode_pos]);

                    innode_pos += 1;
                    if(innode_pos == LEAF_CARD || tmp[innode_pos].key == MAX_KEY) {
                        cur_lfcnt += 1;
                        load_node(tmp, &leaf_nodes_[cur_lfcnt]);
                        innode_pos = 0;
                    }

                    k2 = tmp[innode_pos].key;;
                } else {
                    out.push_back(in[incur]);
                    
                    incur += 1;
                    k1 = in[incur].key;
                }
            }

            if(incur < insize) {
                for(int i = incur; i < insize; i++) 
                    out.push_back(in[i]);
            }

            if(cur_lfcnt < leaf_cnt_) {
                while(cur_lfcnt < leaf_cnt_) {
                    out.push_back(tmp[innode_pos]);

                    innode_pos += 1;
                    if(innode_pos == LEAF_CARD || tmp[innode_pos].key == MAX_KEY) {
                        cur_lfcnt += 1;
                        load_node(tmp, &leaf_nodes_[cur_lfcnt]);
                        innode_pos = 0;
                    }
                }
            }
        }

    private:
    // 内部节点内搜索key，返回<=key中最大的哪个k索引
        int inner_search(int node_idx, _key_t key) const{
            // 定位到节点
            INNode * cur_inner = inner_nodes_ + node_idx;
            // 遍历节点数据
            for(int i = 0; i < INNER_CARD; i++) {
                if (cur_inner->keys[i] > key) {
                    return i - 1;
                }
            }

            return INNER_CARD - 1;
        }

        // 叶子节点中搜索key，返回<=key的最大元素。叶节点内部数据是没有排序的？
        char **leaf_search(int node_idx, _key_t key) const {
            // 定位到叶子节点
            LFNode * cur_leaf = leaf_nodes_ + node_idx;

            // 叶节点内部没有排序？所以遍历叶节点内部，找到<=key的最大元素
            _key_t max_leqkey = cur_leaf->keys[0];
            int8_t max_leqi = 0;
            for(int i = 1; i < LEAF_CARD; i++) {
                if (cur_leaf->keys[i] <= key && cur_leaf->keys[i] > max_leqkey) {
                    max_leqkey = cur_leaf->keys[i];
                    max_leqi = i;
                }
            }

            return (char **) &(cur_leaf->vals[max_leqi]);
        }

        // 叶节点对应位置写入kv记录
        bool leaf_insert(int node_idx, int off, Record rec) { // TODO: should do it in a CAS way
            leaf_nodes_[node_idx].vals[off] = rec.val;
            clwb(&leaf_nodes_[node_idx].vals[off], 8);
            mfence();

            leaf_nodes_[node_idx].keys[off] = rec.key;
            clwb(&leaf_nodes_[node_idx].keys[off], 8);
            mfence();
            return true;
        }

        // 指定节点，指定offset，写入元素
        inline void inner_insert(int node_idx, int off, _key_t key) {
            inner_nodes_[node_idx].keys[off] = key;
        }

        void inner_print(int node_idx) {
            printf("(");
            for(int i = 0; i < INNER_CARD; i++) {
                printf("%lu ", inner_nodes_[node_idx].keys[i]);
            }
            printf(") ");
        }

        void leaf_print(int node_idx) {
            printf("(");
            for(int i = 0; i < LEAF_CARD; i++) {
                printf("[%lu, %lu] ", leaf_nodes_[node_idx].keys[i], (long unsigned int)leaf_nodes_[node_idx].vals[i]);
            }
            printf(") \n");
        }

        static void load_node(Record * to, LFNode * from) {
            for(int i = 0; i < LEAF_CARD; i++) {
                to[i].key = from->keys[i];
                to[i].val = from->vals[i];
            }

            std::sort(to, to + LEAF_CARD);
        }
};

inline entrance_t * get_entrance(Fixtree * tree) {
    return tree->entrance_;
}

inline void free(Fixtree * tree) {
    entrance_t * upent = get_entrance(tree);
    delete tree;

    galc->free(galc->absolute(upent->inner_buff));
    galc->free(galc->absolute(upent->leaf_buff));
    galc->free(upent);

    return ;
}

typedef Fixtree uptree_t;

} // namespace fixtree

#endif //__FIXTREE__