#include "wotree256.h"

namespace wotree256 {

bool insert_recursive(Node * n, _key_t k, uint64_t v, _key_t &split_k, Node * &split_node, int8_t &level) {
    if(n->leftmost_ptr_ == NULL) {
        // leftmost_ptr_ 为空，表示叶子节点，直接调用底层node的store函数写入
        return n->store(k, v, split_k, split_node);
    } else {
        // 不为空，当前节点有子节点，往子节点找
        level++;
        // 获取子节点
        Node * child = (Node *) galc->absolute(n->get_child(k));
        
        _key_t split_k_child;
        Node * split_node_child;
        // 递归调用往子节点插入
        bool splitIf = insert_recursive(child, k, v, split_k_child, split_node_child, level);

        if(splitIf) {
            // 每一级的子节点如果发生了split，则需要将分裂的节点记录关联存储到当前节点
            return n->store(split_k_child, (uint64_t)galc->relative(split_node_child), split_k, split_node);
        } 
        return false;
    }
}

// 递归删除节点，返回是否需要合并
bool remove_recursive(Node * n, _key_t k) {
    if(n->leftmost_ptr_ == NULL) {
        // 叶子节点，直接调用remove方法
        n->remove(k);
        // 删除后，如果节点数小于4个，则寻求合并
        return n->state_.unpack.count < UNDERFLOW_CARD;
    }
    else {
        // 非叶子节点，根据k查询对应子节点
        Node * child = (Node *) galc->absolute(n->get_child(k));

        // 递归调用 remove_recursive
        bool shouldMrg = remove_recursive(child, k);

        if(shouldMrg) {
            // 如果能合并，则获取该子节点左边和右边的子节点
            Node *leftsib = NULL, *rightsib = NULL;
            n->get_lrchild(k, leftsib, rightsib);

            if(leftsib != NULL && (child->state_.unpack.count + leftsib->state_.unpack.count) < CARDINALITY) {
                // 如果 child 节点能跟左边节点合并，则处理合并
                // merge with left node
                // 从当前节点中删除右边那个子树关联的key，然后将右边那个子树合并到左边子树中
                int8_t slotid = child->state_.read(0);
                n->remove(child->recs_[slotid].key);
                Node::merge(leftsib, child);

                return n->state_.unpack.count < UNDERFLOW_CARD;
            } else if (rightsib != NULL && (child->state_.unpack.count + rightsib->state_.unpack.count) < CARDINALITY) {
                // 如果 child 节点能跟右边节点合并，则处理合并
                // merge with right node
                int8_t slotid = rightsib->state_.read(0);
                n->remove(rightsib->recs_[slotid].key);
                Node::merge(child, rightsib);

                return n->state_.unpack.count < UNDERFLOW_CARD;
            }
        }
        return false;
    }
}

bool find(Node ** rootPtr, _key_t key, uint64_t &val) {
    Node * cur = galc->absolute(*rootPtr);
    while(cur->leftmost_ptr_ != NULL) { // no prefetch here
        // 非空，则根据key找对应子节点，直到子节点为叶子节点
        char * child_ptr = cur->get_child(key);
        cur = (Node *)galc->absolute(child_ptr);
    }

    // 叶子节点调用 get_child 拿到的就是对应值的指针
    val = (uint64_t) cur->get_child(key);

    // val为空则没找到对应值
    if((char *)val == NULL)
        return false;
    else
        return true;
}

res_t insert(Node ** rootPtr, _key_t key, uint64_t val, int threshold) {
    Node *root_= galc->absolute(*rootPtr);
    
    int8_t level = 1;
    _key_t split_k;
    Node * split_node;
    // 根节点递归插入
    bool splitIf = insert_recursive(root_, key, val, split_k, split_node, level);

    if(splitIf) {
        // 根节点发生了分裂
        if(level < threshold) {
            // 树的高度没超过阈值，直接构造新的根节点，原root_作为左子数，新节点作为右子树。
            Node *new_root = new Node;
            new_root->leftmost_ptr_ = (char *)galc->relative(root_);
            new_root->append({split_k, (char *)galc->relative(split_node)}, 0, 0);
            new_root->state_.unpack.count = 1;

            clwb(new_root, 64);

            mfence(); // a barrier to make sure the new node is persisted
            // 新的根节点指针赋值给rootPtr
            persist_assign(rootPtr, (Node *)galc->relative(new_root));

            return res_t(false, {0, NULL});
        } else {
            return res_t(true, {split_k, (char *)split_node});
        }   
    }
    else {
        return res_t(false, {0, NULL});
    }
}

bool update(Node ** rootPtr, _key_t key, uint64_t val) {
    Node * cur = galc->absolute(*rootPtr);
    // 如果非叶子节点则循环向下找
    while(cur->leftmost_ptr_ != NULL) { // no prefetch here
        char * child_ptr = cur->get_child(key);
        cur = (Node *)galc->absolute(child_ptr);
    }

    // 叶子节点调用更新操作
    val = (uint64_t) cur->update(key, val);
    return true;
}

bool remove(Node ** rootPtr, _key_t key) {   
    Node *root_= galc->absolute(*rootPtr);
    if(root_->leftmost_ptr_ == NULL) {
        // 为空叶节点，直接调用节点的remove方法
        root_->remove(key);

        return root_->state_.unpack.count == 0;
    }
    else {
        // 非叶节点，有子节点，则先用key查询对应子节点
        Node * child = (Node *) galc->absolute(root_->get_child(key));

        // 子节点中递归删除
        bool shouldMrg = remove_recursive(child, key);

        if(shouldMrg) {
            Node *leftsib = NULL, *rightsib = NULL;
            root_->get_lrchild(key, leftsib, rightsib);

            if(leftsib != NULL && (child->state_.unpack.count + leftsib->state_.unpack.count) < CARDINALITY) {
                // merge with left node
                int8_t slotid = child->state_.read(0);
                // root子树有合并，这里root中删除右边对应的key，并进行子树合并
                root_->remove(child->recs_[slotid].key);
                Node::merge(leftsib, child);
            } 
            else if (rightsib != NULL && (child->state_.unpack.count + rightsib->state_.unpack.count) < CARDINALITY) {
                // merge with right node
                int8_t slotid = rightsib->state_.read(0);
                root_->remove(rightsib->recs_[slotid].key);
                Node::merge(child, rightsib);
            }

            // 最终如果 root 中没有元素了，说明后面的节点删完了，新root指向原来的 leftmost_ptr_
            if(root_->state_.unpack.count == 0) { // the root is empty
                Node * old_root = root_;

                persist_assign(rootPtr, (Node *)root_->leftmost_ptr_);

                galc->free(old_root);
            }
        }

        return false;
    } 
}

void printAll(Node ** rootPtr) {
    Node *root= galc->absolute(*rootPtr);
    root->print("", true);
}

} // namespace wotree256