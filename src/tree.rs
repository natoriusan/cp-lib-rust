// [0, 1<<size)のSegment Tree(1-indexedの内部実装)のiが寄与するセグメントのindex一覧 (set用)
// https://atcoder.jp/contests/abc339/submissions/71935783 (名前変更前)
pub fn included_segments_pow(size: usize, mut i: usize) -> Vec<usize> {
    i += 1 << size;
    let mut segments = vec![];
    while i > 0 {
        segments.push(i);
        i >>= 1;
    }

    segments
}

// [0, 1<<size)のSegment Tree(1-indexedの内部実装)の[l, r)のセグメントによる表現 (prod用)
// 可換専用
// https://atcoder.jp/contests/abc339/submissions/71935783 (名前変更前)
pub fn split_segments_pow(size: usize, mut l: usize, mut r: usize) -> Vec<usize> {
    l += 1 << size;
    r += 1 << size;
    let mut segments = vec![];
    while l > 0 && l != r {
        if l % 2 == 1 {
            segments.push(l);
            l = (l+1)>>1;
        } else {
            l >>= 1;
        }
        if (r-1) % 2 == 0 {
            segments.push(r-1);
        }
        r >>= 1;
    }

    segments
}

// included_segments_powの2冪でなくてもいいバージョン
pub fn included_segments(n: usize, i: usize) -> impl Iterator<Item=usize> {
    std::iter::successors(Some(n+i), |&j| (j >= 2).then_some(j>>1))
}

// split_segments_powの2冪でなくてもいいバージョン
pub fn split_segments(n: usize, mut l: usize, mut r: usize) -> impl Iterator<Item=usize> {
    l += n;
    r += n;
    let r_orig = r;
    let mut count = 0;
    let mut left = true;

    std::iter::from_fn(move || {
        if left {
            while l < r {
                count += 1;
                r >>= 1;
                if l % 2 == 1 {
                    let idx = l;
                    l += 1;
                    l >>= 1;
                    return Some(idx);
                }
                l >>= 1;
            }

            left = false;
        }

        while count > 0 {
            count -= 1;
            let r = r_orig >> count;
            if r % 2 == 1 {
                return Some(r-1);
            }
        }

        None
    })
}


// PersistentSegtree
// https://atcoder.jp/contests/abc453/submissions/74915650
#[derive(Clone, Debug)]
struct Node<T> {
    value: T,
    children: (usize, usize)
}

#[derive(Debug)]
pub struct PersistentSegtree<M: ac_library::Monoid> {
    nodes: std::rc::Rc<std::cell::RefCell<Vec<Node<M::S>>>>,
    root: usize,
    n: usize,
}

impl<M: ac_library::Monoid> Clone for PersistentSegtree<M> {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            root: self.root,
            n: self.n,
        }
    }
}

impl<M: ac_library::Monoid> PersistentSegtree<M> {
    pub fn new(n: usize) -> Self {
        fn make_tree<M: ac_library::Monoid>(nodes: &mut Vec<Node<M::S>>, l: usize, r: usize) -> usize {
            let mut node = Node {
                value: M::identity(),
                children: (usize::MAX, usize::MAX),
            };
            if l+1 < r {
                node.children = (
                    make_tree::<M>(nodes, l, (l+r)/2),
                    make_tree::<M>(nodes, (l+r)/2, r),
                );
            }

            nodes.push(node);
            nodes.len()-1
        }

        assert!(n > 0);
        let mut nodes = Vec::with_capacity(n*3);
        let root = make_tree::<M>(&mut nodes, 0, n);
        Self {
            nodes: std::rc::Rc::new(std::cell::RefCell::new(nodes)),
            root,
            n,
        }
    }

    pub fn get(&self, p: usize) -> M::S {
        fn get_tree<M: ac_library::Monoid>(nodes: &[Node<M::S>], p: usize, i: usize, l: usize, r: usize) -> M::S {
            let node = &nodes[i];
            if l+1 < r {
                if p < (l+r) / 2 {
                    get_tree::<M>(nodes, p, node.children.0, l, (l+r)/2)
                } else {
                    get_tree::<M>(nodes, p, node.children.1, (l+r)/2, r)
                }
            } else {
                node.value.clone()
            }
        }

        assert!(p < self.n);
        get_tree::<M>(&self.nodes.borrow(), p, self.root, 0, self.n)
    }

    #[must_use]
    pub fn set(&self, p: usize, x: M::S) -> Self {
        fn set_tree<M: ac_library::Monoid>(nodes: &mut Vec<Node<M::S>>, p: usize, x: M::S, i: usize, l: usize, r: usize) -> usize {
            let new_node =
                if l+1 < r {
                    let (left, right) = nodes[i].children;
                    let children =
                        if p < (l+r)/2 {
                            (set_tree::<M>(nodes, p, x, left, l, (l+r)/2), right)
                        } else {
                            (left, set_tree::<M>(nodes, p, x, right, (l+r)/2, r))
                        };
                    Node {
                        value: M::binary_operation(&nodes[children.0].value, &nodes[children.1].value),
                        children,
                    }
                } else {
                    Node {
                        value: x,
                        children: (usize::MAX, usize::MAX),
                    }
                };
            nodes.push(new_node);
            nodes.len()-1
        }

        assert!(p < self.n);
        Self {
            nodes: self.nodes.clone(),
            root: set_tree::<M>(&mut self.nodes.borrow_mut(), p, x, self.root, 0, self.n),
            n: self.n,
        }
    }

    pub fn prod<R: std::ops::RangeBounds<usize>>(&self, range: R) -> M::S {
        fn prod_tree<M: ac_library::Monoid>(nodes: &[Node<M::S>], lb: usize, rb: usize, i: usize, l: usize, r: usize) -> M::S {
            let node = &nodes[i];
            if lb <= l && r <= rb {
                node.value.clone()
            } else if rb <= l || r <= lb {
                M::identity()
            } else {
                let (left, right) = node.children;
                M::binary_operation(
                    &prod_tree::<M>(nodes, lb, rb, left, l, (l+r)/2),
                    &prod_tree::<M>(nodes, lb, rb, right, (l+r)/2, r),
                )
            }
        }

        use std::collections::Bound::*;
        let lb = match range.start_bound() {
            Included(&l) => l,
            Excluded(&l) => l+1,
            Unbounded => 0,
        };
        let rb = match range.end_bound() {
            Included(&r) => r+1,
            Excluded(&r) => r,
            Unbounded => self.n,
        };
        assert!(lb <= rb && rb <= self.n);

        if lb >= rb {
            M::identity()
        } else {
            prod_tree::<M>(&self.nodes.borrow(), lb, rb, self.root, 0, self.n)
        }
    }
}


// パス圧縮付きのBinaryTrie (https://atcoder.jp/contests/abc475/submissions/79302686)
type RadixKey = bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>;

struct BinaryRadixTreeNode<M: ac_library::Monoid> {
    prefix: u64,
    len: u8,
    children: [u32; 2],
    value: M::S,
    aggregate: M::S
}

impl<M: ac_library::Monoid> BinaryRadixTreeNode<M> {
    fn lcp(&self, key: &RadixKey) -> usize {
        use bitvec::field::BitField;
        let size = key.len().min(self.len as usize);
        if size == 0 { return 0; }
        let chunk = key[..size].load_be::<u64>() << (64-size);

        ((self.prefix ^ chunk).leading_zeros() as usize).min(size)
    }
    
    fn is_prefix(&self, key: &RadixKey) -> bool {
        use bitvec::field::BitField;
        if (self.len as usize) > key.len() { return false; }
        if self.len == 0 { return true; }
        self.prefix == key[..self.len as usize].load_be::<u64>() << (64-self.len)
    }
}

impl<M: ac_library::Monoid> Clone for BinaryRadixTreeNode<M> {
    fn clone(&self) -> Self {
        Self {
            prefix: self.prefix,
            len: self.len,
            children: self.children,
            value: self.value.clone(),
            aggregate: self.aggregate.clone(),
        }
    }
}

pub struct BinaryRadixTree<M: ac_library::Monoid> {
    nodes: Vec<BinaryRadixTreeNode<M>>
}

impl<M: ac_library::Monoid> BinaryRadixTree<M> {
    pub fn new() -> Self {
        Self {
            nodes: vec![
                BinaryRadixTreeNode {
                    prefix: 0,
                    len: 0,
                    children: [u32::MAX; 2],
                    value: M::identity(),
                    aggregate: M::identity(),
                }
            ]
        }
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn get(&self, mut key: &RadixKey) -> M::S {
        let mut idx = 0;
        loop {
            if key.is_empty() { break self.nodes[idx].value.clone(); }

            let child_idx = self.nodes[idx].children[key[0] as usize] as usize;
            if let Some(child) = self.nodes.get(child_idx) {
                if child.is_prefix(key) {
                    idx = child_idx;
                    key = &key[child.len as usize..];
                } else {
                    break M::identity();
                }

            } else {
                break M::identity();
            }
        }
    }
    
    fn update(&mut self, idx: usize) {
        let node = &self.nodes[idx];
        let mut agg = node.value.clone();
        for child_idx in node.children {
            if let Some(child) = self.nodes.get(child_idx as usize) {
                agg = M::binary_operation(&agg, &child.aggregate);
            }
        }
        
        self.nodes[idx].aggregate = agg;
    }

    pub fn modify(&mut self, key: &RadixKey, f: impl FnOnce(&M::S) -> M::S) {
        self.modify_rec(key, f, 0);
    }

    fn modify_rec(&mut self, key: &RadixKey, f: impl FnOnce(&M::S) -> M::S, idx: usize) {
        use bitvec::field::BitField;
        if key.is_empty() {
            self.nodes[idx].value = f(&self.nodes[idx].value);
        } else {
            let dir = key[0] as usize;
            let child_idx = self.nodes[idx].children[dir] as usize;
            
            if child_idx == u32::MAX as usize {
                let size = key.len().min(64);
                let chunk = key[..size].load_be::<u64>() << (64-size);
                self.nodes[idx].children[dir] = self.len() as u32;
                self.nodes.push(BinaryRadixTreeNode {
                    prefix: chunk,
                    len: size as u8,
                    children: [u32::MAX; 2],
                    value: M::identity(),
                    aggregate: M::identity(),
                });
                self.modify_rec(&key[size..], f, self.len()-1);
            } else {
                let child = &self.nodes[child_idx];
                let len = child.lcp(key);

                if len == child.len as usize {
                    self.modify_rec(&key[len..], f, child_idx);
                } else {
                    self.nodes[idx].children[dir] = self.len() as u32;
                    let child = &mut self.nodes[child_idx];
                    let new_prefix = child.prefix >> (64-len) << (64-len);
                    child.prefix <<= len;
                    child.len -= len as u8;
                    let prefix = child.prefix;
                    self.nodes.push(BinaryRadixTreeNode {
                        prefix: new_prefix,
                        len: len as u8,
                        children: if prefix >> 63 == 1 { [u32::MAX, child_idx as u32] } else { [child_idx as u32, u32::MAX] },
                        value: M::identity(),
                        aggregate: M::identity(),
                    });

                    self.modify_rec(&key[len..], f, self.len()-1);
                }
            }
        }
        
        self.update(idx);
    }

    pub fn set(&mut self, key: &RadixKey, value: M::S) {
        self.modify(key, |_| value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<&'a RadixKey>>(&self, range: R) -> M::S {
        self.prod_rec(range.start_bound().cloned(), range.end_bound().cloned(), 0)
    }

    fn prod_rec(&self, left: std::ops::Bound<&RadixKey>, right: std::ops::Bound<&RadixKey>, idx: usize) -> M::S {
        use std::ops::Bound::*;

        if let Excluded(key) = right && key.is_empty() {
            return M::identity();
        }
        
        let left_unbounded = match left {
            Included(key) => key.is_empty(),
            Excluded(_) => false,
            Unbounded => true,
        };
        
        if let Unbounded = right && left_unbounded {
            return self.nodes[idx].aggregate.clone();
        }

        let mut r =
            if left_unbounded {
                self.nodes[idx].value.clone()
            } else {
                M::identity()
            };
        
        for child_idx in self.nodes[idx].children {
            let Some(child) = self.nodes.get(child_idx as usize) else { continue; };
            
            let new_left = match left {
                Included(key) | Excluded(key) => {
                    let lcp = child.lcp(key);
                    if child.len as usize == lcp {
                        left.map(|_| &key[child.len as usize..])
                    } else if lcp == key.len() || !key[lcp] {
                        Unbounded
                    } else {
                        continue;
                    }
                }
                Unbounded => Unbounded
            };

            let new_right = match right {
                Included(key) | Excluded(key) => {
                    let lcp = child.lcp(key);
                    if child.len as usize == lcp {
                        right.map(|_| &key[child.len as usize..])
                    } else if lcp == key.len() || !key[lcp] {
                        continue;
                    } else {
                        Unbounded
                    }
                }
                Unbounded => Unbounded
            };
            

            r = M::binary_operation(&r, &self.prod_rec(new_left, new_right, child_idx as usize));
        }

        r
    }

    pub fn prod_prefix(&self, mut key: &RadixKey) -> M::S {
        let mut idx = 0;
        let mut acc = M::identity();
        loop {
            acc = M::binary_operation(&acc, &self.nodes[idx].value);
            if key.is_empty() { break; }
            
            let child_idx = self.nodes[idx].children[key[0] as usize] as usize;
            if let Some(child) = self.nodes.get(child_idx) && child.is_prefix(key) {
                idx = child_idx;
                key = &key[child.len as usize..];
            } else {
                break;
            }
        }
        
        acc
    }
    
    pub fn max_right(&self, left: &RadixKey, f: impl Fn(&M::S) -> bool) -> Option<bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>> {
        assert!(f(&M::identity()));
        self.max_right_rec(left, &f, 0, &mut M::identity(), 0)
    }

    fn max_right_rec(&self, left: &RadixKey, f: &impl Fn(&M::S) -> bool, idx: usize, acc: &mut M::S, depth: usize) -> Option<bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>> {
        use bitvec::field::BitField;
        use bitvec::prelude::{BitVec, BitSlice};
        let node = &self.nodes[idx];
        if left.is_empty() {
            let new_acc = M::binary_operation(acc, &node.aggregate);
            if f(&new_acc) {
                *acc = new_acc;
                return None
            }

            let new_acc = M::binary_operation(acc, &node.value);
            if !f(&new_acc) {
                let mut v = BitVec::repeat(false, depth);
                if node.len > 0 {
                    v[depth-node.len as usize..depth].store_be(node.prefix >> (64-node.len));
                }
                return Some(v);
            }
            *acc = new_acc;
        }

        for child_idx in node.children {
            let Some(child) = self.nodes.get(child_idx as usize) else { continue; };
            let lcp = child.lcp(left);
            let new_left =
                if child.len as usize == lcp {
                    &left[lcp..]
                } else if lcp == left.len() || !left[lcp] {
                    BitSlice::empty()
                } else {
                    continue;
                };

            if let Some(mut v) = self.max_right_rec(new_left, f, child_idx as usize, acc, depth+child.len as usize) {
                if node.len > 0 {
                    v[depth-node.len as usize..depth].store_be(node.prefix >> (64-node.len));
                }
                return Some(v);
            }
        }

        None
    }
}

impl<M: ac_library::Monoid> Default for BinaryRadixTree<M> {
    fn default() -> Self {
        Self::new()
    }
}

impl<M: ac_library::Monoid> Clone for BinaryRadixTree<M> {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
        }
    }
}


// 動的セグ木のような使い方: https://atcoder.jp/contests/abc403/submissions/79303011
pub struct RadixTree<M: ac_library::Monoid> {
    tree: BinaryRadixTree<M>,
}

impl<M: ac_library::Monoid> RadixTree<M> {
    pub fn new() -> Self {
        Self {
            tree: BinaryRadixTree::new(),
        }
    }
    
    pub fn get(&self, key: &[usize]) -> M::S {
        self.tree.get(bitvec::prelude::BitSlice::from_slice(key))
    }
    
    pub fn modify(&mut self, key: &[usize], f: impl FnOnce(&M::S) -> M::S) {
        self.tree.modify(bitvec::prelude::BitSlice::from_slice(key), f);
    }

    pub fn set(&mut self, key: &[usize], value: M::S) {
        self.tree.set(bitvec::prelude::BitSlice::from_slice(key), value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<&'a [usize]>>(&self, range: R) -> M::S {
        use bitvec::prelude::BitSlice;
        let start = range.start_bound().cloned().map(BitSlice::from_slice);
        let end = range.end_bound().cloned().map(BitSlice::from_slice);
        self.tree.prod((start, end))
    }
    
    pub fn prod_prefix(&self, key: &[usize]) -> M::S {
        self.tree.prod_prefix(bitvec::prelude::BitSlice::from_slice(key))
    }

    pub fn max_right(&self, left: &[usize], f: impl Fn(&M::S) -> bool) -> Option<Vec<usize>> {
        self.tree.max_right(bitvec::prelude::BitSlice::from_slice(left), f).map(|v| v.into_vec())
    }
}

impl<M: ac_library::Monoid> Default for RadixTree<M> {
    fn default() -> Self {
        Self {
            tree: Default::default(),
        }
    }
}

impl<M: ac_library::Monoid> Clone for RadixTree<M> {
    fn clone(&self) -> Self {
        Self {
            tree: self.tree.clone()
        }
    }
}

pub trait BinaryRadixTreeRef {
    type M: ac_library::Monoid;
    const IS_MUT: bool;
    fn tree(&self) -> &BinaryRadixTree<Self::M>;
    fn update(&mut self, _idx: usize) {}
}

#[derive(Clone)]
pub struct BinaryRadixTreeCursorBase<T: BinaryRadixTreeRef> {
    tree: T,
    path: Vec<u32>,
    key: bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>,
    extra_len: usize
}

impl<M: ac_library::Monoid, T: BinaryRadixTreeRef<M=M>> BinaryRadixTreeCursorBase<T> {
    pub fn key(&self) -> &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0> {
        &self.key
    }

    pub fn value(&self) -> M::S {
        if self.extra_len == 0 {
            self.tree.tree().nodes[*self.path.last().unwrap() as usize].value.clone()
        } else {
            M::identity()
        }
    }

    pub fn aggregate(&self) -> M::S {
        let tree = self.tree.tree();
        let idx = *self.path.last().unwrap() as usize;
        if self.extra_len == 0 {
            tree.nodes[idx].aggregate.clone()
        } else {
            let key = &self.key[self.key.len()-self.extra_len..];
            let child_idx = tree.nodes[idx].children[key[0] as usize] as usize;
            if let Some(child) = tree.nodes.get(child_idx) && child.lcp(key) == key.len() {
                child.aggregate.clone()
            } else {
                M::identity()
            }
        }
    }

    pub fn up(&mut self, mut bits: usize) {
        assert!(bits <= self.key.len());
        self.key.resize(self.key.len()-bits, false);

        let min = bits.min(self.extra_len);
        bits -= min;
        self.extra_len -= min;

        while bits != 0 {
            let node = &self.tree.tree().nodes[self.path.pop().unwrap() as usize];
            self.extra_len = node.len as usize;

            let min = bits.min(self.extra_len);
            bits -= min;
            self.extra_len -= min;
            self.tree.update(*self.path.last().unwrap() as usize);
        }
    }
    
    fn update_path(&mut self) {
        let tree = self.tree.tree();
        let mut key = &self.key[self.key.len()-self.extra_len..];
        let mut idx = *self.path.last().unwrap() as usize;

        while !key.is_empty() {
            let child_idx = tree.nodes[idx].children[key[0] as usize];
            if let Some(child) = tree.nodes.get(child_idx as usize) && child.is_prefix(key) {
                self.path.push(child_idx);
                key = &key[child.len as usize..];
                idx = child_idx as usize;
                self.extra_len -= child.len as usize;
            } else {
                break;
            }
        }
    }

    pub fn down(&mut self, dir: bool) {
        self.key.push(dir);
        self.extra_len += 1;
        self.update_path()
    }
    
    /// 下位bitsビット
    pub fn down_bits(&mut self, key: usize, bits: usize) {
        use bitvec::field::BitField;
        if bits == 0 { return; }
        let len = self.key.len();
        self.key.resize(len+bits, false);
        self.key[len..].store_be(key);
        self.extra_len += bits;
        self.update_path();
    }

    fn down_usize(&mut self, key: usize) {
        self.down_bits(key, 64);
    }
}

impl<M: ac_library::Monoid, T: BinaryRadixTreeRef<M=M>> Drop for BinaryRadixTreeCursorBase<T> {
    fn drop(&mut self) {
        if T::IS_MUT {
            self.up(self.key.len());
        }
    }
}

impl<M: ac_library::Monoid> BinaryRadixTreeRef for &mut BinaryRadixTree<M> {
    type M = M;
    const IS_MUT: bool = true;

    fn tree(&self) -> &BinaryRadixTree<M> {
        self
    }

    fn update(&mut self, idx: usize) {
        (*self).update(idx);
    }
}

impl<M: ac_library::Monoid> BinaryRadixTreeRef for &BinaryRadixTree<M> {
    type M = M;
    const IS_MUT: bool = false;

    fn tree(&self) -> &BinaryRadixTree<M> {
        self
    }
}

pub type BinaryRadixTreeCursor<'a, M> = BinaryRadixTreeCursorBase<&'a BinaryRadixTree<M>>;

pub type BinaryRadixTreeCursorMut<'a, M> = BinaryRadixTreeCursorBase<&'a mut BinaryRadixTree<M>>;

impl<'a, M: ac_library::Monoid> BinaryRadixTreeCursorMut<'a, M> {
    pub fn modify(&mut self, f: impl FnOnce(&M::S) -> M::S) {
        if self.extra_len != 0 {
            let mut key = &self.key[self.key.len()-self.extra_len..];
            self.tree.modify_rec(key, f, *self.path.last().unwrap() as usize);
            let mut node = &self.tree.nodes[*self.path.last().unwrap() as usize];
            while !key.is_empty() {
                let child_idx = node.children[key[0] as usize];
                self.path.push(child_idx);
                node = &self.tree.nodes[child_idx as usize];
                key = &key[node.len as usize..];
            }
            self.extra_len = 0;
        } else {
            self.tree.modify_rec(bitvec::prelude::BitSlice::empty(), f, *self.path.last().unwrap() as usize);
        }
    }

    pub fn set(&mut self, value: M::S) {
        self.modify(|_| value);
    }
}

#[derive(Clone)]
pub struct RadixTreeCursorBase<T: BinaryRadixTreeRef> {
    binary_cursor: BinaryRadixTreeCursorBase<T>,
}

pub type RadixTreeCursor<'a, M> = RadixTreeCursorBase<&'a BinaryRadixTree<M>>;

// https://atcoder.jp/contests/abc353/submissions/79323824
pub type RadixTreeCursorMut<'a, M> = RadixTreeCursorBase<&'a mut BinaryRadixTree<M>>;


impl<M: ac_library::Monoid, T: BinaryRadixTreeRef<M=M>> RadixTreeCursorBase<T>  {
    pub fn key(&self) -> &[usize] {
        self.binary_cursor.key.as_raw_slice()
    }

    pub fn value(&self) -> M::S {
        self.binary_cursor.value()
    }

    pub fn aggregate(&self) -> M::S {
        self.binary_cursor.aggregate()
    }

    pub fn up(&mut self, words: usize) {
        self.binary_cursor.up(words*64);
    }

    pub fn down(&mut self, dir: usize) {
        self.binary_cursor.down_usize(dir);
    }
}

impl<'a, M: ac_library::Monoid> RadixTreeCursorMut<'a, M> {
    pub fn modify(&mut self, f: impl FnOnce(&M::S) -> M::S) {
        self.binary_cursor.modify(f);
    }
    
    pub fn set(&mut self, value: M::S) {
        self.binary_cursor.set(value);
    }
}


impl<M: ac_library::Monoid> BinaryRadixTree<M> {
    pub fn cursor(&self) -> BinaryRadixTreeCursor<'_, M> {
        BinaryRadixTreeCursor {
            tree: self,
            path: vec![0],
            key: bitvec::prelude::BitVec::new(),
            extra_len: 0,
        }
    }
    
    pub fn cursor_mut(&mut self) -> BinaryRadixTreeCursorMut<'_, M> {
        BinaryRadixTreeCursorMut {
            tree: self,
            path: vec![0],
            key: bitvec::prelude::BitVec::new(),
            extra_len: 0,
        }
    }
}

impl<M: ac_library::Monoid> RadixTree<M> {
    pub fn cursor(&self) -> RadixTreeCursor<'_, M> {
        RadixTreeCursor {
            binary_cursor: self.tree.cursor()
        }
    }
    
    pub fn cursor_mut(&mut self) -> RadixTreeCursorMut<'_, M> {
        RadixTreeCursorMut {
            binary_cursor: self.tree.cursor_mut(),
        }
    }
}


struct RadixState<'a, M: ac_library::Monoid> {
    nodes: &'a [BinaryRadixTreeNode<M>],
    idx: u32,
    skip: u8,
}

impl<'a, M: ac_library::Monoid> Clone for RadixState<'a, M> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, M: ac_library::Monoid> Copy for RadixState<'a, M> {
    
}

pub struct SegRadixTree<M: ac_library::Monoid> {
    trees: Vec<RadixTree<M>>
}

impl<M: ac_library::Monoid> SegRadixTree<M> {
    pub fn new(x_len: usize) -> Self {
        Self {
            trees: vec![RadixTree::new(); 2*x_len],
        }
    }

    fn len(&self) -> usize {
        self.trees.len() / 2
    }

    pub fn get(&self, x: usize, y: &[usize]) -> M::S {
        self.trees[self.len()+x].get(y)
    }

    pub fn modify(&mut self, x: usize, y: &[usize], f: impl FnOnce(&M::S) -> M::S) {
        let mut idx = self.len()+x;
        let mut val = None;
        self.trees[idx].modify(y, |v| {
            val = Some(f(v));
            val.clone().unwrap()
        });
        let mut val = val.unwrap();
        
        while idx > 1 {
            val =
                if idx.is_multiple_of(2) {
                    M::binary_operation(&val, &self.trees[idx+1].get(y))
                } else {
                    M::binary_operation(&self.trees[idx-1].get(y), &val)
                };
            
            idx /= 2;
            self.trees[idx].set(y, val.clone());
        }
    }

    pub fn set(&mut self, x: usize, y: &[usize], value: M::S) {
        self.modify(x, y, |_| value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<&'a [usize]>>(&self, x_range: impl std::ops::RangeBounds<usize>, y_range: R) -> M::S {
        use std::collections::Bound::*;
        let xl = match x_range.start_bound() {
            Included(&xl) => xl,
            Excluded(&xl) => xl+1,
            Unbounded => 0,
        };
        let xr = match x_range.end_bound() {
            Included(&xr) => xr+1,
            Excluded(&xr) => xr,
            Unbounded => self.len(),
        };
        assert!(xl <= xr && xr <= self.len());

        let mut r = M::identity();
        for i in split_segments(self.len(), xl, xr) {
            r = M::binary_operation(&r, &self.trees[i].prod((y_range.start_bound(), y_range.end_bound())))
        }

        r
    }

    pub fn max_right_y(&self, x_range: impl std::ops::RangeBounds<usize>, left: &[usize], f: impl Fn(&M::S) -> bool) -> Option<Vec<usize>> {
        use std::ops::Bound::*;
        assert!(f(&M::identity()));
        let xl = match x_range.start_bound() {
            Included(&xl) => xl,
            Excluded(&xl) => xl+1,
            Unbounded => 0,
        };
        let xr = match x_range.end_bound() {
            Included(&xr) => xr+1,
            Excluded(&xr) => xr,
            Unbounded => self.len(),
        };
        assert!(xl <= xr && xr <= self.len());
        
        let mut trees = [RadixState { nodes: &[], idx: 0, skip: 0, }; 64];
        let mut len = 0;
        for (i, si) in split_segments(self.len(), xl, xr).enumerate() {
            len = i+1;
            trees[i] = RadixState {
                nodes: &self.trees[si].tree.nodes,
                idx: 0,
                skip: 0,
            }
        }
        
        Self::max_right_y_rec(bitvec::prelude::BitSlice::from_slice(left), &f, &trees, len, &mut M::identity(), 0, 0, 0).map(|v| v.into_vec())
    }

    fn max_right_y_rec(left: &RadixKey, f: &impl Fn(&M::S) -> bool, trees: &[RadixState<M>; 64], count: usize, acc: &mut M::S, prefix: u64, len: usize, depth: usize) -> Option<bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>> {
        use bitvec::field::BitField;
        use bitvec::prelude::{BitVec, BitSlice};
        if count == 0 { return None; }
        
        if left.is_empty() {
            let mut aggregates = trees[..count].iter().map(|tree| &tree.nodes[tree.idx as usize].aggregate);
            let prod = M::binary_operation(acc, aggregates.next().unwrap());
            let new_acc = aggregates.fold(prod, |prod, agg| M::binary_operation(&prod, agg));
            if f(&new_acc) {
                *acc = new_acc;
                return None;
            }

            let mut values = trees[..count].iter().filter(|tree| tree.skip == tree.nodes[tree.idx as usize].len).map(|tree| &tree.nodes[tree.idx as usize].value);
            if let Some(head) = values.next() {
                let prod = M::binary_operation(acc, head);
                let new_acc = values.fold(prod, |prod, val| M::binary_operation(&prod, val));
                if !f(&new_acc) {
                    let mut v = BitVec::repeat(false, depth);
                    if len > 0 {
                        v[depth-len..depth].store_be(prefix >> (64-len));
                    }
                    return Some(v);
                }
                *acc = new_acc;
            }
        }
        
        for dir in 0..2 {
            let mut trees = *trees;
            let mut new_count = count;
            for i in (0..count).rev() {
                let tree = &trees[i];
                let node = &tree.nodes[tree.idx as usize];
                if tree.skip < node.len {
                    if (node.prefix >> (63-tree.skip)) & 1 != dir as u64 {
                        new_count -= 1;
                        trees.swap(i, new_count);
                    }
                } else {
                    let child_idx = node.children[dir];
                    if child_idx < u32::MAX {
                        trees[i].idx = child_idx;
                        trees[i].skip = 0;
                    } else {
                        new_count -= 1;
                        trees.swap(i, new_count);
                        
                    }
                }
            }
            
            if new_count == 0 { continue; }
            
            let mut skip = u32::MAX;
            let tree0 = trees[0];
            let p = tree0.nodes[tree0.idx as usize].prefix << tree0.skip;
            for tree in &trees[..new_count] {
                let node = &tree.nodes[tree.idx as usize];
                skip = skip.min(
                    ((node.prefix << tree.skip) ^ p).leading_zeros().min((node.len-tree.skip) as u32)
                );
            }
            
            for tree in &mut trees[..new_count] {
                tree.skip += skip as u8;
            }
            
            let next_left =
                if left.is_empty() {
                    BitSlice::empty()
                } else {
                    let size = left.len().min(skip as usize);
                    let lcp = ((p ^ (left[..size].load_be::<u64>() << (64-size))).leading_zeros() as usize).min(size);
                    if lcp == skip as usize {
                        &left[skip as usize..]
                    } else if lcp == left.len() || !left[lcp] {
                        BitSlice::empty()
                    } else {
                        continue;
                    }
                };
            
            if let Some(mut v) = Self::max_right_y_rec(next_left, f, &trees, new_count, acc, p, skip as usize, depth+skip as usize) {
                if len > 0 {
                    v[depth-len..depth].store_be(prefix >> (64-len));
                }
                return Some(v);
            }
        }
        
        None
    }
}
