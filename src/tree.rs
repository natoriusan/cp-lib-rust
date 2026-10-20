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
#[derive(Copy, Clone)]
struct RadixKey<'a> {
    bits: usize,
    len: u8, 
    rem: u8,
    rest: &'a [usize]
}

impl<'a> RadixKey<'a> {
    const fn empty() -> Self {
        Self {
            bits: 0,
            len: 0,
            rem: 0,
            rest: &[],
        }
    }

    #[inline(always)]
    const fn new(key: &'a [usize], len: usize) -> Self {
        debug_assert!(key.len() == len.div_ceil(64));
        let mut r = Self {
            bits: 0,
            len: 0,
            rem: (len as u8).wrapping_sub(1) % 64 + 1,
            rest: key,
        };
        r.advance(0);
        r
    }
    
    /// [start, end) bits
    const fn from_range(key: &'a [usize], start: usize, end: usize) -> Self {
        let (key, _) = key.split_at(end.div_ceil(64));
        let (_, key) = key.split_at(start/64);
        let mut r = Self::new(key, end-start/64*64);
        r.advance(start as u8%64);
        r
    }

    #[inline(always)]
    const fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline(always)]
    const fn dir(&self) -> usize {
        self.bits >> 63
    }

    #[inline(always)]
    const fn advance(&mut self, len: u8) {
        self.len -= len;
        if self.len > 0 {
            self.bits <<= len;
        } else if let Some((&bits, rest)) = self.rest.split_first() {
            self.bits = bits;
            self.rest = rest;
            self.len = if self.rest.is_empty() { self.rem } else { 64 };
        }
    }

    #[inline(always)]
    const fn is_one(&self, idx: u8) -> bool {
        (self.bits << idx) >> 63 == 1
    }
}

struct BinaryRadixTreeNode<M: ac_library::Monoid> {
    prefix: usize,
    len: u8,
    children: [u32; 2],
    value: M::S,
    aggregate: M::S
}

impl<M: ac_library::Monoid> BinaryRadixTreeNode<M> {
    #[inline(always)]
    fn lcp(&self, key: RadixKey) -> u8 {
        ((self.prefix ^ key.bits).leading_zeros() as u8).min(self.len).min(key.len)
    }

    #[inline(always)]
    fn is_prefix(&self, key: RadixKey) -> bool {
        ((self.prefix ^ key.bits).leading_zeros() as u8).min(key.len) >= self.len
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
    
    pub fn get(&self, key: &[usize], len: usize) -> M::S {
        let mut key = RadixKey::new(key, len);
        let mut node = &self.nodes[0];
        loop {
            if key.is_empty() { break node.value.clone(); }

            let child_idx = node.children[key.dir()] as usize;
            if let Some(child) = self.nodes.get(child_idx) && child.is_prefix(key) {
                key.advance(child.len);
                node = child;
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

    pub fn modify(&mut self, key: &[usize], len: usize, f: impl FnOnce(&M::S) -> M::S) {
        self.modify_rec(RadixKey::new(key, len), f, 0);
    }

    fn modify_rec(&mut self, mut key: RadixKey, f: impl FnOnce(&M::S) -> M::S, idx: usize) {
        let node = &mut self.nodes[idx];
        if key.is_empty() { 
            node.value = f(&node.value);
        } else {
            let dir = key.dir();
            let child_idx = node.children[dir] as usize;
            
            if child_idx == u32::MAX as usize {
                self.nodes[idx].children[dir] = self.len() as u32;
                self.nodes.push(BinaryRadixTreeNode {
                    prefix: key.bits,
                    len: key.len,
                    children: [u32::MAX; 2],
                    value: M::identity(),
                    aggregate: M::identity(),
                });
                key.advance(key.len);
                self.modify_rec(key, f, self.len()-1);
            } else {
                let child = &mut self.nodes[child_idx];
                let lcp = child.lcp(key);

                if lcp == child.len {
                    key.advance(lcp);
                    self.modify_rec(key, f, child_idx);
                } else {
                    child.prefix <<= lcp;
                    child.len -= lcp;
                    let child_dir = child.prefix >> 63;
                    self.nodes[idx].children[dir] = self.len() as u32;
                    self.nodes.push(BinaryRadixTreeNode {
                        prefix: key.bits,
                        len: lcp,
                        children: if child_dir == 1 { [u32::MAX, child_idx as u32] } else { [child_idx as u32, u32::MAX] },
                        value: M::identity(),
                        aggregate: M::identity(),
                    });
                    
                    key.advance(lcp);
                    self.modify_rec(key, f, self.len()-1);
                }
            }
        }
        
        self.update(idx);
    }

    pub fn set(&mut self, key: &[usize], len: usize, value: M::S) {
        self.modify(key, len, |_| value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<(&'a [usize], usize)>>(&self, range: R) -> M::S {
        self.prod_rec(range.start_bound().cloned().map(|(key, len)| RadixKey::new(key, len)), range.end_bound().cloned().map(|(key, len)| RadixKey::new(key, len)), 0)
    }

    fn prod_rec(&self, left: std::ops::Bound<RadixKey>, right: std::ops::Bound<RadixKey>, idx: usize) -> M::S {
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
                Included(mut key) | Excluded(mut key) => {
                    let lcp = child.lcp(key);
                    if lcp == child.len {
                        key.advance(lcp);
                        left.map(|_| key)
                    } else if lcp == key.len || !key.is_one(lcp) {
                        Unbounded
                    } else {
                        continue;
                    }
                }
                Unbounded => Unbounded
            };

            let new_right = match right {
                Included(mut key) | Excluded(mut key) => {
                    let lcp = child.lcp(key);
                    if lcp == child.len {
                        key.advance(lcp);
                        right.map(|_| key)
                    } else if lcp == key.len || !key.is_one(lcp) {
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

    pub fn prod_prefix(&self, key: &[usize], len: usize) -> M::S {
        let mut key = RadixKey::new(key, len);
        let mut node = &self.nodes[0];
        let mut acc = M::identity();
        loop {
            acc = M::binary_operation(&acc, &node.value);
            if key.is_empty() { break; }
            
            let child_idx = node.children[key.dir()] as usize;
            if let Some(child) = self.nodes.get(child_idx) && child.is_prefix(key) {
                key.advance(child.len);
                node = child;
            } else {
                break;
            }
        }
        
        acc
    }
    
    pub fn max_right(&self, left: (&[usize], usize), f: impl Fn(&M::S) -> bool) -> Option<(Vec<usize>, usize)> {
        assert!(f(&M::identity()));
        self.max_right_rec(RadixKey::new(left.0, left.1), &f, 0, &mut M::identity(), 0)
    }

    fn max_right_rec(&self, left: RadixKey, f: &impl Fn(&M::S) -> bool, idx: usize, acc: &mut M::S, depth: usize) -> Option<(Vec<usize>, usize)> {
        let node = &self.nodes[idx];
        if left.is_empty() {
            let new_acc = M::binary_operation(acc, &node.aggregate);
            if f(&new_acc) {
                *acc = new_acc;
                return None
            }

            let new_acc = M::binary_operation(acc, &node.value);
            if !f(&new_acc) {
                return Some((vec![0; depth.div_ceil(64)], depth));
            }
            *acc = new_acc;
        }

        for child_idx in node.children {
            let Some(child) = self.nodes.get(child_idx as usize) else { continue; };
            let lcp = child.lcp(left);
            let new_left =
                if lcp == child.len {
                    let mut new_left = left;
                    new_left.advance(lcp);
                    new_left
                } else if lcp == left.len || !left.is_one(lcp) {
                    RadixKey::empty()
                } else {
                    continue;
                };

            if let Some((mut v, len)) = self.max_right_rec(new_left, f, child_idx as usize, acc, depth+child.len as usize) {
                v[depth/64] |= (child.prefix >> (64-child.len)) << (64 - depth as u8 % 64 - child.len);
                return Some((v, len));
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
        self.tree.get(key, key.len()*64)
    }
    
    pub fn modify(&mut self, key: &[usize], f: impl FnOnce(&M::S) -> M::S) {
        self.tree.modify(key, key.len()*64, f);
    }

    pub fn set(&mut self, key: &[usize], value: M::S) {
        self.tree.set(key, key.len()*64, value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<&'a [usize]>>(&self, range: R) -> M::S {
        let start = range.start_bound().cloned().map(|key| (key, key.len()*64));
        let end = range.end_bound().cloned().map(|key| (key, key.len()*64));
        self.tree.prod((start, end))
    }
    
    pub fn prod_prefix(&self, key: &[usize]) -> M::S {
        self.tree.prod_prefix(key, key.len()*64)
    }

    pub fn max_right(&self, left: &[usize], f: impl Fn(&M::S) -> bool) -> Option<Vec<usize>> {
        self.tree.max_right((left, left.len()*64), f).map(|(key, _)| key)
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
    key: Vec<usize>,
    len: usize,
    extra_len: usize
}

impl<M: ac_library::Monoid, T: BinaryRadixTreeRef<M=M>> BinaryRadixTreeCursorBase<T> {
    pub fn key(&self) -> (&[usize], usize) {
        (&self.key, self.len)
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
        } else if self.extra_len < 64 {
            let key = RadixKey::from_range(&self.key, self.len-self.extra_len, self.len);
            let child_idx = tree.nodes[idx].children[key.dir()] as usize;
            if let Some(child) = tree.nodes.get(child_idx) && child.lcp(key) == key.len {
                child.aggregate.clone()
            } else {
                M::identity()
            }
        } else {
            M::identity()
        }
    }

    pub fn up(&mut self, mut bits: usize) {
        assert!(bits <= self.len);

        let min = bits.min(self.extra_len);
        bits -= min;
        self.len -= min;
        self.extra_len -= min;

        while bits != 0 {
            let node = &self.tree.tree().nodes[self.path.pop().unwrap() as usize];
            self.extra_len = node.len as usize;

            let min = bits.min(self.extra_len);
            bits -= min;
            self.len -= min;
            self.extra_len -= min;
            self.tree.update(*self.path.last().unwrap() as usize);
        }
        
        self.key.resize(self.len.div_ceil(64), 0);
        if let Some(last) = self.key.last_mut() {
            *last &= (!0usize).wrapping_shl((self.len as u32).wrapping_neg());
        }
    }
    
    fn update_path(&mut self) {
        let tree = self.tree.tree();
        let mut key = RadixKey::from_range(&self.key, self.len-self.extra_len, self.len);
        let mut idx = *self.path.last().unwrap() as usize;

        while !key.is_empty() {
            let child_idx = tree.nodes[idx].children[key.dir()];
            if let Some(child) = tree.nodes.get(child_idx as usize) && child.is_prefix(key) {
                self.path.push(child_idx);
                key.advance(child.len);
                idx = child_idx as usize;
                self.extra_len -= child.len as usize;
            } else {
                break;
            }
        }
    }

    pub fn down(&mut self, dir: bool) {
        if self.len.is_multiple_of(64) {
            self.key.push((dir as usize) << 63);
        } else {
            *self.key.last_mut().unwrap() |= (dir as usize).wrapping_shl(!self.len as u32);
        }
        self.len += 1;
        self.extra_len += 1;
        self.update_path()
    }
    
    /// 上位bitsビット
    pub fn down_bits(&mut self, key: usize, bits: usize) {
        if bits == 0 { return; }
        let key = key & (!0usize).wrapping_shl((bits as u32).wrapping_neg());
        if self.len.is_multiple_of(64) {
            self.key.push(key);
        } else {
            *self.key.last_mut().unwrap() |= key.wrapping_shr(self.len as u32);
            if self.len % 64 + bits > 64 {
                self.key.push(key.wrapping_shl((self.len as u32).wrapping_neg()));
            }
        }
        
        self.len += bits;
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
            self.up(self.len);
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
            let mut key = RadixKey::from_range(&self.key, self.len-self.extra_len, self.len);
            self.tree.modify_rec(key, f, *self.path.last().unwrap() as usize);
            let mut node = &self.tree.nodes[*self.path.last().unwrap() as usize];
            while !key.is_empty() {
                let child_idx = node.children[key.dir()];
                self.path.push(child_idx);
                node = &self.tree.nodes[child_idx as usize];
                key.advance(node.len);
            }
            self.extra_len = 0;
        } else {
            self.tree.modify_rec(RadixKey::empty(), f, *self.path.last().unwrap() as usize);
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
        &self.binary_cursor.key
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
            key: vec![],
            len: 0,
            extra_len: 0,
        }
    }
    
    pub fn cursor_mut(&mut self) -> BinaryRadixTreeCursorMut<'_, M> {
        BinaryRadixTreeCursorMut {
            tree: self,
            path: vec![0],
            key: vec![],
            len: 0,
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
        
        Self::max_right_y_rec(RadixKey::new(left, left.len()*64), &f, &trees, len, &mut M::identity(), 0)
    }

    fn max_right_y_rec(left: RadixKey, f: &impl Fn(&M::S) -> bool, trees: &[RadixState<M>; 64], count: usize, acc: &mut M::S, depth: usize) -> Option<Vec<usize>> {
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
                    return Some(vec![0; depth.div_ceil(64)]);
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
                    if (node.prefix << tree.skip) >> 63 != dir {
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
            
            let mut skip = u8::MAX;
            let tree0 = trees[0];
            let p = tree0.nodes[tree0.idx as usize].prefix << tree0.skip;
            for tree in &trees[..new_count] {
                let node = &tree.nodes[tree.idx as usize];
                skip = skip.min(
                    (((node.prefix << tree.skip) ^ p).leading_zeros() as u8).min(node.len-tree.skip)
                );
            }
            
            for tree in &mut trees[..new_count] {
                tree.skip += skip;
            }
            
            let new_left =
                if left.is_empty() {
                    RadixKey::empty()
                } else {
                    let lcp = ((p ^ left.bits).leading_zeros() as u8).min(skip).min(left.len);
                    if lcp == skip { 
                        let mut new_left = left ;
                        new_left.advance(skip);
                        new_left
                    } else if lcp == left.len || !left.is_one(lcp) {
                        RadixKey::empty()
                    } else {
                        continue;
                    }
                };
            
            if let Some(mut v) = Self::max_right_y_rec(new_left, f, &trees, new_count, acc, depth+skip as usize) {
                v[depth/64] |= (p >> (64-skip)) << (64 - depth as u8 % 64 - skip);
                return Some(v);
            }
        }
        
        None
    }
}
