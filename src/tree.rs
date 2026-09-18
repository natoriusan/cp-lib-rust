// パス圧縮付きのBinaryTrie (https://atcoder.jp/contests/abc475/submissions/79302686)
#[derive(Clone)]
struct BinaryRadixTreeNode<M: ac_library::Monoid> {
    prefix: u64,
    len: u8,
    children: [u32; 2],
    value: M::S,
    aggregate: M::S
}

#[derive(Clone)]
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

    pub fn get(&self, mut key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>) -> M::S {
        use bitvec::field::BitField;
        let mut idx = 0;
        loop {
            if key.is_empty() { break self.nodes[idx].value.clone(); }

            let child_idx = self.nodes[idx].children[key[0] as usize] as usize;
            if let Some(child) = self.nodes.get(child_idx) {
                if key.len() < child.len as usize || key[..child.len as usize].load_be::<u64>() << (64-child.len) != child.prefix {
                    break M::identity();
                }

                idx = child_idx;
                key = &key[child.len as usize..];
            } else {
                break M::identity();
            }
        }
    }
    
    pub fn update(&mut self, idx: usize) {
        let mut agg = M::identity();
        for i in self.nodes[idx].children {
            if let Some(c) = self.nodes.get(i as usize) {
                agg = M::binary_operation(&agg, &c.aggregate);
            }
        }
        let node = &mut self.nodes[idx];
        node.aggregate = M::binary_operation(&node.value, &agg);
    }

    pub fn modify(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, f: impl FnOnce(&M::S) -> M::S) {
        self.modify_rec(key, f, 0);
    }

    fn modify_rec(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, f: impl FnOnce(&M::S) -> M::S, idx: usize) {
        use bitvec::field::BitField;
        if key.is_empty() {
            self.nodes[idx].value = f(&self.nodes[idx].value);
        } else {
            let size = key.len().min(64);
            let chunk = key[..size].load_be::<u64>() << (64-size);

            if self.nodes[idx].children[key[0] as usize] == u32::MAX {
                self.nodes[idx].children[key[0] as usize] = self.len() as u32;
                self.nodes.push(BinaryRadixTreeNode {
                    prefix: chunk,
                    len: size as u8,
                    children: [u32::MAX; 2],
                    value: M::identity(),
                    aggregate: M::identity(),
                });
            }

            let child_idx = self.nodes[idx].children[key[0] as usize] as usize;
            let child = &self.nodes[child_idx];
            let len = ((chunk ^ child.prefix).leading_zeros() as u8).min(child.len).min(size as u8);

            if len == child.len {
                self.modify_rec(&key[len as usize..], f, child_idx);
            } else {
                self.nodes[idx].children[key[0] as usize] = self.len() as u32;
                let child = &mut self.nodes[child_idx];
                child.prefix <<= len;
                child.len -= len;
                let prefix = child.prefix;
                self.nodes.push(BinaryRadixTreeNode {
                    prefix: chunk >> (64-len) << (64-len),
                    len,
                    children: if prefix >> 63 == 1 { [u32::MAX, child_idx as u32] } else { [child_idx as u32, u32::MAX] },
                    value: M::identity(),
                    aggregate: M::identity(),
                });

                self.modify_rec(&key[len as usize..], f, self.len()-1);
            }
        }
        
        self.update(idx);
    }

    pub fn set(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, value: M::S) {
        self.modify(key, |_| value);
    }

    pub fn prod<'a, R: std::ops::RangeBounds<&'a bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>>>(&self, range: R) -> M::S {
        self.prod_rec(range.start_bound().cloned(), range.end_bound().cloned(), 0)
    }

    fn prod_rec(&self, left: std::ops::Bound<&bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>>, right: std::ops::Bound<&bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>>, idx: usize) -> M::S {
        use bitvec::field::BitField;
        use std::ops::Bound::*;

        if let Unbounded = right {
            if let Included(key) = left && key.is_empty() {
                return self.nodes[idx].aggregate.clone();
            }
            if let Unbounded = left {
                return self.nodes[idx].aggregate.clone();
            }
        }

        let mut r =
            if let Excluded(key) = right && key.is_empty() {
                M::identity()
            } else if let Included(key) = left && key.is_empty() {
                self.nodes[idx].value.clone()
            } else if let Unbounded = left {
                self.nodes[idx].value.clone()
            } else {
                M::identity()
            };

        for i in 0..2 {
            let child_idx = self.nodes[idx].children[i] as usize;
            if let Some(child) = self.nodes.get(child_idx) {
                let left_key = match left {
                    Included(key) => Some(key),
                    Excluded(key) => Some(key),
                    Unbounded => None,
                };

                let right_key = match right {
                    Included(key) => Some(key),
                    Excluded(key) => Some(key),
                    Unbounded => None,
                };

                let new_left =
                    if let Some(key) = left_key {
                        if key.is_empty() {
                            None
                        } else if key.len() < child.len as usize {
                            let chunk = key.load_be::<u64>() << (64-key.len());
                            if chunk <= child.prefix {
                                None
                            } else {
                                continue;
                            }
                        } else {
                            let chunk = key[..child.len as usize].load_be::<u64>() << (64-child.len);
                            if chunk < child.prefix {
                                None
                            } else if chunk > child.prefix {
                                continue;
                            } else {
                                Some(&key[child.len as usize..])
                            }
                        }
                    } else {
                        None
                    };

                let new_left =
                    if let Some(new_left) = new_left {
                        if let Included(_) = left {
                            Included(new_left)
                        } else {
                            Excluded(new_left)
                        }
                    } else {
                        Unbounded
                    };

                let new_right =
                    if let Some(key) = right_key {
                        if key.is_empty() {
                            continue;
                        } else if key.len() < child.len as usize {
                            let chunk = key.load_be::<u64>() << (64-key.len());
                            if chunk > child.prefix {
                                None
                            } else {
                                continue;
                            }
                        } else {
                            let chunk = key[..child.len as usize].load_be::<u64>() << (64-child.len);
                            if child.prefix < chunk {
                                None
                            } else if child.prefix > chunk {
                                continue;
                            } else {
                                Some(&key[child.len as usize..])
                            }
                        }
                    } else {
                        None
                    };

                let new_right =
                    if let Some(new_right) = new_right {
                        if let Included(_) = right {
                            Included(new_right)
                        } else {
                            Excluded(new_right)
                        }
                    } else {
                        Unbounded
                    };

                r = M::binary_operation(&r, &self.prod_rec(new_left, new_right, child_idx));
            }
        }

        r
    }

    pub fn prod_prefix(&self, mut key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>) -> M::S {
        use bitvec::field::BitField;
        let mut idx = 0;
        let mut acc = M::identity();
        loop {
            acc = M::binary_operation(&acc, &self.nodes[idx].value);
            if key.is_empty() { break; }
            
            let child_idx = self.nodes[idx].children[key[0] as usize] as usize;
            if let Some(child) = self.nodes.get(child_idx) {
                if key.len() < child.len as usize || key[..child.len as usize].load_be::<u64>() << (64-child.len) != child.prefix {
                    break;
                }
                
                idx = child_idx;
                key = &key[child.len as usize..];
            } else {
                break;
            }
        }
        
        acc
    }
    
    pub fn max_right(&self, left: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, f: impl Fn(&M::S) -> bool) -> Option<bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>> {
        assert!(f(&M::identity()));
        self.max_right_rec(left, &f, 0, &mut M::identity()).map(|mut v| {
            v.reverse();
            v
        })
    }

    fn max_right_rec(&self, left: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, f: &impl Fn(&M::S) -> bool, idx: usize, acc: &mut M::S) -> Option<bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>> {
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
                let mut v = BitVec::repeat(false, node.len as usize);
                if node.len > 0 {
                    v.store_be(node.prefix.reverse_bits());
                }
                return Some(v);
            }
            *acc = new_acc;
        }

        for i in 0..2 {
            let child_idx = node.children[i] as usize;
            if let Some(child) = self.nodes.get(child_idx) {
                let v =
                    if left.is_empty() {
                        self.max_right_rec(left, f, child_idx, acc)
                    } else if left.len() < child.len as usize {
                        let chunk = left.load_be::<u64>() << (64-left.len());
                        if chunk <= child.prefix {
                            self.max_right_rec(BitSlice::empty(), f, child_idx, acc)
                        } else {
                            continue;
                        }
                    } else {
                        let chunk = left[..child.len as usize].load_be::<u64>() << (64-child.len);
                        if chunk < child.prefix {
                            self.max_right_rec(BitSlice::empty(), f, child_idx, acc)
                        } else if chunk == child.prefix {
                            self.max_right_rec(&left[child.len as usize..], f, child_idx, acc)
                        } else {
                            continue;
                        }
                    };

                if let Some(mut v) = v {
                    if node.len > 0 {
                        let l = v.len();
                        v.resize(v.len()+node.len as usize, false);
                        v[l..].store_be(node.prefix.reverse_bits());
                    }
                    return Some(v);
                }
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


// 動的セグ木のような使い方: https://atcoder.jp/contests/abc403/submissions/79303011
#[derive(Clone)]
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
        use std::ops::Bound::*;
        let start = match range.start_bound().cloned() {
            Included(it) => {
                Included(bitvec::prelude::BitSlice::from_slice(it))
            },
            Excluded(it) => {
                Excluded(bitvec::prelude::BitSlice::from_slice(it))
            },
            Unbounded => Unbounded,
        };
        let end = match range.end_bound().cloned() {
            Included(it) => {
                Included(bitvec::prelude::BitSlice::from_slice(it))
            },
            Excluded(it) => {
                Excluded(bitvec::prelude::BitSlice::from_slice(it))
            },
            Unbounded => Unbounded,
        };
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

pub struct BinaryRadixTreeCursorMut<'a, M: ac_library::Monoid> {
    tree: &'a mut BinaryRadixTree<M>,
    path: Vec<u32>,
    key: bitvec::prelude::BitVec<usize, bitvec::prelude::Msb0>,
    extra_len: usize
}

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
    
    pub fn key(&self) -> &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0> {
        &self.key
    }
    
    pub fn value(&self) -> M::S {
        if self.extra_len == 0 {
            self.tree.nodes[*self.path.last().unwrap() as usize].value.clone()
        } else {
            M::identity()
        }
    }
    
    pub fn aggregate(&self) -> M::S {
        use bitvec::field::BitField;
        if self.extra_len == 0 {
            self.tree.nodes[*self.path.last().unwrap() as usize].aggregate.clone()
        } else {
            let key = &self.key[self.key.len()-self.extra_len..];
            let child_idx = self.tree.nodes[*self.path.last().unwrap() as usize].children[key[0] as usize] as usize;
            if self.extra_len <= 64 && let Some(child) = self.tree.nodes.get(child_idx) {
                let mask =
                    if self.extra_len == 64 {
                        !0
                    } else {
                        !0 >> (64-self.extra_len) << (64-self.extra_len)
                    };
                if self.extra_len <= child.len as usize && key.load_be::<u64>() << (64-self.extra_len) == child.prefix & mask {
                    child.aggregate.clone()
                } else {
                    M::identity()
                }
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
            let node = &self.tree.nodes[self.path.pop().unwrap() as usize];
            self.extra_len = node.len as usize;
            
            let min = bits.min(self.extra_len);
            bits -= min;
            self.extra_len -= min;
            self.tree.update(*self.path.last().unwrap() as usize);
        }
    }
    
    pub fn down(&mut self, dir: bool) {
        use bitvec::field::BitField;
        self.key.push(dir);
        self.extra_len += 1;
        let key = &self.key[self.key.len()-self.extra_len..];
        let child_idx = self.tree.nodes[*self.path.last().unwrap() as usize].children[key[0] as usize];
        if let Some(child) = self.tree.nodes.get(child_idx as usize) && self.extra_len <= 64
            && self.extra_len == child.len as usize && key.load_be::<u64>() << (64-self.extra_len) == child.prefix {
            self.path.push(child_idx);
            self.extra_len = 0
        }
    }
    
    fn down_usize(&mut self, key: usize) {
        use bitvec::field::BitField;
        let len = self.key.len();
        self.key.resize(len+64, false);
        self.key[len..].store_be(key);
        self.extra_len += 64;
        let mut key = &self.key[self.key.len()-self.extra_len..];
        let mut idx = *self.path.last().unwrap() as usize;
        
        while !key.is_empty() {
            let child_idx = self.tree.nodes[idx].children[key[0] as usize];
            if let Some(child) = self.tree.nodes.get(child_idx as usize) {
                if self.extra_len >= child.len as usize && key[..child.len as usize].load_be::<u64>() << (64-child.len) == child.prefix {
                    self.path.push(child_idx);
                    key = &key[child.len as usize..];
                    idx = child_idx as usize;
                    self.extra_len -= child.len as usize;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }
}

impl<'a, M: ac_library::Monoid> Drop for BinaryRadixTreeCursorMut<'a, M> {
    fn drop(&mut self) {
        self.up(self.key.len());
    }
}

// https://atcoder.jp/contests/abc353/submissions/79323824
pub struct RadixTreeCursorMut<'a, M: ac_library::Monoid> {
    binary_cursor: BinaryRadixTreeCursorMut<'a, M>,
}

impl<'a, M: ac_library::Monoid> RadixTreeCursorMut<'a, M> {
    pub fn modify(&mut self, f: impl FnOnce(&M::S) -> M::S) {
        self.binary_cursor.modify(f);
    }
    
    pub fn set(&mut self, value: M::S) {
        self.binary_cursor.set(value);
    }
    
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

impl<M: ac_library::Monoid> BinaryRadixTree<M> {
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
    pub fn cursor_mut(&mut self) -> RadixTreeCursorMut<'_, M> {
        RadixTreeCursorMut {
            binary_cursor: self.tree.cursor_mut(),
        }
    }
}
