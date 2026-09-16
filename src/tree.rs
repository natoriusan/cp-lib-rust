struct BinaryRadixTreeNode<M: ac_library::Monoid> {
    prefix: u64,
    len: u8,
    children: [u32; 2],
    value: M::S,
    aggregate: M::S
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

    pub fn set(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, value: M::S) {
        self.set_rec(key, value, 0);
    }

    fn set_rec(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, value: M::S, idx: usize) {
        use bitvec::field::BitField;
        if key.is_empty() {
            self.nodes[idx].value = value;
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
                self.set_rec(&key[len as usize..], value, child_idx);
            } else {
                self.nodes[idx].children[key[0] as usize] = self.len() as u32;
                self.nodes[child_idx].prefix <<= len;
                self.nodes[child_idx].len -= len;
                self.nodes.push(BinaryRadixTreeNode {
                    prefix: chunk >> (64-len) << (64-len),
                    len,
                    children: if self.nodes[child_idx].prefix >> 63 == 1 { [u32::MAX, child_idx as u32] } else { [child_idx as u32, u32::MAX] },
                    value: M::identity(),
                    aggregate: M::identity(),
                });

                self.set_rec(&key[len as usize..], value, self.len()-1);

            }
        }

        let mut agg = M::identity();
        for i in self.nodes[idx].children {
            if i != u32::MAX {
                agg = M::binary_operation(&agg, &self.nodes[i as usize].aggregate);
            }
        }
        self.nodes[idx].aggregate = M::binary_operation(&self.nodes[idx].value.clone(), &agg);
    }

    pub fn get(&self, mut key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>) -> M::S {
        use bitvec::field::BitField;
        let mut idx = 0;
        loop {
            if key.is_empty() { break self.nodes[idx].value.clone(); }

            let child_idx = self.nodes[idx].children[key[0] as usize];
            if child_idx == u32::MAX { break M::identity(); }

            let child = &self.nodes[child_idx as usize];
            if key.len() < child.len as usize || key[..child.len as usize].load_be::<u64>() << (64-child.len) != child.prefix { break M::identity(); }

            idx = child_idx as usize;
            key = &key[child.len as usize..];
        }
    }

    pub fn modify(&mut self, key: &bitvec::prelude::BitSlice<usize, bitvec::prelude::Msb0>, f: impl FnOnce(M::S) -> M::S) {
        self.set(key, f(self.get(key)))
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
            let child_idx = self.nodes[idx].children[i];
            if child_idx != u32::MAX {
                let child = &self.nodes[child_idx as usize];
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

                r = M::binary_operation(&r, &self.prod_rec(new_left, new_right, child_idx as usize));
            }
        }

        r
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
            let child_idx = node.children[i];
            if child_idx != u32::MAX {
                let child = &self.nodes[child_idx as usize];
                let v =
                    if left.is_empty() {
                        self.max_right_rec(left, f, child_idx as usize, acc)
                    } else if left.len() < child.len as usize {
                        let chunk = left.load_be::<u64>() << (64-left.len());
                        if chunk <= child.prefix {
                            self.max_right_rec(BitSlice::empty(), f, child_idx as usize, acc)
                        } else {
                            continue;
                        }
                    } else {
                        let chunk = left[..child.len as usize].load_be::<u64>() << (64-child.len);
                        if chunk < child.prefix {
                            self.max_right_rec(BitSlice::empty(), f, child_idx as usize, acc)
                        } else if chunk == child.prefix {
                            self.max_right_rec(&left[child.len as usize..], f, child_idx as usize, acc)
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
