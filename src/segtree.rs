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
        assert!(lb < self.n);
        assert!(rb <= self.n);

        if lb >= rb {
            M::identity()
        } else {
            prod_tree::<M>(&self.nodes.borrow(), lb, rb, self.root, 0, self.n)
        }
    }
}
