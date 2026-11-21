pub trait ConstructGraph<T> {
    /// Constructs an undirected graph from Vec of 0-indexed edge pairs
    fn graph(&self, size: usize) -> Vec<Vec<T>>;

    /// Constructs a directed graph from Vec of 0-indexed edge pairs
    fn directed_graph(&self, size: usize) -> Vec<Vec<T>>;
    
    fn rooted_tree(&self, root: usize) -> Vec<Vec<T>>;
    
    fn rooted_parents(&self, root: usize) -> Vec<T> where T: Default;
}

impl ConstructGraph<usize> for Vec<(usize, usize)> {
    #[inline(always)]
    fn graph(&self, size: usize) -> Vec<Vec<usize>> {
        let mut graph = vec![vec![]; size];
        for &(u, v) in self {
            graph[u].push(v);
            graph[v].push(u);
        }

        graph
    }

    #[inline(always)]
    fn directed_graph(&self, size: usize) -> Vec<Vec<usize>> {
        let mut graph = vec![vec![]; size];
        for &(u, v) in self {
            graph[u].push(v);
        }

        graph
    }

    fn rooted_tree(&self, root: usize) -> Vec<Vec<usize>> {
        let graph = self.graph(self.len()+1);
        
        fn dfs(graph: &[Vec<usize>], tree: &mut [Vec<usize>], i: usize, prev: usize) {
            for &j in &graph[i] {
                if j != prev {
                    tree[i].push(j);
                    dfs(graph, tree, j, i);
                }
            }
        }
        
        let mut tree = vec![vec![]; self.len()+1];
        dfs(&graph, &mut tree, root, root);
        
        tree
    }

    fn rooted_parents(&self, root: usize) -> Vec<usize> {
        let graph = self.graph(self.len()+1);

        fn dfs(graph: &[Vec<usize>], parent: &mut [usize], i: usize, prev: usize) {
            parent[i] = prev;
            for &j in &graph[i] {
                if j != prev {
                    dfs(graph, parent, j, i);
                }
            }
        }

        let mut parent = vec![0; self.len()+1];
        dfs(&graph, &mut parent, root, root);
        
        parent
    }
}

impl<T: Copy> ConstructGraph<(usize, T)> for Vec<(usize, usize, T)> {
    #[inline(always)]
    fn graph(&self, size: usize) -> Vec<Vec<(usize, T)>> {
        let mut graph = vec![vec![]; size];
        for &(u, v, w) in self {
            graph[u].push((v, w));
            graph[v].push((u, w));
        }

        graph
    }

    #[inline(always)]
    fn directed_graph(&self, size: usize) -> Vec<Vec<(usize, T)>> {
        let mut graph = vec![vec![]; size];
        for &(u, v, w) in self {
            graph[u].push((v, w));
        }

        graph
    }

    fn rooted_tree(&self, root: usize) -> Vec<Vec<(usize, T)>> {
        let graph = self.graph(self.len()+1);

        fn dfs<T: Copy>(graph: &[Vec<(usize, T)>], tree: &mut [Vec<(usize, T)>], i: usize, prev: usize) {
            for &(j, w) in &graph[i] {
                if j != prev {
                    tree[i].push((j, w));
                    dfs(graph, tree, j, i);
                }
            }
        }

        let mut tree = vec![vec![]; self.len()+1];
        dfs(&graph, &mut tree, root, root);

        tree
    }

    fn rooted_parents(&self, root: usize) -> Vec<(usize, T)> where (usize, T): Default {
        let graph = self.graph(self.len()+1);

        fn dfs<T: Copy>(graph: &[Vec<(usize, T)>], parent: &mut [(usize, T)], i: usize, prev: (usize, T)) {
            parent[i] = prev;
            for &(j, w) in &graph[i] {
                if j != prev.0 {
                    dfs(graph, parent, j, (i, w));
                }
            }
        }

        let mut parent = vec![<(usize, T)>::default(); self.len()+1];
        let prev = (root, parent[0].1);
        dfs(&graph, &mut parent, root, prev);

        parent
    }
}


pub trait EulerTour {
    fn euler_tour(&self) -> Vec<(usize, usize)>;
}

impl EulerTour for Vec<Vec<usize>> {
    fn euler_tour(&self) -> Vec<(usize, usize)> {
        fn dfs(graph: &Vec<Vec<usize>>, indices: &mut Vec<(usize, usize)>, i: usize, from: usize, index: &mut usize) {
            indices[i].0 = *index;
            *index += 1;

            for &j in &graph[i] {
                if j != from {
                    dfs(graph, indices, j, i, index);
                }
            }

            indices[i].1 = *index;
            *index += 1;
        }

        let n = self.len();
        let mut indices = vec![(0, 0); n];
        dfs(self, &mut indices, 0, n, &mut 0);

        indices
    }
}

pub fn bfs<D, D1: Ord + Copy, V: Copy>(mut dist: D, get_dist_mut: impl Fn(&mut D, V) -> &mut Option<D1>, initial: (D1, V), next: impl Fn(&mut dyn FnMut(D1, V), D1, V)) -> D {
    use std::collections::VecDeque;

    let mut queue = VecDeque::new();
    queue.push_back(initial.1);
    *get_dist_mut(&mut dist, initial.1) = Some(initial.0);

    while let Some(v) = queue.pop_front() {
        let d = get_dist_mut(&mut dist, v).unwrap();

        next(&mut |dn, vn| {
            if get_dist_mut(&mut dist, vn).is_none() {
                *get_dist_mut(&mut dist, vn) = Some(dn);
                queue.push_back(vn);
            }
        }, d, v);
    }

    dist
}

pub fn bfs01<D, D1: Ord + Copy, V: Copy>(mut dist: D, get_dist_mut: impl Fn(&mut D, V) -> &mut Option<D1>, initial: (D1, V), next: impl Fn(&mut dyn FnMut(D1, V), D1, V)) -> D {
    use std::collections::VecDeque;

    let mut queue = VecDeque::new();
    queue.push_back(initial);

    while let Some((d, v)) = queue.pop_front() {
        let dv = get_dist_mut(&mut dist, v);
        if dv.is_none() {
            *dv = Some(d);

            next(&mut |dn, vn| {
                if get_dist_mut(&mut dist, vn).is_none() {
                    if dn > d {
                        queue.push_back((dn, vn));
                    } else {
                        queue.push_front((dn, vn));
                    }
                }
            }, d, v);
        }
    }

    dist
}

pub fn dijkstra<D, D1: Ord + Copy, V: Ord + Copy>(mut dist: D, get_dist_mut: impl Fn(&mut D, V) -> &mut Option<D1>, initial: (D1, V), next: impl Fn(&mut dyn FnMut(D1, V), D1, V)) -> D {
    use std::collections::BinaryHeap;
    use std::cmp::Reverse;

    let mut queue = BinaryHeap::new();
    queue.push((Reverse(initial.0), initial.1));

    while let Some((Reverse(d), v)) = queue.pop() {
        let dv = get_dist_mut(&mut dist, v);
        if dv.is_none() {
            *dv = Some(d);

            next(&mut |d, v| {
                if get_dist_mut(&mut dist, v).is_none() {
                    queue.push((Reverse(d), v));
                }
            }, d, v);
        }
    }

    dist
}
