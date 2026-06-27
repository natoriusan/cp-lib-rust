#[allow(dead_code)]
pub trait ConstructGraph<T> {
    /// Constructs an undirected graph from Vec of 0-indexed edge pairs
    fn graph(&self, size: usize) -> Vec<Vec<T>>;

    /// Constructs a directed graph from Vec of 0-indexed edge pairs
    fn directed_graph(&self, size: usize) -> Vec<Vec<T>>;
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
}


#[allow(dead_code)]
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

#[allow(unused_imports)]
pub fn bfs<D, D1: Ord + Copy, V: Ord + Copy>(mut dist: D, get_dist_mut: impl Fn(&mut D, V) -> &mut Option<D1>, initial: (D1, V), next: impl Fn(&mut dyn FnMut(D1, V), D1, V)) -> D {
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

#[allow(unused_imports)]
pub fn bfs01<D, D1: Ord + Copy, V: Ord + Copy>(mut dist: D, get_dist_mut: impl Fn(&mut D, V) -> &mut Option<D1>, initial: (D1, V), next: impl Fn(&mut dyn FnMut(D1, V), D1, V)) -> D {
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

#[allow(unused_imports)]
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
