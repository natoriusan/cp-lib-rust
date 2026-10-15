// BTreeMapをmultisetのように扱うときの補助用の関数
pub trait MultiSet<T> {
    fn insert_multiset(&mut self, value: T);
    fn remove_multiset(&mut self, value: &T);
}

impl<T: Eq + Ord> MultiSet<T> for std::collections::BTreeMap<T, usize> {
    #[inline(always)]
    fn insert_multiset(&mut self, value: T) {
        *self.entry(value).or_insert(0) += 1;
    }

    #[inline(always)]
    fn remove_multiset(&mut self, value: &T) {
        if self[value] == 1 {
            self.remove(value);
        } else {
            *self.get_mut(value).unwrap() -= 1;
        }
    }
}


// 大きい方からk個に対して、何らかの値を求める
// ACLのSegtreeのようにstructにimplして渡す
// https://atcoder.jp/contests/abc306/submissions/72399998
pub trait TopKOperation {
    type V: Clone + Eq + Ord;
    type D: Default;
    fn data_insert(data: &mut Self::D, value: &Self::V);
    fn data_remove(data: &mut Self::D, value: &Self::V);
}

#[derive(Debug)]
pub struct TopK<T: TopKOperation> {
    pub top: std::collections::BTreeMap<T::V, usize>,
    pub other: std::collections::BTreeMap<T::V, usize>,
    pub top_data: T::D,
    pub other_data: T::D,
    k: usize,
    top_count: usize,
}

impl<T: TopKOperation> TopK<T> {
    pub fn new(k: usize) -> Self {
        TopK {
            top: std::collections::BTreeMap::new(),
            other: std::collections::BTreeMap::new(),
            top_data: T::D::default(),
            other_data: T::D::default(),
            k,
            top_count: 0,
        }
    }

    pub fn insert(&mut self, value: T::V) {
        T::data_insert(&mut self.other_data, &value);
        self.other.insert_multiset(value);
        self.balance();
    }

    pub fn remove(&mut self, value: &T::V) {
        if self.other.contains_key(value) {
            T::data_remove(&mut self.other_data, value);
            self.other.remove_multiset(value);
        } else {
            T::data_remove(&mut self.top_data, value);
            self.top.remove_multiset(value);
            self.top_count -= 1;
        }
        self.balance();
    }

    pub fn balance(&mut self) {
        while self.top_count > self.k {
            let val = self.top.first_key_value().unwrap().0.clone();

            T::data_remove(&mut self.top_data, &val);
            self.top.remove_multiset(&val);
            T::data_insert(&mut self.other_data, &val);
            self.other.insert_multiset(val);

            self.top_count -= 1;
        }
        while self.top_count < self.k && let Some(val) = self.other.last_key_value().map(|(i, _)| i.clone()) {
            T::data_remove(&mut self.other_data, &val);
            self.other.remove_multiset(&val);
            T::data_insert(&mut self.top_data, &val);
            self.top.insert_multiset(val);
            self.top_count += 1;
        }

        while let Some((t, _)) = self.top.first_key_value()
            && let Some((o, _)) = self.other.last_key_value()
            && t < o {
            let val1 = t.clone();
            let val2 = o.clone();

            T::data_remove(&mut self.top_data, &val1);
            self.top.remove_multiset(&val1);
            T::data_remove(&mut self.other_data, &val2);
            self.other.remove_multiset(&val2);

            T::data_insert(&mut self.top_data, &val2);
            self.top.insert_multiset(val2);
            T::data_insert(&mut self.other_data, &val1);
            self.other.insert_multiset(val1);
        }
    }

    pub fn update_k(&mut self, k: usize) {
        self.k = k;
        self.balance();
    }
}
