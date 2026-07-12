const DIJ: [(usize, usize); 4] = [(1, 0), (1usize.wrapping_neg(), 0), (0, 1), (0, 1usize.wrapping_neg())];
#[inline(always)]
pub fn neighborhood4(h: usize, w: usize, i: usize, j: usize) -> impl Iterator<Item = (usize, usize)> {
    DIJ.iter().filter_map(move |&(di, dj)| {
        let k = i.wrapping_add(di);
        let l = j.wrapping_add(dj);
        if k < h && l < w {
            Some((k, l))
        } else {
            None
        }
    })
}

const DIJ8: [(usize, usize); 8] = [(1usize.wrapping_neg(), 1usize.wrapping_neg()), (1usize.wrapping_neg(), 0), (1usize.wrapping_neg(), 1), (0, 1usize.wrapping_neg()), (0, 1), (1, 1usize.wrapping_neg()), (1, 0), (1, 1)];
#[inline(always)]
pub fn neighborhood8(h: usize, w: usize, i: usize, j: usize) -> impl Iterator<Item = (usize, usize)> {
    DIJ8.iter().filter_map(move |&(di, dj)| {
        let k = i.wrapping_add(di);
        let l = j.wrapping_add(dj);
        if (di != 0 || dj != 0) && k < h && l < w {
            Some((k, l))
        } else {
            None
        }
    })
}


pub trait ChMaxMin<T> {
    fn chmax(&mut self, val: T);
    fn chmin(&mut self, val: T);
}

impl<T: Copy + Ord> ChMaxMin<T> for T {
    #[inline(always)]
    fn chmax(&mut self, val: T) {
        *self = (*self).max(val);
    }

    #[inline(always)]
    fn chmin(&mut self, val: T) {
        *self = (*self).min(val);
    }
}
