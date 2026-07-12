pub mod graph;
pub mod input;
pub mod math;
pub mod misc;
pub mod segtree;
pub mod set;

#[macro_export]
macro_rules! yes_no {
    ($b:expr) => {
        println!("{}", if $b { "Yes" } else { "No" });
    };
}

#[macro_export]
macro_rules! read_unsigned {
    ($ptr:expr, $t:ty) => {
        unsafe {
            let mut r = 0;
            while *$ptr > b' ' {
                r = r*10 + (*$ptr-b'0') as $t;
                $ptr = $ptr.add(1);
            }
            $ptr = $ptr.add(1);
            r
        }
    };
}
