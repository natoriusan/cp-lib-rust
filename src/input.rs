unsafe extern "C" {
    fn fstat(fd: i32, stat_ptr: *mut u8) -> i32;
    fn mmap(addr: *mut u8, length: usize, prot: i32, flags: i32, fd: i32, offset: isize) -> *mut u8;
}

pub fn mmap_input() -> *const u8 {
    let mut stat_buf = [0u64; 18];
    unsafe {
        fstat(0, stat_buf.as_mut_ptr() as *mut u8);
        let len = stat_buf[6] as usize;
    
        mmap(std::ptr::null_mut(), len, 1, 2, 0, 0) as *const u8
    }
}

pub fn mmap_input_mut() -> *mut u8 {
    let mut stat_buf = [0u64; 18];
    unsafe {
        fstat(0, stat_buf.as_mut_ptr() as *mut u8);
        let len = stat_buf[6] as usize;
    
        mmap(std::ptr::null_mut(), len, 3, 2, 0, 0)
    }
}


#[inline(always)]
pub fn parse_digits_u64(mut x: u64) -> u32 {
    x &= 0x0F0F0F0F0F0F0F0F;
    x = (x * 0x0A01) >> 8;
    x &= 0x00FF00FF00FF00FF;
    x = (x * 0x00640001) >> 16;
    x &= 0x0000FFFF0000FFFF;
    x = (x * 0x271000000001) >> 32;
    x as u32
}

#[inline(always)]
pub fn parse_digits_u32(mut x: u32) -> u32 {
    x &= 0x0F0F0F0F;
    x = (x * 0x0A01) >> 8;
    x &= 0x00FF00FF;
    x = (x * 0x00640001) >> 16;
    x
}

#[inline(always)]
pub fn parse_digits_u16(mut x: u16) -> u16 {
    x &= 0x0F0F;
    x = (x * 0x0A01) >> 8;
    x
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn read_u32(ptr: &mut *const u8) -> u32 {
    let bytes = unsafe { (*ptr as *const u64).read_unaligned().to_le() };
    let whitespace = bytes.wrapping_sub(0x3030303030303030) & 0x8080808080808080;

    if whitespace != 0 {
        let length = (unsafe { core::arch::x86_64::_tzcnt_u64(whitespace) } >> 3) as usize;
        unsafe {
            *ptr = ptr.add(length+1);
        }
        parse_digits_u64(bytes << (64-(length<<3)))
    } else {
        let r = parse_digits_u64(bytes);
        unsafe {
            *ptr = ptr.add(8);
        }

        let bytes = unsafe { (*ptr as *const u16).read_unaligned().to_le() };
        let whitespace = bytes.wrapping_sub(0x3030) & 0x8080;
        let length = (unsafe { core::arch::x86_64::_tzcnt_u16(whitespace) } >> 3) as usize;
        unsafe {
            *ptr = ptr.add(length+1);
        }
        if length == 0 {
            r
        } else {
            r * if length == 1 { 10 } else { 100 } + parse_digits_u16(bytes << (64-(length<<3))) as u32
        }
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn read_u32_small(ptr: &mut *const u8) -> u32 {
    let bytes = unsafe { (*ptr as *const u64).read_unaligned().to_le() };
    let whitespace = bytes.wrapping_sub(0x3030303030303030) & 0x8080808080808080;

    let length = (unsafe { core::arch::x86_64::_tzcnt_u64(whitespace) } >> 3) as usize;
    unsafe {
        *ptr = ptr.add(length+1);
    }
    parse_digits_u64(bytes << (64-(length<<3)))
}

// n != 0
#[inline(always)]
pub fn write_u32(ptr: &mut *mut u8, mut n: u32) {
    unsafe {
        let length = n.ilog10() as usize + 1;
        *ptr = ptr.add(length+1);
        let mut p = ptr.sub(1);
        while n > 0 {
            p = p.sub(1);
            let val = (n % 10) as usize;
            n /= 10;
            *p = val as u8 + b'0';
        }
    }
}

// n != 0
#[inline(always)]
pub fn write_u64(ptr: &mut *mut u8, mut n: u64) {
    unsafe {
        let length = n.ilog10() as usize + 1;
        *ptr = ptr.add(length+1);
        let mut p = ptr.sub(1);
        while n > 0 {
            p = p.sub(1);
            let val = (n % 10) as usize;
            n /= 10;
            *p = val as u8 + b'0';
        }
    }
}

// そんなに速くない
// https://atcoder.jp/contests/arc191/submissions/75606171
#[inline(always)]
#[cfg(target_arch = "x86_64")]
pub fn write_u32_simd(ptr: &mut *mut u8, n: u32) {
    use std::arch::x86_64::*;
    unsafe {
        let v64 = _mm_set_epi64x((n%100000000) as i64, (n/100000000) as i64);

        let v32div = _mm_srli_epi32::<8>(_mm_mul_epu32(v64, _mm_set1_epi32(109951163)));
        let v32mod = _mm_sub_epi32(_mm_bslli_si128::<4>(v64), _mm_mullo_epi32(v32div, _mm_set1_epi32(10000)));
        let v32divmod = _mm_blend_epi32::<0b1010>(_mm_bsrli_si128::<4>(v32div), v32mod);

        let v16div = _mm_srli_epi16::<3>(_mm_mulhi_epu16(v32divmod, _mm_set1_epi16(5243)));
        let v16mod = _mm_bslli_si128::<2>(_mm_sub_epi16(v32divmod, _mm_mullo_epi16(v16div, _mm_set1_epi16(100))));
        let v16divmod = _mm_or_si128(v16div, v16mod);


        let v8div = _mm_mulhi_epu16(v16divmod, _mm_set1_epi16(6554));
        let v8mod = _mm_bslli_si128::<1>(_mm_sub_epi8(v16divmod, _mm_mullo_epi16(v8div, _mm_set1_epi16(10))));
        let v8divmod = _mm_or_si128(v8div, v8mod);

        let skip = {
            let one = _tzcnt_u64(_mm_extract_epi64(v8divmod, 0) as u64) / 8;
            if one == 8 {
                one + _tzcnt_u64(_mm_extract_epi64(v8divmod, 1) as u64) / 8
            } else {
                one
            }
        } as usize;

        _mm_mask_compressstoreu_epi8(*ptr as *mut i8, 0xFFFFu16 << skip, _mm_add_epi8(v8divmod, _mm_set1_epi8(b'0' as i8)));
        *ptr = ptr.add(17-skip);
    }
}
