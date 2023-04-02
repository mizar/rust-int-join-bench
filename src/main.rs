#![allow(clippy::missing_safety_doc)]
use itertools::Itertools;
use std::fmt::Write;

fn main() {
    println!("Hello, world!");
}

pub fn to_string_and_join(values: &[usize]) -> String {
    values
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn fold_by_to_string_without_capacity(values: &[usize]) -> String {
    values
        .iter()
        .map(|s| s.to_string())
        .fold(String::new(), |mut acc, cur| {
            acc.push_str(&cur);
            acc.push_str(" ");
            acc
        })
}

pub fn fold_by_to_string_with_capacity(values: &[usize]) -> String {
    values
        .iter()
        .map(|s| s.to_string())
        // 数値一つが最大20桁 + separator1文字で21文字
        .fold(String::with_capacity(21 * values.len()), |mut acc, cur| {
            acc.push_str(&cur);
            acc.push_str(" ");
            acc
        })
}

pub fn itertools_join(values: &[usize]) -> String {
    values.iter().join(" ")
}

pub fn fold_by_write_without_capacity(values: &[usize]) -> String {
    values.iter().fold(String::new(), |mut acc, cur| {
        write!(&mut acc, "{} ", cur).unwrap();
        acc
    })
}

pub fn fold_by_write_with_capacity(values: &[usize]) -> String {
    values
        .iter()
        // 数値一つが最大20桁 + separator1文字で21文字
        .fold(String::with_capacity(21 * values.len()), |mut acc, cur| {
            write!(&mut acc, "{} ", cur).unwrap();
            acc
        })
}

pub fn foreach_by_write_without_capacity(values: &[usize]) -> String {
    let mut acc = String::new();
    values.iter().for_each(|cur| {
        write!(&mut acc, "{} ", cur).unwrap();
    });
    acc
}

pub fn foreach_by_write_with_capacity(values: &[usize]) -> String {
    // 数値一つが最大20桁 + separator1文字で21文字
    let mut acc = String::with_capacity(21 * values.len());
    values.iter().for_each(|cur| {
        write!(&mut acc, "{} ", cur).unwrap();
    });
    acc
}

pub fn dec4_with_capacity_rawbytes_sp(values: &[usize]) -> String {
    let mut v = Vec::<u8>::with_capacity(21 * values.len());
    let p = v.as_mut_ptr();
    let mut pacc = p;
    values.iter().for_each(|&cur| unsafe {
        DEC4LE.rawbytes_sp_u64(&mut pacc, cur as u64);
    });
    // Rust 1.47.0 or later, `dist.offset_from(origin) as usize`
    // <https://doc.rust-lang.org/std/primitive.pointer.html#method.offset_from>
    //unsafe { v.set_len(((pacc as usize) - (p as usize)).saturating_sub(1)) }
    unsafe { v.set_len((pacc.offset_from(p).max(1) as usize) - 1) }
    unsafe { String::from_utf8_unchecked(v) }
}

pub fn dec4_with_capacity_rawbytes_ow_sp(values: &[usize]) -> String {
    let mut v = Vec::<u8>::with_capacity(21 * values.len() + 3);
    let p = v.as_mut_ptr();
    let mut pacc = p;
    values.iter().for_each(|&cur| unsafe {
        DEC4LE.rawbytes_ow_sp_u64(&mut pacc, cur as u64);
    });
    // Rust 1.47.0 or later, `dist.offset_from(origin) as usize`
    // <https://doc.rust-lang.org/std/primitive.pointer.html#method.offset_from>
    //unsafe { v.set_len(((pacc as usize) - (p as usize)).saturating_sub(1)) }
    unsafe { v.set_len((pacc.offset_from(p).max(1) as usize) - 1) }
    unsafe { String::from_utf8_unchecked(v) }
}

pub fn dec4_with_capacity_bytes(values: &[usize]) -> String {
    let mut v = Vec::<u8>::with_capacity(21 * values.len());
    values.iter().for_each(|&cur| unsafe {
        DEC4LE.bytes_sp_u64(&mut v, cur as u64);
    });
    v.pop();
    unsafe { String::from_utf8_unchecked(v) }
}

pub fn dec4_with_capacity_str(values: &[usize]) -> String {
    let mut v = String::with_capacity(21 * values.len());
    values.iter().for_each(|&cur| unsafe {
        DEC4LE.str_sp_u64(&mut v, cur as u64);
    });
    v.pop();
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(20240401);

        let arr = (0..1000000)
            .chain(
                std::iter::repeat_with(|| rng.gen::<usize>() >> rng.gen_range(0..60)).take(1000000),
            )
            .collect::<Vec<_>>();

        let results = [
            to_string_and_join(&arr),
            fold_by_to_string_without_capacity(&arr),
            fold_by_to_string_with_capacity(&arr),
            itertools_join(&arr),
            fold_by_write_without_capacity(&arr),
            fold_by_write_with_capacity(&arr),
            foreach_by_write_without_capacity(&arr),
            foreach_by_write_with_capacity(&arr),
            dec4_with_capacity_bytes(&arr),
            dec4_with_capacity_rawbytes_ow_sp(&arr),
            dec4_with_capacity_rawbytes_sp(&arr),
            dec4_with_capacity_str(&arr),
        ];

        assert!(
            results
                .iter()
                .map(|s| {
                    // 末尾の空白除去
                    s.trim()
                })
                .all_equal(),
            "{:?}",
            results
        );
    }
}

#[macro_export]
macro_rules! invariant {
    ($expr: expr) => {
        debug_assert!($expr);
        if !($expr) {
            unsafe { core::hint::unreachable_unchecked() };
        }
    };
}
pub struct Dec4le((), (), [u32; 100], [u32; 1000], [u32; 10000]);
pub const DEC4LE: Dec4le = Dec4le::new();
impl Dec4le {
    pub const fn new() -> Self {
        // const fn while: Rust 1.46.0 or later
        let (mut d2, mut i) = ([0u32; 100], 0);
        while i < 100 {
            d2[i as usize] = ((i % 10) << 8) | (i / 10) | 0x0020_3030;
            i += 1;
        }
        let (mut d3, mut i) = ([0u32; 1000], 0);
        while i < 1000 {
            let (dh, dl) = (i / 100, i % 100);
            d3[i as usize] = ((dl % 10) << 16) | ((dl / 10) << 8) | dh | 0x2030_3030;
            i += 1;
        }
        let (mut d4, mut i) = ([0u32; 10000], 0);
        while i < 1_0000 {
            let (dh, dl) = (i / 100, i % 100);
            d4[i as usize] =
                0x30303030 | (dh / 10) | ((dh % 10) << 8) | ((dl / 10) << 16) | ((dl % 10) << 24);
            i += 1;
        }
        Self((), (), d2, d3, d4)
    }
    #[inline(always)]
    unsafe fn rawbytes_d1(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10);
        **v = b'0' | x as u8;
        *v = v.add(1);
    }
    #[inline(always)]
    unsafe fn rawbytes_d2(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100);
        v.copy_from_nonoverlapping(self.2[x as usize].to_le_bytes().as_ptr(), 2);
        *v = v.add(2);
    }
    #[inline(always)]
    unsafe fn rawbytes_d3(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000);
        v.copy_from_nonoverlapping(self.3[x as usize].to_le_bytes().as_ptr(), 3);
        *v = v.add(3);
    }
    #[inline(always)]
    unsafe fn rawbytes_d3ow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000);
        v.copy_from_nonoverlapping(self.3[x as usize].to_le_bytes().as_ptr(), 4);
        *v = v.add(3);
    }
    #[inline(always)]
    unsafe fn rawbytes_d4(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1_0000);
        v.copy_from_nonoverlapping(self.4[x as usize].to_le_bytes().as_ptr(), 4);
        *v = v.add(4);
    }
    #[inline(always)]
    unsafe fn rawbytes_d5(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10_0000);
        let (y0, y1) = (x / 10, x % 10);
        v.copy_from_nonoverlapping(
            (((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x0030_0000_0000)
                .to_le_bytes()
                .as_ptr(),
            5,
        );
        *v = v.add(5);
    }
    #[inline(always)]
    unsafe fn rawbytes_d5ow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10_0000);
        let (y0, y1) = (x / 10, x % 10);
        v.copy_from_nonoverlapping(
            (((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x0030_0000_0000)
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(5);
    }
    #[inline(always)]
    unsafe fn rawbytes_d6(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100_0000);
        let (y0, y1) = (x / 100, x % 100);
        v.copy_from_nonoverlapping(
            ((((self.2[y1 as usize] as u16) as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            6,
        );
        *v = v.add(6);
    }
    #[inline(always)]
    unsafe fn rawbytes_d6ow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100_0000);
        let (y0, y1) = (x / 100, x % 100);
        v.copy_from_nonoverlapping(
            ((((self.2[y1 as usize] as u16) as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(6);
    }
    #[inline(always)]
    unsafe fn rawbytes_d7(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000_0000);
        let (y0, y1) = (x / 1000, x % 1000);
        v.copy_from_nonoverlapping(
            (((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            7,
        );
        *v = v.add(7);
    }
    #[inline(always)]
    unsafe fn rawbytes_d7ow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000_0000);
        let (y0, y1) = (x / 1000, x % 1000);
        v.copy_from_nonoverlapping(
            (((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(7);
    }
    #[inline(always)]
    unsafe fn rawbytes_d8(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1_0000_0000);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.copy_from_nonoverlapping(
            (((self.4[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(8);
    }
    #[inline(always)]
    unsafe fn rawbytes_d16(&self, v: &mut *mut u8, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.copy_from_nonoverlapping(
            (((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes()
                .as_ptr(),
            16,
        );
        *v = v.add(16);
    }
    #[inline(always)]
    unsafe fn rawbytes_d1sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10);
        v.copy_from_nonoverlapping(((x as u16) | 0x2030).to_le_bytes().as_ptr(), 2);
        *v = v.add(2);
    }
    #[inline(always)]
    unsafe fn rawbytes_d2sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100);
        v.copy_from_nonoverlapping(self.2[x as usize].to_le_bytes().as_ptr(), 2);
        *v.add(2) = b' ';
        *v = v.add(3);
    }
    #[inline(always)]
    unsafe fn rawbytes_d2spow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100);
        v.copy_from_nonoverlapping(self.2[x as usize].to_le_bytes().as_ptr(), 4);
        *v = v.add(3);
    }
    #[inline(always)]
    unsafe fn rawbytes_d3sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000);
        v.copy_from_nonoverlapping(self.3[x as usize].to_le_bytes().as_ptr(), 4);
        *v = v.add(4);
    }
    #[inline(always)]
    unsafe fn rawbytes_d4sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1_0000);
        v.copy_from_nonoverlapping(self.4[x as usize].to_le_bytes().as_ptr(), 4);
        *v.add(4) = b' ';
        *v = v.add(5);
    }
    #[inline(always)]
    unsafe fn rawbytes_d5sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10_0000);
        let (y0, y1) = (x / 10, x % 10);
        v.copy_from_nonoverlapping(
            (((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x2030_0000_0000)
                .to_le_bytes()
                .as_ptr(),
            6,
        );
        *v = v.add(6);
    }
    #[inline(always)]
    unsafe fn rawbytes_d5spow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 10_0000);
        let (y0, y1) = (x / 10, x % 10);
        v.copy_from_nonoverlapping(
            (((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x2030_0000_0000)
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(6);
    }
    #[inline(always)]
    unsafe fn rawbytes_d6sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100_0000);
        let (y0, y1) = (x / 1000, x % 1000);
        v.copy_from_nonoverlapping(
            (((self.3[y1 as usize] as u64) << 24) | (self.3[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            7,
        );
        *v = v.add(7);
    }
    #[inline(always)]
    unsafe fn rawbytes_d6spow(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 100_0000);
        let (y0, y1) = (x / 1000, x % 1000);
        v.copy_from_nonoverlapping(
            (((self.3[y1 as usize] as u64) << 24) | (self.3[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(7);
    }
    #[inline(always)]
    unsafe fn rawbytes_d7sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1000_0000);
        let (y0, y1) = (x / 1000, x % 1000);
        v.copy_from_nonoverlapping(
            (((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v = v.add(8);
    }
    #[inline(always)]
    unsafe fn rawbytes_d8sp(&self, v: &mut *mut u8, x: u32) {
        invariant!(x < 1_0000_0000);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.copy_from_nonoverlapping(
            (((self.4[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64))
                .to_le_bytes()
                .as_ptr(),
            8,
        );
        *v.add(8) = b' ';
        *v = v.add(9);
    }
    #[inline(always)]
    unsafe fn rawbytes_d16sp(&self, v: &mut *mut u8, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.copy_from_nonoverlapping(
            (((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes()
                .as_ptr(),
            16,
        );
        *v.add(16) = b' ';
        *v = v.add(17);
    }
    #[inline(always)]
    unsafe fn bytes_d1(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 10 && v.capacity() - v.len() >= 1);
        v.push(b'0' + x as u8);
    }
    #[inline(always)]
    unsafe fn bytes_d2(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 100 && v.capacity() - v.len() >= 2);
        v.extend_from_slice(&self.2[x as usize].to_le_bytes()[..2]);
    }
    #[inline(always)]
    unsafe fn bytes_d3(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1000 && v.capacity() - v.len() >= 3);
        v.extend_from_slice(&self.3[x as usize].to_le_bytes()[..3]);
    }
    #[inline(always)]
    unsafe fn bytes_d4(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1_0000 && v.capacity() - v.len() >= 4);
        v.extend_from_slice(&self.4[x as usize].to_le_bytes());
    }
    #[inline(always)]
    unsafe fn bytes_d5(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 10_0000 && v.capacity() - v.len() >= 5);
        let (y0, y1) = (x / 10, x % 10);
        v.extend_from_slice(
            &((((b'0' + y1 as u8) as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()[..5],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d6(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 100_0000 && v.capacity() - v.len() >= 6);
        let (y0, y1) = (x / 100, x % 100);
        v.extend_from_slice(
            &(((self.2[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()
                [..6],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d7(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1000_0000 && v.capacity() - v.len() >= 7);
        let (y0, y1) = (x / 1000, x % 1000);
        v.extend_from_slice(
            &(((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()
                [..7],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d8(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1_0000_0000 && v.capacity() - v.len() >= 8);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.extend_from_slice(
            &(((self.4[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes(),
        );
    }
    #[inline(always)]
    unsafe fn bytes_d16(&self, v: &mut Vec<u8>, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000 && v.capacity() - v.len() >= 16);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.extend_from_slice(
            &(((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes(),
        );
    }
    #[inline(always)]
    unsafe fn bytes_d1sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 10 && v.capacity() - v.len() >= 2);
        v.extend_from_slice(&((x as u16) | 0x2030).to_le_bytes());
    }
    #[inline(always)]
    unsafe fn bytes_d2sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 100 && v.capacity() - v.len() >= 3);
        v.extend_from_slice(&((self.2[x as usize] as u16 as u32) | 0x0020_0000).to_le_bytes()[..3]);
        /*
        v.extend_from_slice(&(self.2[x as usize] as u16 as u32).to_le_bytes());
        invariant!(v.capacity() - v.len() >= 1);
        v.push(b' ');
        // */
    }
    #[inline(always)]
    unsafe fn bytes_d3sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1000 && v.capacity() - v.len() >= 4);
        v.extend_from_slice(&self.3[x as usize].to_le_bytes());
    }
    #[inline(always)]
    unsafe fn bytes_d4sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1_0000 && v.capacity() - v.len() >= 5);
        v.extend_from_slice(&((self.4[x as usize] as u64) | 0x0020_0000_0000).to_le_bytes()[..5]);
    }
    #[inline(always)]
    unsafe fn bytes_d5sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 10_0000 && v.capacity() - v.len() >= 6);
        let (y0, y1) = (x / 10, x % 10);
        v.extend_from_slice(
            &(((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x2030_0000_0000).to_le_bytes()
                [..6],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d6sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 100_0000 && v.capacity() - v.len() >= 7);
        let (y0, y1) = (x / 100, x % 100);
        v.extend_from_slice(
            &(((self.2[y1 as usize] as u16 as u64) << 32)
                | (self.4[y0 as usize] as u64)
                | 0x0020_0000_0000_0000)
                .to_le_bytes()[..7],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d7sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1000_0000 && v.capacity() - v.len() >= 8);
        let (y0, y1) = (x / 1000, x % 1000);
        v.extend_from_slice(
            &(((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes(),
        );
    }
    #[inline(always)]
    unsafe fn bytes_d8sp(&self, v: &mut Vec<u8>, x: u32) {
        invariant!(x < 1_0000_0000 && v.capacity() - v.len() >= 9);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.extend_from_slice(
            &(((self.4[y1 as usize] as u128) << 32)
                | (self.4[y0 as usize] as u128)
                | 0x0020_0000_0000_0000_0000)
                .to_le_bytes()[..9],
        );
    }
    #[inline(always)]
    unsafe fn bytes_d16sp(&self, v: &mut Vec<u8>, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000 && v.capacity() - v.len() >= 16);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.extend_from_slice(
            &(((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes(),
        );
        invariant!(v.capacity() > v.len());
        v.push(b' ');
    }
    #[inline(always)]
    unsafe fn str_d1(&self, v: &mut String, x: u32) {
        invariant!(x < 10 && v.capacity() - v.len() >= 1);
        v.push_str(std::str::from_utf8_unchecked(&[b'0' + x as u8]));
    }
    #[inline(always)]
    unsafe fn str_d2(&self, v: &mut String, x: u32) {
        invariant!(x < 100 && v.capacity() - v.len() >= 2);
        v.push_str(std::str::from_utf8_unchecked(
            &self.2[x as usize].to_le_bytes()[..2],
        ));
    }
    #[inline(always)]
    unsafe fn str_d3(&self, v: &mut String, x: u32) {
        invariant!(x < 1000 && v.capacity() - v.len() >= 3);
        v.push_str(std::str::from_utf8_unchecked(
            &self.3[x as usize].to_le_bytes()[..3],
        ));
    }
    #[inline(always)]
    unsafe fn str_d4(&self, v: &mut String, x: u32) {
        invariant!(x < 1_0000 && v.capacity() - v.len() >= 4);
        v.push_str(std::str::from_utf8_unchecked(
            &self.4[x as usize].to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d5(&self, v: &mut String, x: u32) {
        invariant!(x < 10_0000 && v.capacity() - v.len() >= 5);
        let (y0, y1) = (x / 10, x % 10);
        v.push_str(std::str::from_utf8_unchecked(
            &((((b'0' + y1 as u8) as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()[..5],
        ));
    }
    #[inline(always)]
    unsafe fn str_d6(&self, v: &mut String, x: u32) {
        invariant!(x < 100_0000 && v.capacity() - v.len() >= 6);
        let (y0, y1) = (x / 100, x % 100);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.2[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()
                [..6],
        ));
    }
    #[inline(always)]
    unsafe fn str_d7(&self, v: &mut String, x: u32) {
        invariant!(x < 1000_0000 && v.capacity() - v.len() >= 7);
        let (y0, y1) = (x / 1000, x % 1000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes()
                [..7],
        ));
    }
    #[inline(always)]
    unsafe fn str_d8(&self, v: &mut String, x: u32) {
        invariant!(x < 1_0000_0000 && v.capacity() - v.len() >= 8);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.4[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d16(&self, v: &mut String, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000 && v.capacity() - v.len() >= 16);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d1sp(&self, v: &mut String, x: u32) {
        invariant!(x < 10 && v.capacity() - v.len() >= 2);
        v.push_str(std::str::from_utf8_unchecked(
            &((x as u16) | 0x2030).to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d2sp(&self, v: &mut String, x: u32) {
        invariant!(x < 100 && v.capacity() - v.len() >= 3);
        v.push_str(std::str::from_utf8_unchecked(
            &((self.2[x as usize] as u16 as u32) | 0x0020_0000).to_le_bytes()[..3],
        ));
    }
    #[inline(always)]
    unsafe fn str_d3sp(&self, v: &mut String, x: u32) {
        invariant!(x < 1000 && v.capacity() - v.len() >= 4);
        v.push_str(std::str::from_utf8_unchecked(
            &self.3[x as usize].to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d4sp(&self, v: &mut String, x: u32) {
        invariant!(x < 1_0000 && v.capacity() - v.len() >= 5);
        v.push_str(std::str::from_utf8_unchecked(
            &((self.4[x as usize] as u64) | 0x0020_0000_0000).to_le_bytes()[..5],
        ));
    }
    #[inline(always)]
    unsafe fn str_d5sp(&self, v: &mut String, x: u32) {
        invariant!(x < 10_0000 && v.capacity() - v.len() >= 6);
        let (y0, y1) = (x / 10, x % 10);
        v.push_str(std::str::from_utf8_unchecked(
            &(((y1 as u64) << 32) | (self.4[y0 as usize] as u64) | 0x2030_0000_0000).to_le_bytes()
                [..6],
        ));
    }
    #[inline(always)]
    unsafe fn str_d6sp(&self, v: &mut String, x: u32) {
        invariant!(x < 100_0000 && v.capacity() - v.len() >= 7);
        let (y0, y1) = (x / 100, x % 100);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.2[y1 as usize] as u16 as u64) << 32)
                | (self.4[y0 as usize] as u64)
                | 0x0020_0000_0000_0000)
                .to_le_bytes()[..7],
        ));
    }
    #[inline(always)]
    unsafe fn str_d7sp(&self, v: &mut String, x: u32) {
        invariant!(x < 1000_0000 && v.capacity() - v.len() >= 8);
        let (y0, y1) = (x / 1000, x % 1000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.3[y1 as usize] as u64) << 32) | (self.4[y0 as usize] as u64)).to_le_bytes(),
        ));
    }
    #[inline(always)]
    unsafe fn str_d8sp(&self, v: &mut String, x: u32) {
        invariant!(x < 1_0000_0000 && v.capacity() - v.len() >= 9);
        let (y0, y1) = (x / 1_0000, x % 1_0000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.4[y1 as usize] as u128) << 32)
                | (self.4[y0 as usize] as u128)
                | 0x0020_0000_0000_0000_0000)
                .to_le_bytes()[..9],
        ));
    }
    #[inline(always)]
    unsafe fn str_d16sp(&self, v: &mut String, x: u64) {
        invariant!(x < 1_0000_0000_0000_0000 && v.capacity() - v.len() >= 17);
        let (y0, y1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
        let (z0, z1, z2, z3) = (y0 / 1_0000, y0 % 1_0000, y1 / 1_0000, y1 % 1_0000);
        invariant!(z0 < 1_0000 && z1 < 1_0000 && z2 < 1_0000 && z3 < 1_0000);
        v.push_str(std::str::from_utf8_unchecked(
            &(((self.4[z3 as usize] as u128) << 96)
                | ((self.4[z2 as usize] as u128) << 64)
                | ((self.4[z1 as usize] as u128) << 32)
                | (self.4[z0 as usize] as u128))
                .to_le_bytes(),
        ));
        invariant!(v.capacity() - v.len() >= 1);
        v.push(' ');
    }
    #[inline(always)]
    pub unsafe fn rawbytes_u64(&self, v: &mut *mut u8, x: u64) {
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.rawbytes_d1(v, x as u32),
                10..=99 => self.rawbytes_d2(v, x as u32),
                100..=999 => self.rawbytes_d3(v, x as u32),
                1000..=9999 => self.rawbytes_d4(v, x as u32),
                1_0000..=9_9999 => self.rawbytes_d5(v, x as u32),
                10_0000..=99_9999 => self.rawbytes_d6(v, x as u32),
                100_0000..=999_9999 => self.rawbytes_d7(v, x as u32),
                1000_0000..=9999_9999 => self.rawbytes_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn rawbytes_ow_u64(&self, v: &mut *mut u8, x: u64) {
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.rawbytes_d1(v, x as u32),
                10..=99 => self.rawbytes_d2(v, x as u32),
                100..=999 => self.rawbytes_d3ow(v, x as u32),
                1000..=9999 => self.rawbytes_d4(v, x as u32),
                1_0000..=9_9999 => self.rawbytes_d5ow(v, x as u32),
                10_0000..=99_9999 => self.rawbytes_d6ow(v, x as u32),
                100_0000..=999_9999 => self.rawbytes_d7ow(v, x as u32),
                1000_0000..=9999_9999 => self.rawbytes_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn rawbytes_sp_u64(&self, v: &mut *mut u8, x: u64) {
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.rawbytes_d1sp(v, x as u32),
                10..=99 => self.rawbytes_d2sp(v, x as u32),
                100..=999 => self.rawbytes_d3sp(v, x as u32),
                1000..=9999 => self.rawbytes_d4sp(v, x as u32),
                1_0000..=9_9999 => self.rawbytes_d5sp(v, x as u32),
                10_0000..=99_9999 => self.rawbytes_d6sp(v, x as u32),
                100_0000..=999_9999 => self.rawbytes_d7sp(v, x as u32),
                1000_0000..=9999_9999 => self.rawbytes_d8sp(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16sp(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn rawbytes_ow_sp_u64(&self, v: &mut *mut u8, x: u64) {
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.rawbytes_d1sp(v, x as u32),
                10..=99 => self.rawbytes_d2spow(v, x as u32),
                100..=999 => self.rawbytes_d3sp(v, x as u32),
                1000..=9999 => self.rawbytes_d4sp(v, x as u32),
                1_0000..=9_9999 => self.rawbytes_d5spow(v, x as u32),
                10_0000..=99_9999 => self.rawbytes_d6spow(v, x as u32),
                100_0000..=999_9999 => self.rawbytes_d7sp(v, x as u32),
                1000_0000..=9999_9999 => self.rawbytes_d8sp(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16sp(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn rawbytes_u128(&self, v: &mut *mut u8, x: u128) {
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.rawbytes_d1(v, x as u32),
                10..=99 => self.rawbytes_d2(v, x as u32),
                100..=999 => self.rawbytes_d3ow(v, x as u32),
                1000..=9999 => self.rawbytes_d4(v, x as u32),
                1_0000..=9_9999 => self.rawbytes_d5ow(v, x as u32),
                10_0000..=99_9999 => self.rawbytes_d6ow(v, x as u32),
                100_0000..=999_9999 => self.rawbytes_d7ow(v, x as u32),
                1000_0000..=9999_9999 => self.rawbytes_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    (x % 1_0000_0000_0000_0000) as u64,
                );
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, y0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, y0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, y0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16(v, y1);
            }
            1844_6744_0737_0955_1616..=9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u32;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, y0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, y0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, y0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000..=9999_9999_9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u64;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                let (z0, z1) = ((y0 / 1_0000_0000) as u32, (y0 % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.rawbytes_d1(v, z0),
                    10..=99 => self.rawbytes_d2(v, z0),
                    100..=999 => self.rawbytes_d3ow(v, z0),
                    1000..=9999 => self.rawbytes_d4(v, z0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, z0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, z0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, z0),
                    1000_0000..=9999_9999 => self.rawbytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d8(v, z1);
                self.rawbytes_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000_0000_0000
                ..=340_2823_6692_0938_4634_6337_4607_4317_6821_1455 => {
                let y0 = (x / 1_0000_0000_0000_0000_0000_0000_0000_0000) as u32;
                let y1 = x - (y0 as u128) * 1_0000_0000_0000_0000_0000_0000_0000_0000;
                let z0 = (y1 / 1_0000_0000_0000_0000) as u64;
                let z1 = (y1 - (z0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.rawbytes_d1(v, y0),
                    10..=99 => self.rawbytes_d2(v, y0),
                    100..=999 => self.rawbytes_d3ow(v, y0),
                    1000..=9999 => self.rawbytes_d4(v, y0),
                    1_0000..=9_9999 => self.rawbytes_d5ow(v, y0),
                    10_0000..=99_9999 => self.rawbytes_d6ow(v, y0),
                    100_0000..=999_9999 => self.rawbytes_d7ow(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.rawbytes_d16(v, z0);
                self.rawbytes_d16(v, z1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn bytes_u64(&self, v: &mut Vec<u8>, x: u64) {
        invariant!(v.capacity() - v.len() >= 20);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.bytes_d1(v, x as u32),
                10..=99 => self.bytes_d2(v, x as u32),
                100..=999 => self.bytes_d3(v, x as u32),
                1000..=9999 => self.bytes_d4(v, x as u32),
                1_0000..=9_9999 => self.bytes_d5(v, x as u32),
                10_0000..=99_9999 => self.bytes_d6(v, x as u32),
                100_0000..=999_9999 => self.bytes_d7(v, x as u32),
                1000_0000..=9999_9999 => self.bytes_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.bytes_d1(v, z0),
                    10..=99 => self.bytes_d2(v, z0),
                    100..=999 => self.bytes_d3(v, z0),
                    1000..=9999 => self.bytes_d4(v, z0),
                    1_0000..=9_9999 => self.bytes_d5(v, z0),
                    10_0000..=99_9999 => self.bytes_d6(v, z0),
                    100_0000..=999_9999 => self.bytes_d7(v, z0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d8(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.bytes_d1(v, y0),
                    10..=99 => self.bytes_d2(v, y0),
                    100..=999 => self.bytes_d3(v, y0),
                    1000..=9999 => self.bytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d16(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn bytes_u128(&self, v: &mut Vec<u8>, x: u128) {
        invariant!(v.capacity() - v.len() >= 39);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.bytes_d1(v, x as u32),
                10..=99 => self.bytes_d2(v, x as u32),
                100..=999 => self.bytes_d3(v, x as u32),
                1000..=9999 => self.bytes_d4(v, x as u32),
                1_0000..=9_9999 => self.bytes_d5(v, x as u32),
                10_0000..=99_9999 => self.bytes_d6(v, x as u32),
                100_0000..=999_9999 => self.bytes_d7(v, x as u32),
                1000_0000..=9999_9999 => self.bytes_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.bytes_d1(v, z0),
                    10..=99 => self.bytes_d2(v, z0),
                    100..=999 => self.bytes_d3(v, z0),
                    1000..=9999 => self.bytes_d4(v, z0),
                    1_0000..=9_9999 => self.bytes_d5(v, z0),
                    10_0000..=99_9999 => self.bytes_d6(v, z0),
                    100_0000..=999_9999 => self.bytes_d7(v, z0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    (x % 1_0000_0000_0000_0000) as u64,
                );
                match y0 {
                    0..=9 => self.bytes_d1(v, y0),
                    10..=99 => self.bytes_d2(v, y0),
                    100..=999 => self.bytes_d3(v, y0),
                    1000..=9999 => self.bytes_d4(v, y0),
                    1_0000..=9_9999 => self.bytes_d5(v, y0),
                    10_0000..=99_9999 => self.bytes_d6(v, y0),
                    100_0000..=999_9999 => self.bytes_d7(v, y0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d16(v, y1);
            }
            1844_6744_0737_0955_1616..=9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u32;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.bytes_d1(v, y0),
                    10..=99 => self.bytes_d2(v, y0),
                    100..=999 => self.bytes_d3(v, y0),
                    1000..=9999 => self.bytes_d4(v, y0),
                    1_0000..=9_9999 => self.bytes_d5(v, y0),
                    10_0000..=99_9999 => self.bytes_d6(v, y0),
                    100_0000..=999_9999 => self.bytes_d7(v, y0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000..=9999_9999_9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u64;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                let (z0, z1) = ((y0 / 1_0000_0000) as u32, (y0 % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.bytes_d1(v, z0),
                    10..=99 => self.bytes_d2(v, z0),
                    100..=999 => self.bytes_d3(v, z0),
                    1000..=9999 => self.bytes_d4(v, z0),
                    1_0000..=9_9999 => self.bytes_d5(v, z0),
                    10_0000..=99_9999 => self.bytes_d6(v, z0),
                    100_0000..=999_9999 => self.bytes_d7(v, z0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d8(v, z1);
                self.bytes_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000_0000_0000
                ..=340_2823_6692_0938_4634_6337_4607_4317_6821_1455 => {
                let y0 = (x / 1_0000_0000_0000_0000_0000_0000_0000_0000) as u32;
                let y1 = x - (y0 as u128) * 1_0000_0000_0000_0000_0000_0000_0000_0000;
                let z0 = (y1 / 1_0000_0000_0000_0000) as u64;
                let z1 = (y1 - (z0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.bytes_d1(v, y0),
                    10..=99 => self.bytes_d2(v, y0),
                    100..=999 => self.bytes_d3(v, y0),
                    1000..=9999 => self.bytes_d4(v, y0),
                    1_0000..=9_9999 => self.bytes_d5(v, y0),
                    10_0000..=99_9999 => self.bytes_d6(v, y0),
                    100_0000..=999_9999 => self.bytes_d7(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d16(v, z0);
                self.bytes_d16(v, z1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn bytes_sp_u64(&self, v: &mut Vec<u8>, x: u64) {
        invariant!(v.capacity() - v.len() >= 21);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.bytes_d1sp(v, x as u32),
                10..=99 => self.bytes_d2sp(v, x as u32),
                100..=999 => self.bytes_d3sp(v, x as u32),
                1000..=9999 => self.bytes_d4sp(v, x as u32),
                1_0000..=9_9999 => self.bytes_d5sp(v, x as u32),
                10_0000..=99_9999 => self.bytes_d6sp(v, x as u32),
                100_0000..=999_9999 => self.bytes_d7sp(v, x as u32),
                1000_0000..=9999_9999 => self.bytes_d8sp(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.bytes_d1(v, z0),
                    10..=99 => self.bytes_d2(v, z0),
                    100..=999 => self.bytes_d3(v, z0),
                    1000..=9999 => self.bytes_d4(v, z0),
                    1_0000..=9_9999 => self.bytes_d5(v, z0),
                    10_0000..=99_9999 => self.bytes_d6(v, z0),
                    100_0000..=999_9999 => self.bytes_d7(v, z0),
                    1000_0000..=9999_9999 => self.bytes_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.bytes_d1(v, y0),
                    10..=99 => self.bytes_d2(v, y0),
                    100..=999 => self.bytes_d3(v, y0),
                    1000..=9999 => self.bytes_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.bytes_d16sp(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn str_u64(&self, v: &mut String, x: u64) {
        invariant!(v.capacity() - v.len() >= 20);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.str_d1(v, x as u32),
                10..=99 => self.str_d2(v, x as u32),
                100..=999 => self.str_d3(v, x as u32),
                1000..=9999 => self.str_d4(v, x as u32),
                1_0000..=9_9999 => self.str_d5(v, x as u32),
                10_0000..=99_9999 => self.str_d6(v, x as u32),
                100_0000..=999_9999 => self.str_d7(v, x as u32),
                1000_0000..=9999_9999 => self.str_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.str_d1(v, z0),
                    10..=99 => self.str_d2(v, z0),
                    100..=999 => self.str_d3(v, z0),
                    1000..=9999 => self.str_d4(v, z0),
                    1_0000..=9_9999 => self.str_d5(v, z0),
                    10_0000..=99_9999 => self.str_d6(v, z0),
                    100_0000..=999_9999 => self.str_d7(v, z0),
                    1000_0000..=9999_9999 => self.str_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    (x % 1_0000_0000_0000_0000) as u64,
                );
                match y0 {
                    0..=9 => self.str_d1(v, y0),
                    10..=99 => self.str_d2(v, y0),
                    100..=999 => self.str_d3(v, y0),
                    1000..=9999 => self.str_d4(v, y0),
                    1_0000..=9_9999 => self.str_d5(v, y0),
                    10_0000..=99_9999 => self.str_d6(v, y0),
                    100_0000..=999_9999 => self.str_d7(v, y0),
                    1000_0000..=9999_9999 => self.str_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d16(v, y1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn str_u128(&self, v: &mut String, x: u128) {
        invariant!(v.capacity() - v.len() >= 39);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.str_d1(v, x as u32),
                10..=99 => self.str_d2(v, x as u32),
                100..=999 => self.str_d3(v, x as u32),
                1000..=9999 => self.str_d4(v, x as u32),
                1_0000..=9_9999 => self.str_d5(v, x as u32),
                10_0000..=99_9999 => self.str_d6(v, x as u32),
                100_0000..=999_9999 => self.str_d7(v, x as u32),
                1000_0000..=9999_9999 => self.str_d8(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.str_d1(v, z0),
                    10..=99 => self.str_d2(v, z0),
                    100..=999 => self.str_d3(v, z0),
                    1000..=9999 => self.str_d4(v, z0),
                    1_0000..=9_9999 => self.str_d5(v, z0),
                    10_0000..=99_9999 => self.str_d6(v, z0),
                    100_0000..=999_9999 => self.str_d7(v, z0),
                    1000_0000..=9999_9999 => self.str_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    (x % 1_0000_0000_0000_0000) as u64,
                );
                match y0 {
                    0..=9 => self.str_d1(v, y0),
                    10..=99 => self.str_d2(v, y0),
                    100..=999 => self.str_d3(v, y0),
                    1000..=9999 => self.str_d4(v, y0),
                    1_0000..=9_9999 => self.str_d5(v, y0),
                    10_0000..=99_9999 => self.str_d6(v, y0),
                    100_0000..=999_9999 => self.str_d7(v, y0),
                    1000_0000..=9999_9999 => self.str_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d16(v, y1);
            }
            1844_6744_0737_0955_1616..=9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u32;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.str_d1(v, y0),
                    10..=99 => self.str_d2(v, y0),
                    100..=999 => self.str_d3(v, y0),
                    1000..=9999 => self.str_d4(v, y0),
                    1_0000..=9_9999 => self.str_d5(v, y0),
                    10_0000..=99_9999 => self.str_d6(v, y0),
                    100_0000..=999_9999 => self.str_d7(v, y0),
                    1000_0000..=9999_9999 => self.str_d8(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000..=9999_9999_9999_9999_9999_9999_9999_9999 => {
                let y0 = (x / 1_0000_0000_0000_0000) as u64;
                let y1 = (x - (y0 as u128) * 1_0000_0000_0000_0000) as u64;
                let (z0, z1) = ((y0 / 1_0000_0000) as u32, (y0 % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.str_d1(v, z0),
                    10..=99 => self.str_d2(v, z0),
                    100..=999 => self.str_d3(v, z0),
                    1000..=9999 => self.str_d4(v, z0),
                    1_0000..=9_9999 => self.str_d5(v, z0),
                    10_0000..=99_9999 => self.str_d6(v, z0),
                    100_0000..=999_9999 => self.str_d7(v, z0),
                    1000_0000..=9999_9999 => self.str_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d8(v, z1);
                self.str_d16(v, y1);
            }
            1_0000_0000_0000_0000_0000_0000_0000_0000
                ..=340_2823_6692_0938_4634_6337_4607_4317_6821_1455 => {
                let y0 = (x / 1_0000_0000_0000_0000_0000_0000_0000_0000) as u32;
                let y1 = x - (y0 as u128) * 1_0000_0000_0000_0000_0000_0000_0000_0000;
                let z0 = (y1 / 1_0000_0000_0000_0000) as u64;
                let z1 = (y1 - (z0 as u128) * 1_0000_0000_0000_0000) as u64;
                match y0 {
                    0..=9 => self.str_d1(v, y0),
                    10..=99 => self.str_d2(v, y0),
                    100..=999 => self.str_d3(v, y0),
                    1000..=9999 => self.str_d4(v, y0),
                    1_0000..=9_9999 => self.str_d5(v, y0),
                    10_0000..=99_9999 => self.str_d6(v, y0),
                    100_0000..=999_9999 => self.str_d7(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d16(v, z0);
                self.str_d16(v, z1);
            }
        }
    }
    #[inline(always)]
    pub unsafe fn str_sp_u64(&self, v: &mut String, x: u64) {
        invariant!(v.capacity() - v.len() >= 20);
        match x {
            0..=9999_9999 => match x {
                0..=9 => self.str_d1sp(v, x as u32),
                10..=99 => self.str_d2sp(v, x as u32),
                100..=999 => self.str_d3sp(v, x as u32),
                1000..=9999 => self.str_d4sp(v, x as u32),
                1_0000..=9_9999 => self.str_d5sp(v, x as u32),
                10_0000..=99_9999 => self.str_d6sp(v, x as u32),
                100_0000..=999_9999 => self.str_d7sp(v, x as u32),
                1000_0000..=9999_9999 => self.str_d8sp(v, x as u32),
                _ => core::hint::unreachable_unchecked(),
            },
            1_0000_0000..=9999_9999_9999_9999 => {
                let (z0, z1) = ((x / 1_0000_0000) as u32, (x % 1_0000_0000) as u32);
                match z0 {
                    0..=9 => self.str_d1(v, z0),
                    10..=99 => self.str_d2(v, z0),
                    100..=999 => self.str_d3(v, z0),
                    1000..=9999 => self.str_d4(v, z0),
                    1_0000..=9_9999 => self.str_d5(v, z0),
                    10_0000..=99_9999 => self.str_d6(v, z0),
                    100_0000..=999_9999 => self.str_d7(v, z0),
                    1000_0000..=9999_9999 => self.str_d8(v, z0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d8sp(v, z1);
            }
            1_0000_0000_0000_0000..=1844_6744_0737_0955_1615 => {
                let (y0, y1) = (
                    (x / 1_0000_0000_0000_0000) as u32,
                    x % 1_0000_0000_0000_0000,
                );
                match y0 {
                    0..=9 => self.str_d1(v, y0),
                    10..=99 => self.str_d2(v, y0),
                    100..=999 => self.str_d3(v, y0),
                    1000..=9999 => self.str_d4(v, y0),
                    _ => core::hint::unreachable_unchecked(),
                }
                self.str_d16sp(v, y1);
            }
        }
    }
}
