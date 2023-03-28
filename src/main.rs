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
            acc.push(' ');
            acc
        })
}

pub fn fold_by_to_string_with_capacity(values: &[usize]) -> String {
    values
        .iter()
        .map(|s| s.to_string())
        // 数値一つが最大6桁 + separator1文字で7文字
        .fold(String::with_capacity(7 * values.len()), |mut acc, cur| {
            acc.push_str(&cur);
            acc.push(' ');
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
        // 数値一つが最大6桁 + separator1文字で7文字
        .fold(String::with_capacity(7 * values.len()), |mut acc, cur| {
            write!(&mut acc, "{} ", cur).unwrap();
            acc
        })
}

const DIGIT4: [u8; 40000] = gen_digit4();
const fn gen_digit4() -> [u8; 40000] {
    let (mut d4, mut i) = ([0u8; 40000], 0);
    // const fn while: Rust 1.46.0 or later
    while i < 1_0000 {
        d4[i * 4] = b'0' + ((i / 100) / 10) as u8;
        d4[i * 4 + 1] = b'0' + ((i / 100) % 10) as u8;
        d4[i * 4 + 2] = b'0' + ((i % 100) / 10) as u8;
        d4[i * 4 + 3] = b'0' + ((i % 100) % 10) as u8;
        i += 1;
    }
    d4
}
unsafe fn dappend(v: &mut String, x: usize) {
    use std::str::from_utf8_unchecked;
    match x {
        0..=9 => v.push_str(from_utf8_unchecked(&(&DIGIT4[(x * 4 + 3)..])[..1])),
        10..=99 => v.push_str(from_utf8_unchecked(&(&DIGIT4[(x * 4 + 2)..])[..2])),
        100..=999 => v.push_str(from_utf8_unchecked(&(&DIGIT4[(x * 4 + 1)..])[..3])),
        1000..=9999 => v.push_str(from_utf8_unchecked(&(&DIGIT4[(x * 4)..])[..4])),
        1_0000..=9_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4 + 3)..])[..1]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
        10_0000..=99_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4 + 2)..])[..2]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
        100_0000..=999_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4 + 1)..])[..3]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
        1000_0000..=9999_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4)..])[..4]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
        _ => {
            let (z0, z1) = (x / 1_0000_0000, x % 1_0000_0000);
            let (y0, y1) = (z1 / 1_0000, z1 % 1_0000);
            dappend(v, z0);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4)..])[..4]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
    }
}

pub fn digit4_with_capacity(values: &[usize]) -> String {
    let mut acc = values
        .iter()
        .fold(String::with_capacity(7 * values.len()), |mut acc, &cur| {
            unsafe { dappend(&mut acc, cur) };
            acc.push(' ');
            acc
        });
    acc.pop();
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let arr = (0..1000000).collect::<Vec<_>>();

        let results = [
            to_string_and_join(&arr),
            fold_by_to_string_without_capacity(&arr),
            fold_by_to_string_with_capacity(&arr),
            itertools_join(&arr),
            fold_by_write_without_capacity(&arr),
            fold_by_write_with_capacity(&arr),
            digit4_with_capacity(&arr),
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
