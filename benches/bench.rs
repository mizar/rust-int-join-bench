use bencher::{benchmark_group, benchmark_main, Bencher};
use itertools::Itertools;
use once_cell::sync::Lazy;
use rand::Rng;
use std::io;
use std::io::Write;

const N: usize = 100000;

static VALUES: Lazy<Vec<usize>> = Lazy::new(|| {
    let mut rng = rand::thread_rng();

    (0..N).map(|_| rng.gen_range(0..1000000)).collect()
});

fn itertools_join(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        eprintln!("{}", values.iter().join(" "));
    })
}

#[allow(unused)]
fn itertools_format(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        eprintln!("{}", values.iter().format(" "));
    })
}

#[allow(unused)]
fn foreach_print(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        values.iter().for_each(|x| {
            eprint!("{} ", x);
        });
        eprintln!();
    })
}

fn itertools_join_with_bufwriter(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::BufWriter::new(io::stderr().lock());
        writeln!(stderr, "{}", values.iter().join(" ")).unwrap();
    })
}

fn itertools_format_with_bufwriter(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::BufWriter::new(io::stderr().lock());
        writeln!(stderr, "{}", values.iter().format(" ")).unwrap();
    })
}

fn foreach_print_with_bufwriter(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::BufWriter::new(io::stderr().lock());
        values.iter().for_each(|x| {
            write!(stderr, "{} ", x).unwrap();
        });
        writeln!(stderr).unwrap();
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
unsafe fn dappend_bytes(v: &mut Vec<u8>, x: usize) {
    match x {
        0..=9 => v.extend_from_slice(&(&DIGIT4[(x * 4 + 3)..])[..1]),
        10..=99 => v.extend_from_slice(&(&DIGIT4[(x * 4 + 2)..])[..2]),
        100..=999 => v.extend_from_slice(&(&DIGIT4[(x * 4 + 1)..])[..3]),
        1000..=9999 => v.extend_from_slice(&(&DIGIT4[(x * 4)..])[..4]),
        1_0000..=9_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.extend_from_slice(&(&DIGIT4[(y0 * 4 + 3)..])[..1]);
            v.extend_from_slice(&(&DIGIT4[(y1 * 4)..])[..4]);
        }
        10_0000..=99_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.extend_from_slice(&(&DIGIT4[(y0 * 4 + 2)..])[..2]);
            v.extend_from_slice(&(&DIGIT4[(y1 * 4)..])[..4]);
        }
        100_0000..=999_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.extend_from_slice(&(&DIGIT4[(y0 * 4 + 1)..])[..3]);
            v.extend_from_slice(&(&DIGIT4[(y1 * 4)..])[..4]);
        }
        1000_0000..=9999_9999 => {
            let (y0, y1) = (x / 1_0000, x % 1_0000);
            v.extend_from_slice(&(&DIGIT4[(y0 * 4)..])[..4]);
            v.extend_from_slice(&(&DIGIT4[(y1 * 4)..])[..4]);
        }
        _ => {
            let (z0, z1) = (x / 1_0000_0000, x % 1_0000_0000);
            let (y0, y1) = (z1 / 1_0000, z1 % 1_0000);
            dappend_bytes(v, z0);
            v.extend_from_slice(&(&DIGIT4[(y0 * 4)..])[..4]);
            v.extend_from_slice(&(&DIGIT4[(y1 * 4)..])[..4]);
        }
    }
}
unsafe fn dappend_str(v: &mut String, x: usize) {
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
            dappend_str(v, z0);
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y0 * 4)..])[..4]));
            v.push_str(from_utf8_unchecked(&(&DIGIT4[(y1 * 4)..])[..4]));
        }
    }
}

fn digit4_bytes(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::stderr();
        let mut buf = values.iter().fold(Vec::<u8>::new(), |mut acc, &cur| {
            unsafe { dappend_bytes(&mut acc, cur) };
            acc.push(b' ');
            acc
        });
        buf.pop();
        buf.push(b'\n');
        stderr.write_all(&buf).unwrap();
    })
}

fn digit4_str(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::stderr();
        writeln!(
            stderr,
            "{}",
            values
                .iter()
                .fold(String::new(), |mut acc, &cur| {
                    unsafe { dappend_str(&mut acc, cur) };
                    acc.push(' ');
                    acc
                })
                .trim_end()
        )
        .unwrap();
    })
}

fn digit4_str_with_bufwriter(bench: &mut Bencher) {
    let values = &*VALUES;
    bench.iter(|| {
        let mut stderr = io::BufWriter::new(io::stderr().lock());
        writeln!(
            stderr,
            "{}",
            values
                .iter()
                .fold(String::with_capacity(7 * values.len()), |mut acc, &cur| {
                    unsafe { dappend_str(&mut acc, cur) };
                    acc.push(' ');
                    acc
                })
                .trim_end()
        )
        .unwrap();
    })
}

benchmark_group!(
    benches,
    itertools_join,
    //itertools_format,
    //foreach_print,
    itertools_join_with_bufwriter,
    itertools_format_with_bufwriter,
    foreach_print_with_bufwriter,
    digit4_bytes,
    digit4_str,
    digit4_str_with_bufwriter,
);
benchmark_main!(benches);
