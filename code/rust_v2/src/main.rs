// Extend v2(a(n)) for a(n) = per[gcd(i,j)]_{1..n}  past n=32, to test the c=1 question:
//   is  v2(a(n)) - v2(n!)  bounded  (<=> v2(a(n)) ~ v2(n!) ~ n, i.e. growth constant c=1) ?
//   and does the proved linear bound  v2(a(n)) >= v2(ceil(n/2)!)  hold with room to spare?
//
// Method: Gray-code Ryser permanent mod 2^128 (u128 wrapping = arithmetic mod 2^128).
//   a(n) mod 2^128 pins the low 128 bits, so v2(a(n)) = trailing_zeros  (valid since
//   v2(a(n)) ~ n < 128 for all n we run).  Cost O(n * 2^n); progress + ETA + interim save.
//
// Run:   cd code/rust_v2 && cargo run --release -- 21 34
//        (args = START END inclusive; default 21 34.  Bump END to 36/38 for more, slower.)

use std::env;
use std::fs::OpenOptions;
use std::io::Write;
use std::time::Instant;

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a
}

// v2(m!) = m - popcount(m)   (Legendre, p=2)
fn v2_factorial(m: u64) -> u32 { (m - m.count_ones() as u64) as u32 }

fn permanent_mod_pow2(n: usize, report_every: u64, t0: Instant) -> u128 {
    // G[i][j] = gcd(i+1, j+1) as u128
    let mut g = vec![vec![0u128; n]; n];
    for i in 0..n { for j in 0..n { g[i][j] = gcd((i + 1) as u128, (j + 1) as u128); } }

    let mut row = vec![0u128; n];       // row[i] = sum_{j in S} G[i][j]
    let mut total: u128 = 0;            // sum_S (-1)^|S| prod_i row[i]
    let end: u64 = 1u64 << n;
    let mut next_report: u64 = report_every;

    for k in 1..end {
        let gray = k ^ (k >> 1);
        let prev = (k - 1) ^ ((k - 1) >> 1);
        let bit = gray ^ prev;          // exactly one bit changed
        let j = bit.trailing_zeros() as usize;
        if gray & bit != 0 {
            for i in 0..n { row[i] = row[i].wrapping_add(g[i][j]); }
        } else {
            for i in 0..n { row[i] = row[i].wrapping_sub(g[i][j]); }
        }
        let mut prod: u128 = 1;
        for i in 0..n { prod = prod.wrapping_mul(row[i]); }
        if gray.count_ones() & 1 == 1 { total = total.wrapping_sub(prod); }
        else { total = total.wrapping_add(prod); }

        if k >= next_report {
            let frac = k as f64 / end as f64;
            let el = t0.elapsed().as_secs_f64();
            let eta = if frac > 0.0 { el / frac - el } else { 0.0 };
            eprint!("\r  n={:2}  {:5.1}%   elapsed {:6.1}s   ETA {:6.1}s   ", n, frac * 100.0, el, eta);
            let _ = std::io::stderr().flush();
            next_report += report_every;
        }
    }
    eprintln!("\r  n={:2}  100.0%   done in {:6.1}s                         ", n, t0.elapsed().as_secs_f64());
    if n & 1 == 1 { total = total.wrapping_neg(); }   // per = (-1)^n * total
    total
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let start: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(21);
    let end: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(34);

    let outpath = "../v2_ryser_out.txt";
    println!("Extending v2(a(n)) for n = {}..={}  (Gray-code Ryser mod 2^128)", start, end);
    println!("{:>3} {:>8} {:>8} {:>10} {:>14} {:>16}",
             "n", "v2(a)", "v2(n!)", "v2(cn2!)", "v2(a)-v2(n!)", "v2(a)-v2(cn2!)");
    // (re)start the interim file with a header
    {
        let mut f = OpenOptions::new().create(true).write(true).truncate(true).open(outpath).unwrap();
        writeln!(f, "# n  v2(a)  v2(n!)  v2(ceil(n/2)!)  v2(a)-v2(n!)  v2(a)-v2(ceil(n/2)!)  a(n)mod2^128").unwrap();
    }

    for n in start..=end {
        let t0 = Instant::now();
        let report_every: u64 = 1u64 << (if n >= 26 { n - 6 } else { 20.min(n as u32).max(1) as usize });
        let perm = permanent_mod_pow2(n, report_every, t0);
        let v2a = if perm == 0 { 999 } else { perm.trailing_zeros() };
        let m = ((n + 1) / 2) as u64;
        let v2f = v2_factorial(n as u64);
        let v2c = v2_factorial(m);
        let d1 = v2a as i64 - v2f as i64;
        let d2 = v2a as i64 - v2c as i64;
        println!("{:>3} {:>8} {:>8} {:>10} {:>14} {:>16}", n, v2a, v2f, v2c, d1, d2);
        // interim save (append) so a long run is never lost
        let mut f = OpenOptions::new().append(true).open(outpath).unwrap();
        writeln!(f, "{} {} {} {} {} {} {}", n, v2a, v2f, v2c, d1, d2, perm).unwrap();
    }
    println!("\nInterim results saved to code/v2_ryser_out.txt");
    println!("KEY CHECKS:  (a) v2(a)-v2(n!) should stay bounded (was in [-5,1] to n=32) => supports c=1;");
    println!("             (b) v2(a)-v2(ceil(n/2)!) should stay >= 0 (the proved linear bound).");
}
