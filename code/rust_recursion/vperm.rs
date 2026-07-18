// v2(a(2^k+1)) via the zeroed even-even block:  v2(a) = v2(per M')  for k>=3,
// where M' = G(2^k+1) with the even x even block set to 0.
//
// Since gcd is symmetric, the two cofactor families coincide (Q = R^T), and per M'
// collapses to a QUADRATIC FORM in m+1 = 2^{k-1}+1 permanents of size m:
//
//   per M' = u^T P u = sum_{i,j} P[i][j] * u_i * u_j
//   u_i    = per(R with column i deleted)   (i = 0..=m),  R[a][b] = gcd(a+1, odd_b)  (m x (m+1))
//   P[i][j]= gcd(odd_i, odd_j),   odd_t = 2t+1
//
// We only need v2(per M'); predicted value is 2^k-2k+3 (=55 at k=6) < 64, so work mod 2^64
// with native wrapping arithmetic. If the printed v2 is 64 the residue vanished mod 2^64
// (true v2 >= 64) and a wider modulus is needed.
//
// Usage:  vperm <k>   (k>=3).

use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 { let t = a % b; a = b; b = t; }
    a
}

// Ryser permanent of an s x s matrix (row-major), mod 2^64 (wrapping).
fn perm_mod(mat: &[u64], s: usize) -> u64 {
    if s == 0 { return 1; }
    if s == 1 { return mat[0]; }
    let mut rowsum = vec![0u64; s];
    let mut res: u64 = 0;
    let mut prev: u64 = 0;
    let total: u64 = 1u64 << s;
    for x in 1u64..total {
        let g = x ^ (x >> 1);
        let j = (g ^ prev).trailing_zeros() as usize;
        if (g >> j) & 1 == 1 {
            for i in 0..s { rowsum[i] = rowsum[i].wrapping_add(mat[i * s + j]); }
        } else {
            for i in 0..s { rowsum[i] = rowsum[i].wrapping_sub(mat[i * s + j]); }
        }
        prev = g;
        // 4-way ILP accumulators to break the serial multiply latency chain
        let mut p0: u64 = 1; let mut p1: u64 = 1; let mut p2: u64 = 1; let mut p3: u64 = 1;
        let mut i = 0usize;
        while i + 4 <= s {
            p0 = p0.wrapping_mul(rowsum[i]);
            p1 = p1.wrapping_mul(rowsum[i + 1]);
            p2 = p2.wrapping_mul(rowsum[i + 2]);
            p3 = p3.wrapping_mul(rowsum[i + 3]);
            i += 4;
        }
        while i < s { p0 = p0.wrapping_mul(rowsum[i]); i += 1; }
        let prod = p0.wrapping_mul(p1).wrapping_mul(p2).wrapping_mul(p3);
        if (s as u32 - g.count_ones()) & 1 == 0 {
            res = res.wrapping_add(prod);
        } else {
            res = res.wrapping_sub(prod);
        }
    }
    res
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(6);
    assert!(k >= 3, "need k>=3");
    let m: usize = 1usize << (k - 1);
    let n: usize = (1usize << k) + 1;
    let nthreads: usize = std::env::var("NTHREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(10);
    rayon::ThreadPoolBuilder::new().num_threads(nthreads).build_global().ok();
    eprintln!("k={k} n={n} m={m}: m+1={} permanents of size {m}, threads={}",
              m + 1, rayon::current_num_threads());

    let oddidx: Vec<u64> = (0..=m).map(|i| (2 * i + 1) as u64).collect(); // 1,3,...,2m+1
    // R[a][b] = gcd(a+1, odd_b),  a = 0..m-1, b = 0..m   (m x (m+1))
    let r_mat: Vec<Vec<u64>> = (0..m)
        .map(|a| (0..=m).map(|b| gcd((a + 1) as u64, oddidx[b])).collect())
        .collect();
    // P[i][j] = gcd(odd_i, odd_j)
    let p_mat: Vec<Vec<u64>> = (0..=m)
        .map(|i| (0..=m).map(|j| gcd(oddidx[i], oddidx[j])).collect())
        .collect();

    let done = AtomicUsize::new(0);
    let tot = m + 1;
    let start = Instant::now();

    // u_i = per(R with column i deleted), size m x m
    let u: Vec<u64> = (0..=m).into_par_iter().map(|i| {
        let mut flat = Vec::with_capacity(m * m);
        for a in 0..m {
            for b in 0..=m {
                if b == i { continue; }
                flat.push(r_mat[a][b]);
            }
        }
        let v = perm_mod(&flat, m);
        let d = done.fetch_add(1, Ordering::Relaxed) + 1;
        let el = start.elapsed().as_secs_f64();
        let eta = el / (d as f64) * (tot as f64) - el;
        eprintln!("  [{d}/{tot}] u[{i}] done  elapsed {el:.0}s  eta {eta:.0}s", );
        v
    }).collect();

    // per M' = sum_{i,j} P[i][j] * u_i * u_j  (mod 2^64)
    let mut result: u64 = 0;
    for i in 0..=m {
        for j in 0..=m {
            result = result.wrapping_add(p_mat[i][j].wrapping_mul(u[i]).wrapping_mul(u[j]));
        }
    }

    let v = result.trailing_zeros();
    let pred = (1u64 << k) - (2 * k as u64) + 3;
    println!("k={k} n={n}: v2(per M') = {v}   (residue mod 2^64 = {result})");
    println!("  closed-form prediction v2(a) = 2^k-2k+3 = {pred}   MATCH: {}", v as u64 == pred);
    println!("  deficit D = v2(n!)-v2(a) = {} - {} = {}", (1u64<<k)-1, v, ((1u64<<k)-1).wrapping_sub(v as u64));
    if v >= 64 { println!("  WARNING: residue vanished mod 2^64; rerun with wider modulus"); }
    println!("  elapsed {:.1}s", start.elapsed().as_secs_f64());
}
