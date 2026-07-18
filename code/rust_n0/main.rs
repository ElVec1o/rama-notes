// Compute v2(N0(n)) for odd n via the factorization  N0 = Σ_v per(A_v)·per(B_v)
// (A_v: even-positions × odd-values∖{v},  B_v: odd-positions × even-values∪{v}).
// This replaces a 2^n permanent by ~ (n+1)/2 permanents of size ~ n/2.
// If v2(a)=v2(N0) (the verified w=0-dominance mechanism), this tests the deficit
// conjecture  v2(a(2^k+1)) = 2^k - 2k + 3.  All arithmetic mod 2^128 (u128 wrapping).
//
// Build & run:   rustc -O code/rust_n0/main.rs -o /tmp/n0 && /tmp/n0
// (uses all cores; interim per-v results printed so partial progress is visible)

use std::thread;
use std::time::Instant;

fn odd(mut x: u128) -> u128 { while x & 1 == 0 { x >>= 1; } x }
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }
fn v2(x: u128) -> u32 { if x == 0 { 128 } else { x.trailing_zeros() } }

// Gray-code Ryser, mod 2^128.  per = (-1)^n Σ_S (-1)^{|S|} ∏_i rowsum_i(S).
fn permanent_mod(mat: &[Vec<u128>]) -> u128 {
    let n = mat.len();
    if n == 0 { return 1; }
    let mut row = vec![0u128; n];
    let mut acc = 0u128;
    let mut gray: u64 = 0;
    let total: u64 = 1u64 << n;
    for k in 1..total {
        let g = k ^ (k >> 1);
        let j = (g ^ gray).trailing_zeros() as usize;
        if (g >> j) & 1 == 1 {
            for i in 0..n { row[i] = row[i].wrapping_add(mat[i][j]); }
        } else {
            for i in 0..n { row[i] = row[i].wrapping_sub(mat[i][j]); }
        }
        gray = g;
        let mut prod: u128 = 1;
        for i in 0..n { prod = prod.wrapping_mul(row[i]); }
        if g.count_ones() & 1 == 0 { acc = acc.wrapping_add(prod); }
        else { acc = acc.wrapping_sub(prod); }
    }
    if n & 1 == 1 { acc.wrapping_neg() } else { acc }
}

fn n0(n: usize, nthreads: usize) -> u128 {
    let epos: Vec<u128> = (1..=n as u128).filter(|x| x % 2 == 0).collect();
    let opos: Vec<u128> = (1..=n as u128).filter(|x| x % 2 == 1).collect();
    let oddvals = opos.clone();
    let evenvals = epos.clone();
    let vs = oddvals.clone();
    let nv = vs.len();
    let chunk = (nv + nthreads - 1) / nthreads;
    let mut handles = Vec::new();
    for t in 0..nthreads {
        let vs = vs.clone(); let epos = epos.clone(); let opos = opos.clone();
        let oddvals = oddvals.clone(); let evenvals = evenvals.clone();
        let lo = t * chunk; let hi = ((t + 1) * chunk).min(nv);
        if lo >= hi { continue; }
        handles.push(thread::spawn(move || {
            let mut partial: u128 = 0;
            for vi in lo..hi {
                let v = vs[vi];
                let ov: Vec<u128> = oddvals.iter().cloned().filter(|&j| j != v).collect();
                let a: Vec<Vec<u128>> = epos.iter()
                    .map(|&i| ov.iter().map(|&j| gcd(odd(i), odd(j))).collect()).collect();
                let mut bcols = evenvals.clone(); bcols.push(v);
                let b: Vec<Vec<u128>> = opos.iter()
                    .map(|&i| bcols.iter().map(|&j| gcd(odd(i), odd(j))).collect()).collect();
                let prod = permanent_mod(&a).wrapping_mul(permanent_mod(&b));
                partial = partial.wrapping_add(prod);
                eprintln!("  [n={}] v={:>3} done (v2 of this term = {})", n, v, v2(prod));
            }
            partial
        }));
    }
    let mut total: u128 = 0;
    for h in handles { total = total.wrapping_add(h.join().unwrap()); }
    total
}

fn s2(mut x: u64) -> u64 { let mut s = 0; while x > 0 { s += x & 1; x >>= 1; } s }

fn main() {
    let nthreads = thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    eprintln!("using {} threads", nthreads);
    // Sweep odd n = 35..65 (ascending: cheap first).  D = v2(n!) - v2(N0) = deficit.
    // If v2(a)=v2(N0) (mechanism), this is the deficit.  n=65 tests k=6: predicted v2=55, D=8.
    let mut n = 35usize;
    while n <= 65 {
        let start = Instant::now();
        let val = n0(n, nthreads);
        let vn = v2(val) as i64;
        let vfac = n as i64 - s2(n as u64) as i64;   // v2(n!) = n - s2(n)
        let is_peak = (n - 1) & (n - 2) == 0;         // n = 2^k+1 ?
        let tag = if is_peak {
            let k = (n - 1).trailing_zeros() as i64;
            format!("  [2^k+1, k={}, predicted v2=2^k-2k+3={}]", k, (1i64 << k) - 2 * k + 3)
        } else { String::new() };
        println!("n={:>3}  v2(N0)={:>3}  v2(n!)={:>3}  D={:>2}{}   ({:?})",
                 n, vn, vfac, vfac - vn, tag, start.elapsed());
        n += 2;
    }
}
