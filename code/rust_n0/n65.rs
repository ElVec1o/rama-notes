// Compute v2(N0(65)) — the k=6 test of the deficit conjecture (predicted v2=55, D=8).
// N0(n) = Σ_v per(A_v)·per(B_v);  A_v: even-pos × odd-vals∖{v} (32×32), B_v: odd-pos × even-vals∪{v} (33×33).
// Parallel over the 33 values v; mod 2^128; progress + ETA + interim save.
//
// ONE-LINER:
//   rustc -O ~/Documents/elvec1o/RAMA-NOTEBOOK/code/rust_n0/n65.rs -o /tmp/n65 && /tmp/n65
//
// It first verifies n=33 (instant, must print v2=25 MATCH), then computes n=65 (~minutes–1h on
// a multicore box).  Interim per-v results are appended to /tmp/n0_partial.txt.  Paste the final
// line ("n= 65  v2(N0)= ...") back.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use std::thread;
use std::io::Write;

fn odd(mut x: u128) -> u128 { while x & 1 == 0 { x >>= 1; } x }
fn gcd(a: u128, b: u128) -> u128 { if b == 0 { a } else { gcd(b, a % b) } }
fn v2(x: u128) -> u32 { if x == 0 { 128 } else { x.trailing_zeros() } }

fn permanent_mod(mat: &[Vec<u128>]) -> u128 {
    let n = mat.len();
    if n == 0 { return 1; }
    let mut row = vec![0u128; n];
    let mut acc = 0u128;
    let mut gray: u64 = 0;
    for k in 1..(1u64 << n) {
        let g = k ^ (k >> 1);
        let j = (g ^ gray).trailing_zeros() as usize;
        if (g >> j) & 1 == 1 { for i in 0..n { row[i] = row[i].wrapping_add(mat[i][j]); } }
        else { for i in 0..n { row[i] = row[i].wrapping_sub(mat[i][j]); } }
        gray = g;
        let mut prod: u128 = 1;
        for i in 0..n { prod = prod.wrapping_mul(row[i]); }
        if g.count_ones() & 1 == 0 { acc = acc.wrapping_add(prod); } else { acc = acc.wrapping_sub(prod); }
    }
    if n & 1 == 1 { acc.wrapping_neg() } else { acc }
}

fn n0(n: usize, nthreads: usize, verbose: bool) -> u128 {
    let epos: Vec<u128> = (1..=n as u128).filter(|x| x % 2 == 0).collect();
    let opos: Vec<u128> = (1..=n as u128).filter(|x| x % 2 == 1).collect();
    let oddvals = opos.clone();
    let evenvals = epos.clone();
    let vs = oddvals.clone();
    let nv = vs.len();
    let done = Arc::new(AtomicUsize::new(0));
    let start = Instant::now();
    let save = Arc::new(Mutex::new(
        std::fs::OpenOptions::new().create(true).append(true).open("/tmp/n0_partial.txt").ok()));
    let chunk = (nv + nthreads - 1) / nthreads;
    let mut handles = Vec::new();
    for t in 0..nthreads {
        let (vs, epos, opos, oddvals, evenvals) =
            (vs.clone(), epos.clone(), opos.clone(), oddvals.clone(), evenvals.clone());
        let (done, save) = (done.clone(), save.clone());
        let lo = t * chunk; let hi = ((t + 1) * chunk).min(nv);
        if lo >= hi { continue; }
        handles.push(thread::spawn(move || {
            let mut partial: u128 = 0;
            for vi in lo..hi {
                let v = vs[vi];
                let ov: Vec<u128> = oddvals.iter().cloned().filter(|&j| j != v).collect();
                let a: Vec<Vec<u128>> = epos.iter().map(|&i| ov.iter().map(|&j| gcd(odd(i), odd(j))).collect()).collect();
                let mut bcols = evenvals.clone(); bcols.push(v);
                let b: Vec<Vec<u128>> = opos.iter().map(|&i| bcols.iter().map(|&j| gcd(odd(i), odd(j))).collect()).collect();
                let prod = permanent_mod(&a).wrapping_mul(permanent_mod(&b));
                partial = partial.wrapping_add(prod);
                let c = done.fetch_add(1, Ordering::SeqCst) + 1;
                if verbose {
                    let el = start.elapsed().as_secs_f64();
                    let eta = el / (c as f64) * ((nv - c) as f64);
                    eprintln!("  [n={}] v={:>3} done  ({}/{})  elapsed {:.0}s  ETA {:.0}s", n, v, c, nv, el, eta);
                }
                if let Ok(mut g) = save.lock() { if let Some(f) = g.as_mut() {
                    let _ = writeln!(f, "n={} v={} prod_hi={:x} prod_lo={:x}", n, v, (prod >> 64) as u64, prod as u64);
                }}
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
    // sanity: n=33 must be 25
    let v33 = v2(n0(33, nthreads, false));
    println!("n= 33  v2(N0)={:>3}   (must be 25: {})", v33, if v33 == 25 { "OK ✓" } else { "FAIL ✗" });
    // the target
    let start = Instant::now();
    let val = n0(65, nthreads, true);
    let vn = v2(val) as i64;
    let d = (65 - s2(65)) as i64 - vn;
    println!("n= 65  v2(N0)={:>3}   predicted 55   deficit D={:>2}   [{}]   ({:?})",
             vn, d, if vn == 55 { "MATCH — D=8 confirmed!" } else { "DIFFERS from conjecture" }, start.elapsed());
}
