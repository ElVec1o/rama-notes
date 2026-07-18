// FAST v2(N0(65)) — the k=6 deficit test (predicted v2=55, D=8).
// Optimizations vs the naive version:
//   (a) mod 2^64 (u64): safe since v2 predicted 55 < 64 (sanity-checked on n=33 → must be 25).
//   (b) cofactor trick: per B_v = Σ_r gcd(r,v)·C_r with C_r fixed, so everything is 66 size-32
//       permanents (33 A_v + 33 C_r) instead of 33 size-32 + 33 size-33.  ~3-4x faster overall.
// Parallel over the 66 permanents; progress + ETA; interim save to /tmp/n0_partial.txt.
//
// ONE-LINER:
//   rustc -O ~/Documents/elvec1o/RAMA-NOTEBOOK/code/rust_n0/n65fast.rs -o /tmp/n65f && /tmp/n65f
//
// Prints n=33 sanity (must be 25), then n=65.  Paste back the final "n= 65 ..." line.
// (If it reports v2 >= 60, tell me — I'll give a u128 version to rule out overflow.)

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use std::thread;
use std::io::Write;

fn odd(mut x: u64) -> u64 { while x & 1 == 0 { x >>= 1; } x }
fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn v2(x: u64) -> u32 { if x == 0 { 64 } else { x.trailing_zeros() } }

fn per64(mat: &[Vec<u64>]) -> u64 {
    let n = mat.len();
    if n == 0 { return 1; }
    let mut row = vec![0u64; n];
    let mut acc = 0u64;
    let mut gray: u64 = 0;
    for k in 1..(1u64 << n) {
        let g = k ^ (k >> 1);
        let j = (g ^ gray).trailing_zeros() as usize;
        if (g >> j) & 1 == 1 { for i in 0..n { row[i] = row[i].wrapping_add(mat[i][j]); } }
        else { for i in 0..n { row[i] = row[i].wrapping_sub(mat[i][j]); } }
        gray = g;
        let mut prod: u64 = 1;
        for i in 0..n { prod = prod.wrapping_mul(row[i]); }
        if g.count_ones() & 1 == 0 { acc = acc.wrapping_add(prod); } else { acc = acc.wrapping_sub(prod); }
    }
    if n & 1 == 1 { acc.wrapping_neg() } else { acc }
}

fn n0_fast(n: usize, nthreads: usize, verbose: bool) -> u64 {
    let epos: Vec<u64> = (1..=n as u64).filter(|x| x % 2 == 0).collect();     // even positions (rows of A)
    let opos: Vec<u64> = (1..=n as u64).filter(|x| x % 2 == 1).collect();     // odd positions (rows of C)
    let oddvals = opos.clone();                                               // odd values (cols of A / index v)
    let evenparts: Vec<u64> = epos.iter().map(|&x| odd(x)).collect();         // odd parts of even values (cols of C)
    let nv = oddvals.len();                                                   // = |odd positions| too

    // 66 jobs: job idx 0..nv-1 = A_v (v=oddvals[idx]);  idx nv..2nv-1 = C_r (r=opos[idx-nv]).
    let njobs = 2 * nv;
    let results: Arc<Mutex<Vec<u64>>> = Arc::new(Mutex::new(vec![0u64; njobs]));
    let done = Arc::new(AtomicUsize::new(0));
    let start = Instant::now();
    let save = Arc::new(Mutex::new(
        std::fs::OpenOptions::new().create(true).append(true).open("/tmp/n0_partial.txt").ok()));
    let chunk = (njobs + nthreads - 1) / nthreads;
    let mut handles = Vec::new();
    for t in 0..nthreads {
        let (epos, opos, oddvals, evenparts) = (epos.clone(), opos.clone(), oddvals.clone(), evenparts.clone());
        let (results, done, save) = (results.clone(), done.clone(), save.clone());
        let lo = t * chunk; let hi = ((t + 1) * chunk).min(njobs);
        if lo >= hi { continue; }
        handles.push(thread::spawn(move || {
            for job in lo..hi {
                let val = if job < nv {
                    // A_v : even-positions × (odd-values ∖ {v})
                    let v = oddvals[job];
                    let cols: Vec<u64> = oddvals.iter().cloned().filter(|&j| j != v).collect();
                    let m: Vec<Vec<u64>> = epos.iter().map(|&i| cols.iter().map(|&j| gcd(odd(i), j)).collect()).collect();
                    per64(&m)
                } else {
                    // C_r : (odd-positions ∖ {r}) × even-value-odd-parts
                    let r = opos[job - nv];
                    let m: Vec<Vec<u64>> = opos.iter().cloned().filter(|&i| i != r)
                        .map(|i| evenparts.iter().map(|&c| gcd(i, c)).collect()).collect();
                    per64(&m)
                };
                results.lock().unwrap()[job] = val;
                let c = done.fetch_add(1, Ordering::SeqCst) + 1;
                if verbose {
                    let el = start.elapsed().as_secs_f64();
                    let eta = el / (c as f64) * ((njobs - c) as f64);
                    let pct = 100.0 * (c as f64) / (njobs as f64);
                    eprintln!("  [n=65]  {:>2}/{} permanents  ({:>3.0}%)   elapsed {:>4.1} min   ETA {:>4.1} min",
                              c, njobs, pct, el / 60.0, eta / 60.0);
                    use std::io::Write as _;
                    let _ = std::io::stderr().flush();
                }
                if let Ok(mut g) = save.lock() { if let Some(f) = g.as_mut() {
                    let _ = writeln!(f, "n={} job={} val={:x}", n, job, val);
                }}
            }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let res = results.lock().unwrap();
    let pera: &[u64] = &res[0..nv];
    let cr: &[u64] = &res[nv..2 * nv];
    // per B_v = Σ_r gcd(r,v)·C_r ;  N0 = Σ_v per(A_v)·per(B_v)
    let mut n0: u64 = 0;
    for vi in 0..nv {
        let v = oddvals[vi];
        let mut perb: u64 = 0;
        for ri in 0..nv { perb = perb.wrapping_add(gcd(opos[ri], v).wrapping_mul(cr[ri])); }
        n0 = n0.wrapping_add(pera[vi].wrapping_mul(perb));
    }
    n0
}

fn s2(mut x: u64) -> u64 { let mut s = 0; while x > 0 { s += x & 1; x >>= 1; } s }

fn main() {
    let nthreads = thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    eprintln!("using {} threads", nthreads);
    let v33 = v2(n0_fast(33, nthreads, false));
    println!("n= 33  v2(N0)={:>3}   (must be 25: {})", v33, if v33 == 25 { "OK ✓" } else { "FAIL ✗ — do not trust n=65" });
    let start = Instant::now();
    let val = n0_fast(65, nthreads, true);
    let vn = v2(val) as i64;
    let d = (65 - s2(65)) as i64 - vn;
    println!("n= 65  v2(N0)={:>3}   predicted 55   deficit D={:>2}   [{}]   ({:?})",
             vn, d, if vn == 55 { "MATCH — D=8, five-for-five!" } else { "DIFFERS from conjecture" }, start.elapsed());
}
