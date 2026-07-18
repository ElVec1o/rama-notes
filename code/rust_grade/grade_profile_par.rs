// Parallel grade profile of a(n) = per[gcd(i,j)]  (see grade_profile.rs for the math).
// Ryser splits cleanly: fix the top T columns to a bitmask f (2^T independent tasks),
// Gray-code the bottom (n-T) columns within each task, sum the partial poly-results.
// Threads pull tasks from an atomic counter; each keeps a local accumulator.
//
// Build & run (one line):
//   rustc -C opt-level=3 -C target-cpu=native grade_profile_par.rs -o /tmp/gpp && /tmp/gpp 33
// Optional: /tmp/gpp <n> <threads> <T>   (defaults: threads = ncpu, T = 8).

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use std::io::Write;

fn v2(mut x: u64) -> usize { if x == 0 { return 64; } let mut v = 0; while x & 1 == 0 { x >>= 1; v += 1; } v }
fn oddpart(mut x: u64) -> u64 { while x & 1 == 0 { x >>= 1; } x }
fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(33);
    let nthreads: usize = args.get(2).and_then(|s| s.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4));
    let t_bits: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(8).min(n - 1);
    assert!(n >= 2 && n <= 40);

    // monomial entries c[i][j] * t^{e[i][j]}
    let mut e = vec![vec![0usize; n]; n];
    let mut c = vec![vec![0u64; n]; n];
    for i in 0..n {
        let vi = v2((i + 1) as u64); let oi = oddpart((i + 1) as u64);
        for j in 0..n { e[i][j] = vi.min(v2((j + 1) as u64)); c[i][j] = gcd(oi, oddpart((j + 1) as u64)); }
    }
    let maxdeg: usize = (1..=n).map(|i| v2(i as u64)).sum();  // = v2(n!)
    let dsize = maxdeg + 1;
    let rideg: Vec<usize> = (0..n).map(|i| v2((i + 1) as u64).min(maxdeg)).collect();

    let e = Arc::new(e); let c = Arc::new(c); let rideg = Arc::new(rideg);
    let ntasks: u64 = 1u64 << t_bits;             // top-bit configs
    let nbot: usize = n - t_bits;                 // bottom columns 0..nbot-1; top cols nbot..n-1
    let next = Arc::new(AtomicU64::new(0));        // task dispenser
    let done = Arc::new(AtomicU64::new(0));        // completed tasks (progress)
    let global = Arc::new(Mutex::new(vec![0i128; dsize]));  // combined acc (i128 to sum partials safely mod 2^64 via wrap at end)
    let start = Instant::now();

    let mut handles = Vec::new();
    for _ in 0..nthreads {
        let (e, c, rideg) = (e.clone(), c.clone(), rideg.clone());
        let (next, done, global) = (next.clone(), done.clone(), global.clone());
        handles.push(std::thread::spawn(move || {
            let mut acc = vec![0u64; dsize];          // local Ryser sum mod 2^64
            let mut rows = vec![vec![0u64; dsize]; n];
            let mut prod = vec![0u64; dsize];
            let mut tmp = vec![0u64; dsize];
            loop {
                let f = next.fetch_add(1, Ordering::Relaxed);
                if f >= ntasks { break; }
                // init rowsums from the top columns set in f
                for r in rows.iter_mut() { for x in r.iter_mut() { *x = 0; } }
                let mut pc_top = 0usize;
                for tb in 0..t_bits {
                    if (f >> tb) & 1 == 1 {
                        pc_top += 1;
                        let j = nbot + tb;
                        for i in 0..n { let ei = e[i][j]; rows[i][ei] = rows[i][ei].wrapping_add(c[i][j]); }
                    }
                }
                // process all bottom subsets via Gray code
                let mut prev: u64 = 0;
                let bot_total: u64 = 1u64 << nbot;
                for g in 0..bot_total {
                    if g != 0 {
                        let gray = g ^ (g >> 1);
                        let diff = gray ^ prev;
                        let j = diff.trailing_zeros() as usize; // bottom column
                        if (gray & diff) != 0 {
                            for i in 0..n { let ei = e[i][j]; rows[i][ei] = rows[i][ei].wrapping_add(c[i][j]); }
                        } else {
                            for i in 0..n { let ei = e[i][j]; rows[i][ei] = rows[i][ei].wrapping_sub(c[i][j]); }
                        }
                        prev = gray;
                    }
                    let botset = g ^ (g >> 1);
                    let ssize = pc_top + botset.count_ones() as usize;
                    if ssize == 0 { continue; } // empty S -> product 0
                    // prod = product_i rows[i]  (truncated to maxdeg)
                    for x in prod.iter_mut() { *x = 0; } prod[0] = 1;
                    let mut curdeg = 0usize;
                    for i in 0..n {
                        let rd_i = rideg[i];
                        let newdeg = (curdeg + rd_i).min(maxdeg);
                        for x in tmp[0..=newdeg].iter_mut() { *x = 0; }
                        for a in 0..=curdeg {
                            let pa = prod[a]; if pa == 0 { continue; }
                            for b in 0..=rd_i {
                                let cb = rows[i][b];
                                if cb != 0 && a + b <= maxdeg { tmp[a + b] = tmp[a + b].wrapping_add(pa.wrapping_mul(cb)); }
                            }
                        }
                        curdeg = newdeg;
                        prod[0..=curdeg].copy_from_slice(&tmp[0..=curdeg]);
                    }
                    if (n - ssize) & 1 == 0 { for w in 0..dsize { acc[w] = acc[w].wrapping_add(prod[w]); } }
                    else { for w in 0..dsize { acc[w] = acc[w].wrapping_sub(prod[w]); } }
                }
                let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                if d % 4 == 0 {
                    let el = start.elapsed().as_secs_f64();
                    let frac = d as f64 / ntasks as f64;
                    eprint!("\r  n={} {:6.2}%  elapsed {:.0}s  ETA {:.0}s   ", n, 100.0 * frac, el, el / frac - el);
                    std::io::stderr().flush().ok();
                }
            }
            // fold local acc (mod 2^64) into global as signed i128
            let mut gg = global.lock().unwrap();
            for w in 0..dsize { gg[w] += acc[w] as i128; }
        }));
    }
    for h in handles { h.join().unwrap(); }
    eprintln!();

    let gg = global.lock().unwrap();
    let acc: Vec<u64> = gg.iter().map(|&x| (x as i128 & ((1i128 << 64) - 1)) as u64).collect();

    let mut a_mod: u64 = 0;
    for w in 0..dsize { a_mod = a_mod.wrapping_add(acc[w].wrapping_shl(w as u32)); }
    println!("n = {}   maxdeg=v2(n!) = {}   threads={}  T={}", n, maxdeg, nthreads, t_bits);
    println!("{:>3} {:>10} {:>12}", "w", "v2(N_w)", "w+v2(N_w)");
    let (mut best, mut best2) = (usize::MAX, usize::MAX);
    let mut argmin = Vec::new();
    for w in 0..dsize {
        if acc[w] == 0 { continue; }
        let vn = acc[w].trailing_zeros() as usize; let tot = w + vn;
        println!("{:>3} {:>10} {:>12}", w, vn, tot);
        if tot < best { best2 = best; best = tot; argmin = vec![w]; }
        else if tot == best { argmin.push(w); }
        else if tot < best2 { best2 = tot; }
    }
    let margin = if best2 == usize::MAX { 999 } else { best2 - best };
    println!("\nmin_w (w+v2(N_w)) = {}  at w = {:?}  MARGIN to 2nd = {}", best, argmin, margin);
    println!("v2(a(n)) = {}   (expect 25 for n=33)", a_mod.trailing_zeros());
    println!("VERDICT: argmin=[0] & large margin => w=0 dominates => deficit BOUNDED (turnover, D(65)=5).");
    println!("         a low w competes/wins       => deficit UNBOUNDED (D(65)=8).");
}
