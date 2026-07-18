// Adaptive-peak window row at c=3: achiever parity of
//   #{ v odd ≤ n : π₂(A_v) odd  ∧  π₃(B_v) odd },   n = 2^k + 3.
// Gram/matching engine (validated in Python for k ≤ 12):
//   π_j ≡ Σ_{|T|=j, T⊆P} ms_j(T,rowN)·ms_j(T,colN)  (mod 2),  P = prime powers q^a ≤ n, q≡3 (4),
//   ms₂({p,q},N)   = N(p)N(q) + N(lcm)                          (mod 2)
//   ms₃({p,q,r},N) = N(p)N(q)N(r) + N(pq)N(r) + N(pr)N(q) + N(qr)N(p)   (lcms; mod 2)
// Counts: A rows m/D; A cols (n/D+1)/2 − [D|v];  B rows (n/D+1)/2; B cols m/D + [D|v].
// Per-v: only T with T∩divisors(v) ≠ ∅ change (recompute-and-XOR delta).
//
// Build & run:  rustc -O -C target-cpu=native window_c3.rs -o /tmp/wc3 && /tmp/wc3 13
// k=13 ≈ seconds; k=15 ≈ a few minutes (threads).

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Instant;

fn gcd(a: u64, b: u64) -> u64 { if b == 0 { a } else { gcd(b, a % b) } }
fn lcm(a: u64, b: u64) -> u64 { a / gcd(a, b) * b }

fn prime_powers3(n: u64) -> Vec<u64> {
    let mut sieve = vec![true; (n + 1) as usize];
    let mut out = Vec::new();
    for q in 2..=n {
        if sieve[q as usize] {
            let mut x = q * q;
            while x <= n { sieve[x as usize] = false; x += q; }
            if q % 4 == 3 {
                let mut qa = q;
                while qa <= n { out.push(qa); if qa > n / q { break; } qa *= q; }
            }
        }
    }
    out.sort();
    out
}

// count functions (parity only matters at use sites, keep u64)
#[inline] fn a_row(d: u64, m: u64) -> u64 { m / d }
#[inline] fn nodd(d: u64, n: u64) -> u64 { (n / d + 1) / 2 }

#[inline]
fn ms2(p: u64, q: u64, f: &dyn Fn(u64) -> u64) -> u64 {
    (f(p) & 1) * (f(q) & 1) ^ (f(lcm(p, q)) & 1)
}
#[inline]
fn ms3(p: u64, q: u64, r: u64, f: &dyn Fn(u64) -> u64) -> u64 {
    let (a, b, c) = (f(p) & 1, f(q) & 1, f(r) & 1);
    (a & b & c)
        ^ ((f(lcm(p, q)) & 1) & c)
        ^ ((f(lcm(p, r)) & 1) & b)
        ^ ((f(lcm(q, r)) & 1) & a)
}
#[inline]
fn ms4(p: u64, q: u64, r: u64, s: u64, f: &dyn Fn(u64) -> u64) -> u64 {
    let (a, b, c, d) = (f(p) & 1, f(q) & 1, f(r) & 1, f(s) & 1);
    let (wpq, wpr, wps) = (f(lcm(p, q)) & 1, f(lcm(p, r)) & 1, f(lcm(p, s)) & 1);
    let (wqr, wqs, wrs) = (f(lcm(q, r)) & 1, f(lcm(q, s)) & 1, f(lcm(r, s)) & 1);
    (a & b & c & d)
        ^ (wpq & c & d) ^ (wpr & b & d) ^ (wps & b & c)
        ^ (wqr & a & d) ^ (wqs & a & c) ^ (wrs & a & b)
        ^ (wpq & wrs) ^ (wpr & wqs) ^ (wps & wqr)
}
// generic dispatcher over sorted index tuples
fn msj(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    match t.len() {
        2 => ms2(t[0], t[1], f),
        3 => ms3(t[0], t[1], t[2], f),
        4 => ms4(t[0], t[1], t[2], t[3], f),
        _ => unreachable!(),
    }
}
// enumerate all size-j index tuples with first index from `firsts`-style loops is inlined at call sites
fn for_tuples(np: usize, j: usize, start_i: usize, skip: &dyn Fn(usize) -> bool, mut g: impl FnMut(&[usize])) {
    // fixed first index start_i; remaining j-1 from increasing indices, honoring skip
    let mut idxs = vec![0usize; j];
    idxs[0] = start_i;
    fn rec(np: usize, j: usize, pos: usize, min_next: usize, skip: &dyn Fn(usize) -> bool,
           idxs: &mut Vec<usize>, g: &mut dyn FnMut(&[usize])) {
        if pos == j { g(idxs); return; }
        for x in min_next..np {
            if skip(x) { continue; }
            idxs[pos] = x;
            rec(np, j, pos + 1, x + 1, skip, idxs, g);
        }
    }
    rec(np, j, 1, 0, skip, &mut idxs, &mut g);
}

fn main() {
    let k: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(13);
    let c: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(3);
    let d: usize = ((c - 1) / 2) as usize;
    let (ja, jb) = (d + 1, d + 2);
    let n: u64 = (1u64 << k) + c;
    let m: u64 = n / 2;
    let pp = Arc::new(prime_powers3(n));
    let np = pp.len();
    let nthreads: usize = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    eprintln!("k={} c={} n={} |P|={} jA={} jB={} threads={}", k, c, n, np, ja, jb, nthreads);
    let t0 = Instant::now();

    // ---- base sums S0A (pairs, j=2) and S0B (triples, j=3), parallel over first index ----
    let idx = Arc::new(AtomicUsize::new(0));
    let s0a_acc = Arc::new(AtomicU64::new(0));
    let s0b_acc = Arc::new(AtomicU64::new(0));
    let mut hs = Vec::new();
    for _ in 0..nthreads {
        let (pp, idx, s0a_acc, s0b_acc) = (pp.clone(), idx.clone(), s0a_acc.clone(), s0b_acc.clone());
        hs.push(std::thread::spawn(move || {
            let arow = |d: u64| a_row(d, m);
            let acol = |d: u64| nodd(d, n);
            let brow = |d: u64| nodd(d, n);
            let bcol = |d: u64| a_row(d, m);
            let (mut sa, mut sb) = (0u64, 0u64);
            loop {
                let i = idx.fetch_add(1, Ordering::Relaxed);
                if i >= np { break; }
                // A-side tuples of size ja starting at i
                for_tuples(np, ja, i, &|x| x <= i && x != i, |t| {
                    let vals: Vec<u64> = t.iter().map(|&x| pp[x]).collect();
                    if msj(&vals, &arow) == 1 { sa ^= msj(&vals, &acol); }
                });
                // B-side tuples of size jb starting at i
                for_tuples(np, jb, i, &|x| x <= i && x != i, |t| {
                    let vals: Vec<u64> = t.iter().map(|&x| pp[x]).collect();
                    if msj(&vals, &brow) == 1 { sb ^= msj(&vals, &bcol); }
                });
            }
            s0a_acc.fetch_xor(sa, Ordering::Relaxed);
            s0b_acc.fetch_xor(sb, Ordering::Relaxed);
        }));
    }
    for h in hs { h.join().unwrap(); }
    let s0a = s0a_acc.load(Ordering::Relaxed) & 1;
    let s0b = s0b_acc.load(Ordering::Relaxed) & 1;
    eprintln!("base sums done: S0A={} S0B={}  ({:.1}s)", s0a, s0b, t0.elapsed().as_secs_f64());

    // ---- per-v deltas, parallel over v ----
    let vcnt = Arc::new(AtomicU64::new(0));
    let vidx = Arc::new(AtomicU64::new(0));
    let mut hv = Vec::new();
    for _ in 0..nthreads {
        let (pp, vidx, vcnt) = (pp.clone(), vidx.clone(), vcnt.clone());
        hv.push(std::thread::spawn(move || {
            let arow = |d: u64| a_row(d, m);
            let brow = |d: u64| nodd(d, n);
            let mut local = 0u64;
            loop {
                let t = vidx.fetch_add(1, Ordering::Relaxed);
                let v = 2 * t + 1;
                if v > n { break; }
                let dv: Vec<usize> = (0..np).filter(|&i| v % pp[i] == 0).collect();
                let (mut da, mut db) = (0u64, 0u64);
                if !dv.is_empty() {
                    let acol_b = |d: u64| nodd(d, n);
                    let acol_v = |d: u64| nodd(d, n) - if v % d == 0 { 1 } else { 0 };
                    let bcol_b = |d: u64| a_row(d, m);
                    let bcol_v = |d: u64| a_row(d, m) + if v % d == 0 { 1 } else { 0 };
                    let in_dv = |i: usize| dv.binary_search(&i).is_ok();
                    // T ∩ Dv ≠ ∅, canonical: ip = smallest Dv-index in T; rest avoid Dv-indices < ip and ip itself
                    for &ip in &dv {
                        let skip = |x: usize| x == ip || (in_dv(x) && x < ip);
                        for_tuples(np, ja, ip, &skip, |t| {
                            let mut vals: Vec<u64> = t.iter().map(|&x| pp[x]).collect();
                            vals.sort();
                            if msj(&vals, &arow) == 1 {
                                da ^= msj(&vals, &acol_b) ^ msj(&vals, &acol_v);
                            }
                        });
                        for_tuples(np, jb, ip, &skip, |t| {
                            let mut vals: Vec<u64> = t.iter().map(|&x| pp[x]).collect();
                            vals.sort();
                            if msj(&vals, &brow) == 1 {
                                db ^= msj(&vals, &bcol_b) ^ msj(&vals, &bcol_v);
                            }
                        });
                    }
                }
                if (s0a ^ da) == 1 && (s0b ^ db) == 1 { local += 1; }
            }
            vcnt.fetch_add(local, Ordering::Relaxed);
        }));
    }
    for h in hv { h.join().unwrap(); }
    let count = vcnt.load(Ordering::Relaxed);
    println!("k={} c={} achiever count={} parity={}  ({:.1}s)",
        k, c, count, if count % 2 == 1 { "ODD" } else { "EVEN" }, t0.elapsed().as_secs_f64());
}
