// Window row via the NORMAL FORM (no per-v loop):
//   C(k,c) ≡ b1·b2·V ⊕ b2·L(α) ⊕ b1·L(β) ⊕ αᵀMβ   (mod 2)
// where (linearity lemma, proved by induction on the matching recursion)
//   b   = Σ_{|T|=j} ms_j(T,row)·ms_j(T,colbase)
//   γ_D = Σ_{T∋D}  ms_j(T,row)·ms_{j-1}(T∖D,colbase)
//   L(γ)= Σ_D γ_D·oddmult(D),   M_{DE} = oddmult(lcm(D,E)),  V = ((c+1)/2) & 1.
// A-side: j=d+1, row=m/D, colbase=oddmult;  B-side: j=d+2, row=oddmult, colbase=m/D.
//
// Build & run:  rustc -O -C target-cpu=native window_nf.rs -o /tmp/wnf && /tmp/wnf <k> <c>

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
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

#[inline]
fn ms1(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    ((f(t[0]) & 1))
}
#[inline]
fn ms2(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    ((f(t[0]) & 1) & (f(t[1]) & 1)) ^ ((f(lcm(t[0], t[1])) & 1))
}
#[inline]
fn ms3(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[2])) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(t[2]) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(t[1]) & 1))
}
#[inline]
fn ms4(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1)) ^ ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(lcm(t[2], t[3])) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[2])) & 1) & (f(t[3]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[3])) & 1) & (f(t[2]) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(lcm(t[2], t[3])) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(t[1]) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(lcm(t[1], t[3])) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(lcm(t[1], t[2])) & 1))
}
#[inline]
fn ms5(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1) & (f(t[4]) & 1)) ^ ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1) & (f(lcm(t[3], t[4])) & 1)) ^ ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(lcm(t[2], t[3])) & 1) & (f(t[4]) & 1)) ^ ((f(t[0]) & 1) & (f(t[1]) & 1) & (f(lcm(t[2], t[4])) & 1) & (f(t[3]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[2])) & 1) & (f(t[3]) & 1) & (f(t[4]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[2])) & 1) & (f(lcm(t[3], t[4])) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[3])) & 1) & (f(t[2]) & 1) & (f(t[4]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[3])) & 1) & (f(lcm(t[2], t[4])) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[4])) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1)) ^ ((f(t[0]) & 1) & (f(lcm(t[1], t[4])) & 1) & (f(lcm(t[2], t[3])) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(t[2]) & 1) & (f(lcm(t[3], t[4])) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(lcm(t[2], t[3])) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[1])) & 1) & (f(lcm(t[2], t[4])) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(t[1]) & 1) & (f(t[3]) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(t[1]) & 1) & (f(lcm(t[3], t[4])) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(lcm(t[1], t[3])) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[2])) & 1) & (f(lcm(t[1], t[4])) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(t[1]) & 1) & (f(lcm(t[2], t[4])) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(lcm(t[1], t[2])) & 1) & (f(t[4]) & 1)) ^ ((f(lcm(t[0], t[3])) & 1) & (f(lcm(t[1], t[4])) & 1) & (f(t[2]) & 1)) ^ ((f(lcm(t[0], t[4])) & 1) & (f(t[1]) & 1) & (f(t[2]) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[4])) & 1) & (f(t[1]) & 1) & (f(lcm(t[2], t[3])) & 1)) ^ ((f(lcm(t[0], t[4])) & 1) & (f(lcm(t[1], t[2])) & 1) & (f(t[3]) & 1)) ^ ((f(lcm(t[0], t[4])) & 1) & (f(lcm(t[1], t[3])) & 1) & (f(t[2]) & 1))
}
#[inline]
fn ms(t: &[u64], f: &dyn Fn(u64) -> u64) -> u64 {
    match t.len() {
        0 => 1,
        1 => ms1(t, f),
        2 => ms2(t, f),
        3 => ms3(t, f),
        4 => ms4(t, f),
        5 => ms5(t, f),
        _ => unreachable!(),
    }
}

// enumerate T of size j (parallel over first index); accumulate b and alpha
fn side_coeffs(pp: &Arc<Vec<u64>>, j: usize, row: Arc<dyn Fn(u64) -> u64 + Send + Sync>,
               colb: Arc<dyn Fn(u64) -> u64 + Send + Sync>, nthreads: usize) -> (u64, Vec<u64>) {
    let np = pp.len();
    let idx = Arc::new(AtomicUsize::new(0));
    let bacc = Arc::new(AtomicU64::new(0));
    let alpha = Arc::new(Mutex::new(vec![0u64; np]));
    let mut hs = Vec::new();
    for _ in 0..nthreads {
        let (pp, idx, bacc, alpha) = (pp.clone(), idx.clone(), bacc.clone(), alpha.clone());
        let (row, colb) = (row.clone(), colb.clone());
        hs.push(std::thread::spawn(move || {
            let mut la = vec![0u64; pp.len()];
            let mut lb = 0u64;
            let mut idxs = vec![0usize; j];
            loop {
                let i = idx.fetch_add(1, Ordering::Relaxed);
                if i >= pp.len() { break; }
                idxs[0] = i;
                // recursive enumeration of the remaining j-1 indices > previous
                fn rec(pp: &Vec<u64>, idxs: &mut Vec<usize>, pos: usize, j: usize,
                       row: &dyn Fn(u64) -> u64, colb: &dyn Fn(u64) -> u64,
                       la: &mut Vec<u64>, lb: &mut u64) {
                    if pos == j {
                        let vals: Vec<u64> = idxs.iter().map(|&x| pp[x]).collect();
                        if ms(&vals, row) == 1 {
                            *lb ^= ms(&vals, colb);
                            for (t, &ix) in idxs.iter().enumerate() {
                                let sub: Vec<u64> = vals.iter().enumerate()
                                    .filter(|(s, _)| *s != t).map(|(_, &v)| v).collect();
                                la[ix] ^= ms(&sub, colb);
                            }
                        }
                        return;
                    }
                    for x in (idxs[pos - 1] + 1)..pp.len() {
                        idxs[pos] = x;
                        rec(pp, idxs, pos + 1, j, row, colb, la, lb);
                    }
                }
                rec(&pp, &mut idxs, 1, j, row.as_ref(), colb.as_ref(), &mut la, &mut lb);
            }
            bacc.fetch_xor(lb & 1, Ordering::Relaxed);
            let mut g = alpha.lock().unwrap();
            for (x, v) in la.iter().enumerate() { g[x] ^= v & 1; }
        }));
    }
    for h in hs { h.join().unwrap(); }
    let b = bacc.load(Ordering::Relaxed) & 1;
    let a = alpha.lock().unwrap().clone();
    (b, a)
}

fn main() {
    let k: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(13);
    let c: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(5);
    let d = ((c - 1) / 2) as usize;
    let (ja, jb) = (d + 1, d + 2);
    let n: u64 = (1u64 << k) + c;
    let m: u64 = n / 2;
    let pp = Arc::new(prime_powers3(n));
    let np = pp.len();
    let nthreads = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4);
    eprintln!("k={} c={} n={} |P|={} jA={} jB={} threads={}", k, c, n, np, ja, jb, nthreads);
    let t0 = Instant::now();

    let a_row: Arc<dyn Fn(u64) -> u64 + Send + Sync> = Arc::new(move |dd: u64| m / dd);
    let a_col: Arc<dyn Fn(u64) -> u64 + Send + Sync> = Arc::new(move |dd: u64| (n / dd + 1) / 2);
    let b_row = a_col.clone();
    let b_col = a_row.clone();

    let (b1, alpha) = side_coeffs(&pp, ja, a_row, a_col.clone(), nthreads);
    eprintln!("A-side done ({:.1}s): b1={}  |alpha|={}", t0.elapsed().as_secs_f64(), b1,
        alpha.iter().filter(|&&x| x == 1).count());
    let (b2, beta) = side_coeffs(&pp, jb, b_row, b_col, nthreads);
    eprintln!("B-side done ({:.1}s): b2={}  |beta|={}", t0.elapsed().as_secs_f64(), b2,
        beta.iter().filter(|&&x| x == 1).count());

    let oddm = |dd: u64| ((n / dd + 1) / 2) & 1;
    let vpar = ((c + 1) / 2) & 1;
    let (mut l1, mut l2) = (0u64, 0u64);
    for i in 0..np {
        if alpha[i] == 1 { l1 ^= oddm(pp[i]); }
        if beta[i] == 1 { l2 ^= oddm(pp[i]); }
    }
    // bilinear form over the sparse supports
    let sa: Vec<u64> = (0..np).filter(|&i| alpha[i] == 1).map(|i| pp[i]).collect();
    let sb: Vec<u64> = (0..np).filter(|&i| beta[i] == 1).map(|i| pp[i]).collect();
    let mut bform = 0u64;
    for &x in &sa {
        for &y in &sb {
            let l = lcm(x, y);
            if l <= n { bform ^= oddm(l); }
        }
    }
    let cnt = (b1 & b2 & vpar) ^ (b2 & l1) ^ (b1 & l2) ^ bform;
    println!("k={} c={} NORMAL-FORM parity = {}  ({})   ({:.1}s)",
        k, c, cnt, if cnt == 1 { "ODD" } else { "EVEN" }, t0.elapsed().as_secs_f64());
}
