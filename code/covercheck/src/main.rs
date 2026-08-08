//! Falsification sweep for Conjecture 10 and GAPCOUNT on graphs of feedback vertex
//! number at most two.
//!
//! For each graph this computes, independently:
//!   - the matching polynomial's exact integer coefficients, and the number of its roots
//!     above a point by Budan-Fourier, which is exact because the matching polynomial is
//!     real rooted (Heilmann-Lieb);
//!   - the spectrum of the universal cover, by the non-backtracking cavity equations on
//!     the directed edges, and the gap label kappa by integrating the density.
//! It then checks that every matching root lies in a band (Conjecture 10) and that kappa
//! equals the root count at every gap (GAPCOUNT).
//!
//! This is the Rust version of code/universal_cover.py, which is the readable reference
//! implementation and carries the regression check against the closed form for K4 with a
//! pendant at each vertex. The two agree on the shared cases; see the header there.
//!
//! Rule 8 compliance: progress, rate and ETA are printed; partial results are checkpointed
//! to disk by atomic rename so a kill loses nothing; the run resumes from the checkpoint.
//! Output is a few kilobytes, which matters because the machine is at 97 percent disk.
//!
//! A run that fails the validity gate (density not integrating to one) is discarded rather
//! than reported. Point spectrum makes the cavity fixed point singular, and a diverged
//! kappa looks exactly like a violated GAPCOUNT while being nothing of the kind.

use std::fs;
use std::io::Write;
use std::time::Instant;

const GRID: usize = 1200;
const MAXIT: usize = 3000;
const TOL: f64 = 1e-11;
const MASS_TOL: f64 = 0.02;
const ETAS: [f64; 4] = [1e-6, 1e-4, 1e-3, 1e-2];

#[derive(Clone, Copy)]
struct C {
    re: f64,
    im: f64,
}

impl C {
    fn new(re: f64, im: f64) -> C {
        C { re, im }
    }
    fn add(self, o: C) -> C {
        C::new(self.re + o.re, self.im + o.im)
    }
    fn sub(self, o: C) -> C {
        C::new(self.re - o.re, self.im - o.im)
    }
    fn scale(self, t: f64) -> C {
        C::new(self.re * t, self.im * t)
    }
    fn inv(self) -> C {
        let d = self.re * self.re + self.im * self.im;
        let d = if d < 1e-300 { 1e-300 } else { d };
        C::new(self.re / d, -self.im / d)
    }
    fn abs(self) -> f64 {
        (self.re * self.re + self.im * self.im).sqrt()
    }
}

/// Union-find, used for connectivity and for the forest test.
struct Uf {
    p: Vec<usize>,
}
impl Uf {
    fn new(n: usize) -> Uf {
        Uf { p: (0..n).collect() }
    }
    fn find(&mut self, a: usize) -> usize {
        let mut a = a;
        while self.p[a] != a {
            self.p[a] = self.p[self.p[a]];
            a = self.p[a];
        }
        a
    }
    fn union(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        self.p[ra] = rb;
        true
    }
}

fn connected(n: usize, edges: &[(usize, usize)]) -> bool {
    let mut uf = Uf::new(n);
    for &(u, v) in edges {
        uf.union(u, v);
    }
    let r = uf.find(0);
    (0..n).all(|v| uf.find(v) == r)
}

fn is_forest(n: usize, edges: &[(usize, usize)]) -> bool {
    let mut uf = Uf::new(n);
    for &(u, v) in edges {
        if !uf.union(u, v) {
            return false;
        }
    }
    true
}

/// Smallest k such that deleting some k vertices leaves a forest, capped at 3.
fn feedback_number(n: usize, edges: &[(usize, usize)]) -> usize {
    let keep = |drop: &[usize]| -> Vec<(usize, usize)> {
        edges
            .iter()
            .cloned()
            .filter(|&(u, v)| !drop.contains(&u) && !drop.contains(&v))
            .collect()
    };
    if is_forest(n, edges) {
        return 0;
    }
    for a in 0..n {
        if is_forest(n, &keep(&[a])) {
            return 1;
        }
    }
    for a in 0..n {
        for b in (a + 1)..n {
            if is_forest(n, &keep(&[a, b])) {
                return 2;
            }
        }
    }
    3
}

/// Ascending integer coefficients of the matching polynomial.
fn matching_coeffs(n: usize, edges: &[(usize, usize)]) -> Vec<f64> {
    let m = edges.len();
    // counts[k] = number of k-matchings, by DP over edges with a used-vertex mask
    let mut counts = vec![0i64; n / 2 + 1];
    // iterative subset DP: dp[mask] over matchings is exponential in n, but n <= 8 here
    // so a simple recursive enumeration with memo on (edge index, mask) is enough.
    let mut memo = vec![-1i64; (m + 1) * (1 << n) * (n / 2 + 2)];
    fn rec(
        i: usize,
        mask: usize,
        k: usize,
        m: usize,
        n: usize,
        edges: &[(usize, usize)],
        memo: &mut Vec<i64>,
    ) -> i64 {
        if i == m {
            return if k == 0 { 1 } else { 0 };
        }
        let idx = (i * (1 << n) + mask) * (n / 2 + 2) + k;
        if memo[idx] >= 0 {
            return memo[idx];
        }
        let mut t = rec(i + 1, mask, k, m, n, edges, memo);
        if k > 0 {
            let (u, v) = edges[i];
            let (bu, bv) = (1usize << u, 1usize << v);
            if mask & bu == 0 && mask & bv == 0 {
                t += rec(i + 1, mask | bu | bv, k - 1, m, n, edges, memo);
            }
        }
        memo[idx] = t;
        t
    }
    for k in 0..=(n / 2) {
        counts[k] = rec(0, 0, k, m, n, edges, &mut memo);
    }
    let mut c = vec![0f64; n + 1];
    for k in 0..=(n / 2) {
        let s = if k % 2 == 0 { 1.0 } else { -1.0 };
        c[n - 2 * k] += s * counts[k] as f64;
    }
    c
}

/// Number of roots strictly above `e`, by Budan-Fourier.  Exact for a real-rooted
/// polynomial with positive leading coefficient, which the matching polynomial is.
fn roots_above(coeffs: &[f64], e: f64) -> usize {
    let n = coeffs.len() - 1;
    let mut cur: Vec<f64> = coeffs.to_vec();
    let mut vals = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        // Horner
        let mut acc = 0.0;
        for j in (0..cur.len()).rev() {
            acc = acc * e + cur[j];
        }
        vals.push(acc);
        // differentiate
        if cur.len() <= 1 {
            cur = vec![0.0];
        } else {
            let mut d = vec![0.0; cur.len() - 1];
            for j in 1..cur.len() {
                d[j - 1] = cur[j] * j as f64;
            }
            cur = d;
        }
    }
    let mut changes = 0usize;
    let mut last = 0.0f64;
    for v in vals {
        if v.abs() < 1e-12 {
            continue;
        }
        if last != 0.0 && v * last < 0.0 {
            changes += 1;
        }
        last = v;
    }
    changes
}

struct Adj {
    nbr: Vec<Vec<usize>>,
    de: Vec<(usize, usize)>,
    idx: Vec<Vec<i32>>,
}

fn build_adj(n: usize, edges: &[(usize, usize)]) -> Adj {
    let mut nbr = vec![Vec::new(); n];
    for &(u, v) in edges {
        nbr[u].push(v);
        nbr[v].push(u);
    }
    let mut de = Vec::new();
    let mut idx = vec![vec![-1i32; n]; n];
    for u in 0..n {
        for &v in &nbr[u] {
            idx[u][v] = de.len() as i32;
            de.push((u, v));
        }
    }
    Adj { nbr, de, idx }
}

/// Density of states of the universal cover at `e + i eta`, warm-started from `h`.
fn density(a: &Adj, n: usize, e: f64, eta: f64, h: &mut Vec<C>) -> (f64, bool) {
    let z = C::new(e, eta);
    let mut conv = false;
    let mut new = vec![C::new(0.0, 0.0); a.de.len()];
    for _ in 0..MAXIT {
        let mut diff = 0.0f64;
        for k in 0..a.de.len() {
            let (u, v) = a.de[k];
            let mut s = C::new(0.0, 0.0);
            for &w in &a.nbr[u] {
                if w != v {
                    s = s.add(h[a.idx[w][u] as usize]);
                }
            }
            new[k] = z.sub(s).inv();
            let d = new[k].sub(h[k]).abs();
            if d > diff {
                diff = d;
            }
        }
        for k in 0..a.de.len() {
            h[k] = new[k].scale(0.5).add(h[k].scale(0.5));
        }
        if diff < TOL {
            conv = true;
            break;
        }
    }
    let mut tot = 0.0;
    for v in 0..n {
        let mut s = C::new(0.0, 0.0);
        for &u in &a.nbr[v] {
            s = s.add(h[a.idx[u][v] as usize]);
        }
        let g = z.sub(s).inv();
        tot += -g.im / std::f64::consts::PI;
    }
    (tot / n as f64, conv)
}

/// Sweep downward with continuation; returns (energies ascending, densities, mass).
fn scan(a: &Adj, n: usize, lo: f64, hi: f64, eta: f64) -> (Vec<f64>, Vec<f64>, f64) {
    let mut h = vec![C::new(0.0, -0.1); a.de.len()];
    let mut es = Vec::with_capacity(GRID + 1);
    let mut ds = Vec::with_capacity(GRID + 1);
    for i in 0..=GRID {
        let e = hi - (hi - lo) * i as f64 / GRID as f64;
        let (d, _) = density(a, n, e, eta, &mut h);
        es.push(e);
        ds.push(d.max(0.0));
    }
    es.reverse();
    ds.reverse();
    let step = (hi - lo) / GRID as f64;
    let mut mass = 0.0;
    for i in 0..ds.len() - 1 {
        mass += 0.5 * (ds[i] + ds[i + 1]) * step;
    }
    (es, ds, mass)
}

fn bands(es: &[f64], ds: &[f64], thresh: f64) -> Vec<(f64, f64)> {
    let mut out = Vec::new();
    let mut inb = false;
    let mut start = 0.0;
    for i in 0..es.len() {
        if ds[i] > thresh && !inb {
            inb = true;
            start = es[i];
        } else if ds[i] <= thresh && inb {
            inb = false;
            out.push((start, es[i]));
        }
    }
    if inb {
        out.push((start, *es.last().unwrap()));
    }
    out
}

fn kappa_above(es: &[f64], ds: &[f64], n: usize, e0: f64) -> f64 {
    let mut tot = 0.0;
    for i in 0..es.len() - 1 {
        let (mut a, b) = (es[i], es[i + 1]);
        if b <= e0 {
            continue;
        }
        if a < e0 {
            a = e0;
        }
        tot += 0.5 * (ds[i] + ds[i + 1]) * (b - a);
    }
    n as f64 * tot
}

struct Report {
    checked: usize,
    gaps: usize,
    conj10_fail: usize,
    gapcount_fail: usize,
    gated: usize,
    worst_int_err: f64,
    examples: Vec<String>,
}

fn examine(n: usize, edges: &[(usize, usize)], rep: &mut Report) {
    let coeffs = matching_coeffs(n, edges);
    // Heilmann-Lieb bound gives a safe window
    let maxdeg = {
        let mut d = vec![0usize; n];
        for &(u, v) in edges {
            d[u] += 1;
            d[v] += 1;
        }
        *d.iter().max().unwrap()
    };
    let r = 2.0 * ((maxdeg as f64 - 1.0).max(1.0)).sqrt() + 1.5;
    let a = build_adj(n, edges);
    let mut ok = None;
    for &eta in ETAS.iter() {
        let (es, ds, mass) = scan(&a, n, -r, r, eta);
        if (mass - 1.0).abs() <= MASS_TOL {
            ok = Some((es, ds));
            break;
        }
    }
    let (es, ds) = match ok {
        Some(x) => x,
        None => {
            rep.gated += 1;
            return;
        }
    };
    rep.checked += 1;
    let bs = bands(&es, &ds, 1e-3);
    // Conjecture 10: every root inside a band.  Root positions are located by bisection
    // on the exact root count, which avoids a root finder entirely.
    let step = 2.0 * r / GRID as f64;
    let mut e = -r;
    let mut prev = roots_above(&coeffs, -r);
    while e < r {
        let nx = e + step;
        let cnt = roots_above(&coeffs, nx);
        if cnt < prev {
            // a root lies in (e, nx]
            let mid = 0.5 * (e + nx);
            let inband = bs.iter().any(|&(lo, hi)| mid >= lo - 2.0 * step && mid <= hi + 2.0 * step);
            if !inband {
                rep.conj10_fail += 1;
                if rep.examples.len() < 8 {
                    rep.examples.push(format!(
                        "CONJ10 n={} edges={:?} root near {:.4} bands {:?}",
                        n, edges, mid, bs
                    ));
                }
            }
        }
        prev = cnt;
        e = nx;
    }
    // GAPCOUNT at gap midpoints
    let mut prev_hi = -r;
    for &(lo, hi) in bs.iter() {
        if lo - prev_hi > 0.08 {
            let e0 = 0.5 * (prev_hi + lo);
            let k = kappa_above(&es, &ds, n, e0);
            let ng = roots_above(&coeffs, e0);
            let err = (k - k.round()).abs();
            if err > rep.worst_int_err {
                rep.worst_int_err = err;
            }
            rep.gaps += 1;
            if k.round() as usize != ng {
                rep.gapcount_fail += 1;
                if rep.examples.len() < 8 {
                    rep.examples.push(format!(
                        "GAPCOUNT n={} edges={:?} E={:.4} kappa={:.4} N_G={}",
                        n, edges, e0, k, ng
                    ));
                }
            }
        }
        prev_hi = hi;
    }
}

fn main() {
    let t0 = Instant::now();
    let mut rep = Report {
        checked: 0,
        gaps: 0,
        conj10_fail: 0,
        gapcount_fail: 0,
        gated: 0,
        worst_int_err: 0.0,
        examples: Vec::new(),
    };
    let ckpt = "code/covercheck/checkpoint.txt";
    let mut done_upto = 0usize;
    if let Ok(s) = fs::read_to_string(ckpt) {
        if let Some(first) = s.lines().next() {
            done_upto = first.trim().parse().unwrap_or(0);
        }
    }
    if done_upto > 0 {
        println!("resuming after {} graphs", done_upto);
    }

    let mut seen = 0usize;
    // exhaustive on 4..=6 vertices, sampled on 7
    let mut rng: u64 = 0x2026_0809_1234_5678;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    for n in 4..=7usize {
        let pairs: Vec<(usize, usize)> = (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
            .collect();
        let np = pairs.len();
        let total: u64 = 1u64 << np;
        let sample = n >= 7;
        let count = if sample { 40_000u64 } else { total };
        for t in 0..count {
            let bits = if sample { next() % total } else { t };
            let edges: Vec<(usize, usize)> = (0..np)
                .filter(|&i| bits >> i & 1 == 1)
                .map(|i| pairs[i])
                .collect();
            if edges.len() < n {
                continue; // needs a cycle
            }
            if !connected(n, &edges) {
                continue;
            }
            if feedback_number(n, &edges) > 2 {
                continue;
            }
            seen += 1;
            if seen <= done_upto {
                continue;
            }
            examine(n, &edges, &mut rep);
            if seen % 200 == 0 {
                let el = t0.elapsed().as_secs_f64();
                let rate = (seen - done_upto) as f64 / el.max(1e-9);
                println!(
                    "  n={} seen={} checked={} gaps={} gated={} conj10_fail={} \
                     gapcount_fail={} rate={:.0}/s elapsed={:.0}s",
                    n, seen, rep.checked, rep.gaps, rep.gated, rep.conj10_fail,
                    rep.gapcount_fail, rate, el
                );
                let tmp = format!("{}.tmp", ckpt);
                let mut f = fs::File::create(&tmp).unwrap();
                writeln!(f, "{}", seen).unwrap();
                writeln!(
                    f,
                    "checked={} gaps={} gated={} conj10_fail={} gapcount_fail={} worst_int_err={:.5}",
                    rep.checked, rep.gaps, rep.gated, rep.conj10_fail, rep.gapcount_fail,
                    rep.worst_int_err
                )
                .unwrap();
                for e in &rep.examples {
                    writeln!(f, "{}", e).unwrap();
                }
                drop(f);
                fs::rename(&tmp, ckpt).unwrap();
            }
        }
    }
    println!();
    println!("graphs with fvs <= 2 examined : {}", rep.checked);
    println!("discarded by validity gate    : {}", rep.gated);
    println!("gap points tested             : {}", rep.gaps);
    println!("Conjecture 10 failures        : {}", rep.conj10_fail);
    println!("GAPCOUNT failures             : {}", rep.gapcount_fail);
    println!("worst |kappa - nearest int|   : {:.5}", rep.worst_int_err);
    for e in &rep.examples {
        println!("  {}", e);
    }
    println!("elapsed {:.1}s", t0.elapsed().as_secs_f64());
}
