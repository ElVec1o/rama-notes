//! Does the split criterion ever fail?
//!
//! At a point x lying in a gap of spec(T), let K be the set of bands of the maximal abelian
//! cover whose range contains x, and put
//!
//!     pi(z) = prod_{k in K} (x - lambda_k(z)),   w(z) = |prod_{k not in K} (x - lambda_k(z))|.
//!
//! The factors outside K never vanish, so their product has a constant sign s and
//! mu_G(x) = s * integral of pi w. Splitting pi into positive and negative parts and bounding
//! w by its extremes in each term separately,
//!
//!     J_+ / J_-  >  Lambda := sup(w) / inf(w)
//!
//! is sufficient for mu_G(x) != 0, with no hypothesis on |K|. That is
//! CrossingSplit.ne_zero_of_split. This program looks for a point where it fails, and
//! measures the two halves separately: J_+/J_- is band geometry, Lambda is the weight.
//!
//! The Python version of this sweep covered 1708 graphs in 100 minutes, which was a Rule 8
//! violation. This is the Rust replacement, with progress, ETA, atomic checkpoints and
//! resume, and it reaches n = 8 where the Python stopped at 7.
//!
//! Eigenvalues of the n by n Hermitian A + iB come from the real symmetric 2n by 2n
//! [[A, -B], [B, A]], whose spectrum is that of the Hermitian matrix with every value
//! doubled. That embedding costs a factor eight over a complex Jacobi but is far harder to
//! get wrong, and correctness matters more here than speed.

use std::fs;
use std::io::Write;
use std::time::Instant;

const GRID: usize = 900; // energies in the cavity scan
const MAXIT: usize = 2000;
const TOL: f64 = 1e-11;
const ETAS: [f64; 3] = [1e-4, 1e-3, 1e-2];
const QUOTA: usize = 9000; // graphs sampled per vertex count
const GAP_MIN: f64 = 0.08;
const FRACS: [f64; 7] = [0.05, 0.2, 0.35, 0.5, 0.65, 0.8, 0.95];
const CKPT: &str = "private/jsweep_ckpt.txt";

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
    fn inv(self) -> C {
        let d = (self.re * self.re + self.im * self.im).max(1e-300);
        C::new(self.re / d, -self.im / d)
    }
}

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
    let mut c = n;
    for &(u, v) in edges {
        if uf.union(u, v) {
            c -= 1;
        }
    }
    c == 1
}

/// Cotree edge indices for a spanning tree grown greedily.
fn cotree(n: usize, edges: &[(usize, usize)]) -> Vec<usize> {
    let mut uf = Uf::new(n);
    let mut cot = Vec::new();
    for (i, &(u, v)) in edges.iter().enumerate() {
        if !uf.union(u, v) {
            cot.push(i);
        }
    }
    cot
}

// ---------------------------------------------------------------- universal cover

struct Adj {
    de: Vec<(usize, usize)>,
    idx: Vec<Vec<i32>>,
    nbr: Vec<Vec<usize>>,
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
    Adj { de, idx, nbr }
}

/// Non-backtracking cavity density of states at e + i eta, warm started from `h`.
fn density(a: &Adj, n: usize, e: f64, eta: f64, h: &mut Vec<C>) -> f64 {
    let z = C::new(e, eta);
    let mut new = vec![C::new(0.0, 0.0); a.de.len()];
    for _ in 0..MAXIT {
        let mut diff = 0.0f64;
        for k in 0..a.de.len() {
            let (u, v) = a.de[k];
            let mut s = z;
            for &w in &a.nbr[v] {
                if w == u {
                    continue;
                }
                let j = a.idx[v][w] as usize;
                s = s.sub(h[j]);
            }
            let val = s.inv();
            diff = diff.max((val.re - h[k].re).abs().max((val.im - h[k].im).abs()));
            new[k] = val;
        }
        h.copy_from_slice(&new);
        if diff < TOL {
            break;
        }
    }
    let mut acc = 0.0;
    for u in 0..n {
        let mut s = z;
        for &w in &a.nbr[u] {
            s = s.sub(h[a.idx[u][w] as usize]);
        }
        acc += s.inv().im;
    }
    -acc / (std::f64::consts::PI * n as f64)
}

fn scan(a: &Adj, n: usize, lo: f64, hi: f64, eta: f64) -> (Vec<f64>, Vec<f64>) {
    let mut h = vec![C::new(0.0, -0.1); a.de.len()];
    let (mut es, mut ds) = (Vec::with_capacity(GRID + 1), Vec::with_capacity(GRID + 1));
    for i in 0..=GRID {
        let e = hi - (hi - lo) * i as f64 / GRID as f64;
        let d = density(a, n, e, eta, &mut h);
        es.push(e);
        ds.push(d.max(0.0));
    }
    es.reverse();
    ds.reverse();
    (es, ds)
}

fn bands(es: &[f64], ds: &[f64], thresh: f64) -> Vec<(f64, f64)> {
    let mut out = Vec::new();
    let (mut inb, mut start) = (false, 0.0);
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

// ---------------------------------------------------------------- eigenvalues

/// Eigenvalues of a real symmetric matrix by cyclic Jacobi, no eigenvectors.
/// `m` is dim by dim in row-major order and is destroyed.
fn jacobi(m: &mut [f64], dim: usize, out: &mut Vec<f64>) {
    for _ in 0..60 {
        let mut off = 0.0;
        for p in 0..dim {
            for q in (p + 1)..dim {
                off += m[p * dim + q] * m[p * dim + q];
            }
        }
        if off < 1e-22 {
            break;
        }
        for p in 0..dim {
            for q in (p + 1)..dim {
                let apq = m[p * dim + q];
                if apq.abs() < 1e-18 {
                    continue;
                }
                let theta = (m[q * dim + q] - m[p * dim + p]) / (2.0 * apq);
                let t = if theta >= 0.0 {
                    1.0 / (theta + (theta * theta + 1.0).sqrt())
                } else {
                    -1.0 / (-theta + (theta * theta + 1.0).sqrt())
                };
                let c = 1.0 / (t * t + 1.0).sqrt();
                let s = t * c;
                for k in 0..dim {
                    let akp = m[k * dim + p];
                    let akq = m[k * dim + q];
                    m[k * dim + p] = c * akp - s * akq;
                    m[k * dim + q] = s * akp + c * akq;
                }
                for k in 0..dim {
                    let apk = m[p * dim + k];
                    let aqk = m[q * dim + k];
                    m[p * dim + k] = c * apk - s * aqk;
                    m[q * dim + k] = s * apk + c * aqk;
                }
            }
        }
    }
    out.clear();
    for i in 0..dim {
        out.push(m[i * dim + i]);
    }
    out.sort_by(|a, b| a.partial_cmp(b).unwrap());
}

/// Eigenvalues of the n by n Hermitian matrix given as (re, im) row-major, via the real
/// symmetric 2n by 2n embedding [[A, -B], [B, A]]; every eigenvalue appears twice.
fn herm_eigvals(re: &[f64], im: &[f64], n: usize, buf: &mut Vec<f64>, ev: &mut Vec<f64>,
                out: &mut Vec<f64>) {
    let d = 2 * n;
    buf.clear();
    buf.resize(d * d, 0.0);
    for i in 0..n {
        for j in 0..n {
            buf[i * d + j] = re[i * n + j];
            buf[(i + n) * d + (j + n)] = re[i * n + j];
            buf[i * d + (j + n)] = -im[i * n + j];
            buf[(i + n) * d + j] = im[i * n + j];
        }
    }
    jacobi(buf, d, ev);
    out.clear();
    let mut k = 0;
    while k < d {
        out.push(0.5 * (ev[k] + ev[k + 1]));
        k += 2;
    }
}

// ---------------------------------------------------------------- the sweep

struct Rep {
    graphs: usize,
    points: usize,
    fires: usize,
    worst_margin: f64,
    worst_true: f64,
    kap: Vec<usize>,
    kap_fire: Vec<usize>,
    worst_at: String,
}

fn examine(n: usize, edges: &[(usize, usize)], b: usize, rep: &mut Rep) {
    let a = build_adj(n, edges);
    let mut got = None;
    for &eta in ETAS.iter() {
        let (es, ds) = scan(&a, n, -5.5, 5.5, eta);
        if (kappa_above(&es, &ds, 1, -5.5) - 1.0).abs() <= 0.03 {
            got = Some((es, ds));
            break;
        }
    }
    let (es, ds) = match got {
        Some(x) => x,
        None => return,
    };
    let bs = bands(&es, &ds, 1e-3);
    let mut internal = Vec::new();
    for i in 0..bs.len().saturating_sub(1) {
        if bs[i + 1].0 - bs[i].1 > GAP_MIN {
            internal.push((bs[i].1, bs[i + 1].0));
        }
    }
    if internal.is_empty() {
        return;
    }

    // band spectra on the torus grid, computed once for the graph
    let steps: usize = if b == 2 { 64 } else { 20 };
    let total: usize = steps.pow(b as u32);
    let cot = cotree(n, edges);
    let mut lam = vec![0.0f64; total * n];
    let (mut re, mut im) = (vec![0.0; n * n], vec![0.0; n * n]);
    let (mut buf, mut ev, mut vals) = (Vec::new(), Vec::new(), Vec::new());
    for t in 0..total {
        for x in re.iter_mut() {
            *x = 0.0;
        }
        for x in im.iter_mut() {
            *x = 0.0;
        }
        for (i, &(u, v)) in edges.iter().enumerate() {
            let (mut cr, mut ci) = (1.0, 0.0);
            if let Some(j) = cot.iter().position(|&c| c == i) {
                let th = 2.0 * std::f64::consts::PI
                    * ((t / steps.pow(j as u32)) % steps) as f64
                    / steps as f64;
                cr = th.cos();
                ci = th.sin();
            }
            re[u * n + v] += cr;
            im[u * n + v] += ci;
            re[v * n + u] += cr;
            im[v * n + u] -= ci;
        }
        herm_eigvals(&re, &im, n, &mut buf, &mut ev, &mut vals);
        lam[t * n..t * n + n].copy_from_slice(&vals);
    }
    let mut lo = vec![f64::INFINITY; n];
    let mut hi = vec![f64::NEG_INFINITY; n];
    for t in 0..total {
        for k in 0..n {
            lo[k] = lo[k].min(lam[t * n + k]);
            hi[k] = hi[k].max(lam[t * n + k]);
        }
    }

    for &(g0, g1) in internal.iter() {
        for &f in FRACS.iter() {
            let x = g0 + f * (g1 - g0);
            let cross: Vec<usize> = (0..n).filter(|&k| lo[k] <= x && x <= hi[k]).collect();
            let kap = cross.len();
            if kap == 0 {
                continue; // settled by the localization
            }
            let (mut jp, mut jm, mut ip, mut im_, mut wlo, mut whi) =
                (0.0f64, 0.0f64, 0.0f64, 0.0f64, f64::INFINITY, 0.0f64);
            let mut bad = false;
            for t in 0..total {
                let (mut pi, mut w) = (1.0f64, 1.0f64);
                for k in 0..n {
                    let d = x - lam[t * n + k];
                    if cross.contains(&k) {
                        pi *= d;
                    } else {
                        w *= d;
                    }
                }
                let w = w.abs();
                if w <= 0.0 {
                    bad = true;
                    break;
                }
                wlo = wlo.min(w);
                whi = whi.max(w);
                if pi > 0.0 {
                    jp += pi;
                    ip += pi * w;
                } else {
                    jm += -pi;
                    im_ += -pi * w;
                }
            }
            if bad || jp <= 0.0 || jm <= 0.0 {
                continue;
            }
            let (jp, jm, ip, im_) = if jp >= jm {
                (jp, jm, ip, im_)
            } else {
                (jm, jp, im_, ip)
            };
            let lambda = whi / wlo;
            let margin = (jp / jm) / lambda;
            let truth = im_ / ip;
            rep.points += 1;
            while rep.kap.len() <= kap {
                rep.kap.push(0);
                rep.kap_fire.push(0);
            }
            rep.kap[kap] += 1;
            if margin > 1.0 {
                rep.fires += 1;
                rep.kap_fire[kap] += 1;
            }
            if margin < rep.worst_margin {
                rep.worst_margin = margin;
                rep.worst_at = format!("n={} b={} kap={} x={:.4} edges={:?}", n, b, kap, x, edges);
            }
            rep.worst_true = rep.worst_true.max(truth);
            if truth >= 1.0 {
                println!("  REFUTATION n={} b={} kap={} x={:.5} edges={:?} I-/I+={:.6}",
                         n, b, kap, x, edges, truth);
            }
        }
    }
}

/// All m-subsets of `pairs`, visited in order; calls `f` with the running index.
fn combos(pairs: &[(usize, usize)], m: usize, mut f: impl FnMut(usize, &[(usize, usize)])) {
    let k = pairs.len();
    if m > k {
        return;
    }
    let mut idx: Vec<usize> = (0..m).collect();
    let mut cnt = 0usize;
    let mut cur = vec![(0usize, 0usize); m];
    loop {
        for i in 0..m {
            cur[i] = pairs[idx[i]];
        }
        f(cnt, &cur);
        cnt += 1;
        let mut i = m;
        loop {
            if i == 0 {
                return;
            }
            i -= 1;
            if idx[i] != i + k - m {
                idx[i] += 1;
                for j in (i + 1)..m {
                    idx[j] = idx[j - 1] + 1;
                }
                break;
            }
        }
    }
}

fn count_combos(k: usize, m: usize) -> usize {
    if m > k {
        return 0;
    }
    let mut r = 1u128;
    for i in 0..m {
        r = r * (k - i) as u128 / (i + 1) as u128;
    }
    r as usize
}

fn main() {
    let nmax: usize = std::env::var("NMAX").ok().and_then(|v| v.parse().ok()).unwrap_or(8);
    let resume: usize = fs::read_to_string(CKPT)
        .ok()
        .and_then(|s| s.split_whitespace().next().and_then(|v| v.parse().ok()))
        .unwrap_or(0);
    if resume > 0 {
        println!("resuming after {} graphs", resume);
    }
    let mut rep = Rep {
        graphs: 0,
        points: 0,
        fires: 0,
        worst_margin: f64::INFINITY,
        worst_true: 0.0,
        kap: Vec::new(),
        kap_fire: Vec::new(),
        worst_at: String::new(),
    };

    // plan
    let mut plan = Vec::new();
    for n in 4..=nmax {
        let pairs: Vec<(usize, usize)> =
            (0..n).flat_map(|u| ((u + 1)..n).map(move |v| (u, v))).collect();
        for b in 2..=3usize {
            let m = n + b - 1;
            let tot = count_combos(pairs.len(), m);
            if tot == 0 {
                continue;
            }
            let stride = std::cmp::max(1, tot / QUOTA);
            plan.push((n, b, m, stride, tot / stride));
        }
    }
    let planned: usize = plan.iter().map(|p| p.4).sum();
    println!("plan: {} graph slots over n = 4..{}", planned, nmax);
    let _ = std::io::stdout().flush();
    for p in &plan {
        println!("  n={} b={} edges={} stride={} slots={}", p.0, p.1, p.2, p.3, p.4);
    }

    let t0 = Instant::now();
    let mut seen = 0usize;
    for &(n, b, m, stride, _) in plan.iter() {
        let pairs: Vec<(usize, usize)> =
            (0..n).flat_map(|u| ((u + 1)..n).map(move |v| (u, v))).collect();
        combos(&pairs, m, |i, e| {
            if i % stride != 0 {
                return;
            }
            seen += 1;
            if seen <= resume {
                return;
            }
            if !connected(n, e) {
                return;
            }
            rep.graphs += 1;
            examine(n, e, b, &mut rep);
            if rep.graphs % 500 == 0 {
                let el = t0.elapsed().as_secs_f64();
                let rate = rep.graphs as f64 / el;
                println!(
                    "  {}/{}  pts {}  fires {}  worst margin {:.4}  worst I-/I+ {:.5}  \
                     {:.0}s  ETA {:.1}min",
                    seen, planned, rep.points, rep.fires, rep.worst_margin, rep.worst_true,
                    el, (planned - seen) as f64 / rate / 60.0
                );
                let tmp = format!("{}.tmp", CKPT);
                if let Ok(mut fh) = fs::File::create(&tmp) {
                    let _ = writeln!(
                        fh, "{} points={} fires={} worst_margin={:.6} worst_true={:.6}",
                        seen, rep.points, rep.fires, rep.worst_margin, rep.worst_true
                    );
                }
                let _ = fs::rename(&tmp, CKPT);
                let _ = std::io::stdout().flush();
            }
        });
    }

    println!("\ngraphs examined   : {}", rep.graphs);
    println!("residue points    : {}", rep.points);
    println!("criterion fires   : {}/{}", rep.fires, rep.points);
    println!("worst margin      : {:.6}   (must exceed 1)", rep.worst_margin);
    println!("  attained at     : {}", rep.worst_at);
    println!("worst true I-/I+  : {:.6}   (1 would refute Conjecture 10)", rep.worst_true);
    for k in 1..rep.kap.len() {
        if rep.kap[k] > 0 {
            println!("  kappa={}: {} points, fires {}", k, rep.kap[k], rep.kap_fire[k]);
        }
    }
}
