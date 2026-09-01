// (3,4)-biregular search for a zero of mu_G inside the spectral gap of the universal cover.
// See README.md. Nothing floating point enters a verdict.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::fs::File;
use std::io::Write;
use std::time::Instant;

// ---------------------------------------------------------------- rng (xorshift, reproducible)
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        self.0 = x; x
    }
    fn below(&mut self, n: usize) -> usize { (self.next() % (n as u64)) as usize }
}

// ---------------------------------------------------------------- bipartite graph, A side deg 4
#[derive(Clone)]
struct Bip { a: usize, b: usize, nb: Vec<Vec<usize>> } // nb[j] = neighbours in A of B-vertex j

impl Bip {
    fn n(&self) -> usize { self.a + self.b }
    fn connected(&self) -> bool {
        // BFS on A u B, A vertices 0..a, B vertices a..a+b
        let mut adj = vec![Vec::new(); self.n()];
        for (j, ns) in self.nb.iter().enumerate() {
            for &i in ns { adj[i].push(self.a + j); adj[self.a + j].push(i); }
        }
        let mut seen = vec![false; self.n()];
        let mut st = vec![0usize]; seen[0] = true; let mut c = 1;
        while let Some(v) = st.pop() {
            for &w in &adj[v] { if !seen[w] { seen[w] = true; c += 1; st.push(w); } }
        }
        c == self.n()
    }
    fn degrees_ok(&self) -> bool {
        let mut d = vec![0usize; self.a];
        for ns in &self.nb {
            if ns.len() != 3 { return false; }
            for &i in ns { d[i] += 1; }
        }
        d.iter().all(|&x| x == 4)
    }
}

// ---------------------------------------------------------------- exact matching counts
// m_k = number of k-matchings. DP over subsets of the A side, B vertices processed in order.
fn matching_counts(g: &Bip) -> Vec<i128> {
    let full = 1usize << g.a;
    let mut dp = vec![0i128; full];
    dp[0] = 1;
    for ns in &g.nb {
        let mut nd = dp.clone(); // B-vertex left unmatched
        for s in 0..full {
            let v = dp[s];
            if v == 0 { continue; }
            for &i in ns {
                if s & (1 << i) == 0 { nd[s | (1 << i)] += v; }
            }
        }
        dp = nd;
    }
    let mut m = vec![0i128; g.a + 1];
    for s in 0..full { if dp[s] != 0 { m[(s as u32).count_ones() as usize] += dp[s]; } }
    m
}

// brute force k-matchings, for the self-test only
fn matching_counts_brute(g: &Bip) -> Vec<i128> {
    let mut edges = Vec::new();
    for (j, ns) in g.nb.iter().enumerate() { for &i in ns { edges.push((i, g.a + j)); } }
    let mut m = vec![0i128; g.a + 1];
    let e = edges.len();
    for mask in 0u64..(1u64 << e) {
        let mut used = vec![false; g.n()];
        let mut ok = true; let mut k = 0;
        for t in 0..e {
            if mask >> t & 1 == 1 {
                let (u, v) = edges[t];
                if used[u] || used[v] { ok = false; break; }
                used[u] = true; used[v] = true; k += 1;
            }
        }
        if ok { m[k] += 1; }
    }
    m
}

// ---------------------------------------------------------------- Q(y), roots are the squares
// mu_G = sum_k (-1)^k m_k x^(n-2k) = x^(n-2nu) * Q(x^2),  Q(y) = sum_j (-1)^(nu-j) m_(nu-j) y^j
fn q_poly(m: &[i128]) -> Vec<BigInt> {
    let nu = (0..m.len()).rev().find(|&k| m[k] != 0).unwrap();
    (0..=nu).map(|j| {
        let c = BigInt::from(m[nu - j]);
        if (nu - j) % 2 == 0 { c } else { -c }
    }).collect()
}

fn deriv(p: &[BigInt]) -> Vec<BigInt> {
    if p.len() <= 1 { return vec![BigInt::zero()]; }
    (1..p.len()).map(|i| &p[i] * BigInt::from(i)).collect()
}

/// sign of P(num/den) for den > 0, computed exactly as sign of sum_i c_i num^i den^(D-i)
fn sign_at(p: &[BigInt], num: &BigInt, den: &BigInt) -> i32 {
    let d = p.len() - 1;
    let mut acc = BigInt::zero();
    let mut npow = BigInt::one();               // num^i
    let mut dpow = vec![BigInt::one(); d + 1];  // den^(d-i)
    for i in 1..=d { dpow[i] = &dpow[i - 1] * den; }
    for i in 0..=d {
        acc += &p[i] * &npow * &dpow[d - i];
        npow *= num;
    }
    if acc.is_zero() { 0 } else if acc.is_positive() { 1 } else { -1 }
}

fn variations(signs: &[i32]) -> usize {
    let mut v = 0; let mut last = 0;
    for &s in signs {
        if s == 0 { continue; }
        if last != 0 && s != last { v += 1; }
        last = s;
    }
    v
}

/// Budan-Fourier variation count of P at the rational num/den.
fn bf_variations(p: &[BigInt], num: &BigInt, den: &BigInt) -> usize {
    let mut signs = Vec::new();
    let mut cur = p.to_vec();
    loop {
        signs.push(sign_at(&cur, num, den));
        if cur.len() <= 1 { break; }
        cur = deriv(&cur);
    }
    variations(&signs)
}

/// number of roots of Q in (0, num/den], exact because Q is hyperbolic with positive roots.
/// Returns None if the internal consistency check V(0) = deg Q fails.
fn roots_in_low_window(q: &[BigInt], num: &BigInt, den: &BigInt) -> Option<usize> {
    let d = q.len() - 1;
    // V(0): signs of Q^(k)(0) are the signs of the coefficients
    let v0 = variations(&q.iter().map(|c| if c.is_zero() { 0 }
                                     else if c.is_positive() { 1 } else { -1 })
                        .collect::<Vec<_>>());
    if v0 != d { return None; }
    Some(d - bf_variations(q, num, den))
}

/// number of roots of Q strictly above num/den. The complement of spec(T) for the
/// (3,4)-biregular tree has TWO windows, (0, sqrt3-sqrt2) and (sqrt3+sqrt2, infinity), and
/// Heilmann-Lieb only confines the roots of mu_G to |x| < 2 sqrt3 = 3.4641, which exceeds
/// sqrt3+sqrt2 = 3.1463. So the upper window has to be checked, not assumed empty.
/// For a hyperbolic Q with positive roots the Budan-Fourier count V(R) is exactly the number
/// of roots in (R, infinity).
fn roots_in_high_window(q: &[BigInt], num: &BigInt, den: &BigInt) -> usize {
    bf_variations(q, num, den)
}

// ---------------------------------------------------------------- generation
fn subsets3(a: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    for i in 0..a { for j in i + 1..a { for k in j + 1..a { out.push(vec![i, j, k]); } } }
    out
}

/// exhaustive over labelled graphs, B vertices in non-decreasing subset order
fn exhaustive(t: usize, mut f: impl FnMut(&Bip)) {
    let (a, b) = (3 * t, 4 * t);
    let subs = subsets3(a);
    let mut cap = vec![4usize; a];
    let mut chosen: Vec<usize> = Vec::new();
    fn go(start: usize, b: usize, subs: &[Vec<usize>], cap: &mut Vec<usize>,
          chosen: &mut Vec<usize>, a: usize, f: &mut impl FnMut(&Bip)) {
        if chosen.len() == b {
            let g = Bip { a, b, nb: chosen.iter().map(|&s| subs[s].clone()).collect() };
            if g.connected() { f(&g); }
            return;
        }
        let left = b - chosen.len();
        for si in start..subs.len() {
            let s = &subs[si];
            if s.iter().any(|&i| cap[i] == 0) { continue; }
            // prune: remaining capacity must be exactly 3 per remaining B vertex
            for &i in s { cap[i] -= 1; }
            let rem: usize = cap.iter().sum();
            if rem == 3 * (left - 1) {
                chosen.push(si);
                go(si, b, subs, cap, chosen, a, f);
                chosen.pop();
            }
            for &i in s { cap[i] += 1; }
        }
    }
    go(0, b, &subs, &mut cap, &mut chosen, a, &mut f);
}

/// random (3,4)-biregular bipartite graph by stub pairing with rejection
fn random_bip(t: usize, rng: &mut Rng) -> Option<Bip> {
    let (a, b) = (3 * t, 4 * t);
    let mut stubs: Vec<usize> = (0..a).flat_map(|i| std::iter::repeat(i).take(4)).collect();
    for i in (1..stubs.len()).rev() { let j = rng.below(i + 1); stubs.swap(i, j); }
    let mut nb = vec![Vec::new(); b];
    for j in 0..b {
        for s in 0..3 {
            let v = stubs[3 * j + s];
            if nb[j].contains(&v) { return None; }   // multi-edge
            nb[j].push(v);
        }
        nb[j].sort();
    }
    let g = Bip { a, b, nb };
    if g.degrees_ok() && g.connected() { Some(g) } else { None }
}

// ---------------------------------------------------------------- self-test
fn selftest() {
    println!("self-test");
    let mut fail = 0;

    // 1. K_{3,4}: the a=3 side has degree 4, the b=4 side degree 3
    let k34 = Bip { a: 3, b: 4, nb: vec![vec![0, 1, 2]; 4] };
    assert!(k34.degrees_ok() && k34.connected());
    let m = matching_counts(&k34);
    let mb = matching_counts_brute(&k34);
    println!("  K_3,4 matching counts DP    {:?}", m);
    println!("  K_3,4 matching counts brute {:?}", mb);
    if m != mb { println!("  MISMATCH"); fail += 1; }

    // 2. DP vs brute force on random small graphs
    let mut rng = Rng(12345);
    let mut n_ok = 0;
    for _ in 0..4000 {
        if let Some(g) = random_bip(2, &mut rng) {
            if matching_counts(&g) != matching_counts_brute(&g) {
                println!("  DP/brute MISMATCH on a t=2 graph"); fail += 1; break;
            }
            n_ok += 1;
            if n_ok >= 3 { break; }
        }
    }
    println!("  DP vs brute force on {} random t=2 graphs: {}", n_ok,
             if fail == 0 { "AGREE" } else { "MISMATCH" });

    // 3. Budan-Fourier on a polynomial with known roots: (y-1)(y-4) = 4 - 5y + y^2
    let q: Vec<BigInt> = vec![BigInt::from(4), BigInt::from(-5), BigInt::from(1)];
    for (num, den, want) in [(1i64, 1i64, 1usize), (2, 1, 1), (4, 1, 2), (1, 2, 0)] {
        let got = roots_in_low_window(&q, &BigInt::from(num), &BigInt::from(den));
        let ok = got == Some(want);
        println!("  (y-1)(y-4), roots in (0,{}/{}] = {:?}, want {} {}",
                 num, den, got, want, if ok { "OK" } else { "WRONG" });
        if !ok { fail += 1; }
    }

    // 4. end to end on K_{3,4}: smallest positive root of mu should be OUTSIDE the low window,
    //    m = [1,12,36,24] by hand: m_2 = C(12,2) - 3*C(4,2) - 4*C(3,2) = 36, m_3 = 4*3*2 = 24
    let q34 = q_poly(&m);
    println!("  K_3,4 Q coefficients {:?}", q34);
    let (num, den) = (BigInt::from(10099684u64), BigInt::from(100000000u64));
    let hits = roots_in_low_window(&q34, &num, &den);
    println!("  K_3,4 roots of mu in (0, 0.3178): {:?} (expect Some(0))", hits);
    if hits != Some(0) { fail += 1; }

    let hi = roots_in_high_window(&q34, &BigInt::from(98990u64), &BigInt::from(10000u64));
    println!("  K_3,4 roots of mu above sqrt3+sqrt2: {} (expect 0)", hi);
    if hi != 0 { fail += 1; }

    // 5. the window is a strict under-estimate: (3178/10000)^2 < (sqrt3-sqrt2)^2
    let lhs = 3178f64 / 10000.0;
    println!("  window edge {} < sqrt3-sqrt2 = {:.9}: {}", lhs, 3f64.sqrt() - 2f64.sqrt(),
             lhs < 3f64.sqrt() - 2f64.sqrt());
    if !(lhs < 3f64.sqrt() - 2f64.sqrt()) { fail += 1; }

    println!("{}", if fail == 0 { "self-test PASSED" } else { "self-test FAILED" });
    if fail != 0 { std::process::exit(1); }
}

// ---------------------------------------------------------------- main sweep
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--selftest") { selftest(); return; }

    let num = BigInt::from(10099684u64);      // (3178/10000)^2, strictly below (sqrt3-sqrt2)^2
    let den = BigInt::from(100000000u64);
    // (sqrt3+sqrt2)^2 = 5 + 2 sqrt6 = 9.8989794...; 98990/10000 is strictly above it, so a root
    // counted above this really is outside spec(T).
    let hnum = BigInt::from(98990u64);
    let hden = BigInt::from(10000u64);
    let t0 = Instant::now();
    let budget = std::env::var("BUDGET").ok().and_then(|s| s.parse::<f64>().ok())
                 .unwrap_or(3600.0);

    let mut tested: u64 = 0;
    let mut bad_check: u64 = 0;
    let mut hits: Vec<String> = Vec::new();
    let mut last_report = 0.0;

    let mut report = |tested: u64, hits: usize, bad: u64, t: f64, tag: &str| {
        let line = format!("{} tested={} hits={} failed_consistency={} elapsed={:.0}s",
                           tag, tested, hits, bad, t);
        println!("{}", line);
        let _ = std::io::stdout().flush();
        if let Ok(mut f) = File::create("checkpoint.txt") { let _ = writeln!(f, "{}", line); }
    };

    println!("(3,4)-biregular sweep. A root of mu_G in (0, 0.3178) is a counterexample to");
    println!("Conjecture 10 in a class where DegreeBound.lean rules out the Aomoto escape.\n");

    // exhaustive t = 1, 2
    for t in 1..=2usize {
        let mut local = 0u64;
        let mut found: Vec<String> = Vec::new();
        exhaustive(t, |g| {
            let m = matching_counts(g);
            let q = q_poly(&m);
            let hi = roots_in_high_window(&q, &hnum, &hden);
            match roots_in_low_window(&q, &num, &den) {
                None => { bad_check += 1; }
                Some(k) => {
                    if k > 0 || hi > 0 {
                        found.push(format!("t={} n={} low={} high={} nb={:?}", t, g.n(), k, hi, g.nb));
                    }
                }
            }
            local += 1;
        });
        tested += local;
        for f in &found { println!("  HIT {}", f); hits.push(f.clone()); }
        report(tested, hits.len(), bad_check, t0.elapsed().as_secs_f64(),
               &format!("exhaustive t={} (n={}): {} connected labelled graphs;", t, 7 * t, local));
    }

    // random t = 3..
    let mut rng = Rng(0xD3C0FFEE);
    'outer: for t in 3..=6usize {
        let mut local = 0u64;
        loop {
            let el = t0.elapsed().as_secs_f64();
            if el > budget { report(tested, hits.len(), bad_check, el, "[budget reached]"); break 'outer; }
            if let Some(g) = random_bip(t, &mut rng) {
                let m = matching_counts(&g);
                let q = q_poly(&m);
                let hi = roots_in_high_window(&q, &hnum, &hden);
                match roots_in_low_window(&q, &num, &den) {
                    None => { bad_check += 1; }
                    Some(k) => {
                        if k > 0 || hi > 0 {
                            let s = format!("t={} n={} low={} high={} nb={:?}", t, g.n(), k, hi, g.nb);
                            println!("  HIT {}", s); hits.push(s);
                        }
                    }
                }
                tested += 1; local += 1;
            }
            let el = t0.elapsed().as_secs_f64();
            if el - last_report > 20.0 {
                last_report = el;
                let rate = tested as f64 / el.max(1e-9);
                report(tested, hits.len(), bad_check, el,
                       &format!("random t={} (n={}): local={} rate={:.0}/s eta_to_budget={:.0}s;",
                                t, 7 * t, local, rate, (budget - el).max(0.0)));
            }
            if local >= 20000 { break; }
        }
    }

    let el = t0.elapsed().as_secs_f64();
    report(tested, hits.len(), bad_check, el, "TOTAL");
    if !hits.is_empty() {
        let mut f = File::create("hits.json").unwrap();
        writeln!(f, "[").unwrap();
        for (i, h) in hits.iter().enumerate() {
            writeln!(f, " \"{}\"{}", h.replace('"', "'"), if i + 1 == hits.len() { "" } else { "," }).unwrap();
        }
        writeln!(f, "]").unwrap();
        println!("\n  COUNTEREXAMPLE(S) FOUND. A zero of mu_G lies in (0, sqrt3-sqrt2), which is a");
        println!("  gap of spec(T_G) for the (3,4)-biregular tree, and by DegreeBound.lean it");
        println!("  cannot be an eigenvalue. Conjecture D3 is false.");
    } else {
        println!("\n  No zero of mu_G outside spec(T), on every graph tested. Every verdict is");
        println!("  exact, with no floating point in it, but the sweep is a sample: t <= 6");
        println!("  (n <= 42), exhaustive only at t = 1 and t = 2. This is evidence for");
        println!("  Conjecture 10 in the trap-free class, not a proof of it.");
        if bad_check > 0 {
            println!("  WARNING: {} graphs failed the V(0) = deg Q consistency check and were", bad_check);
            println!("  not decided. Investigate before quoting the coverage.");
        }
    }
}
