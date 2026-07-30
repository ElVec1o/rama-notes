// Is the lower band edge -2 sqrt(m) asymptotically sharp?
//
// Setting: G is (a,b)-biregular bipartite, mu_G(x) = x^(q-p) f_G(x^2), c = (a-1)+(b-1),
// g(z) = f_G(z+c), m = (a-1)(b-1).  Conjecture: every root rho of g has |rho| <= 2 sqrt(m).
// Question: does the least root of g reach -2 sqrt(m) asymptotically along a family of
// increasing girth/size?
//
// Family: bipartite circulants B(n,S), left i ~ right (i+k) mod n for k in S.
// S = {0,1,3} is a Sidon set, so no C_4 and girth >= 6 for every n >= 7; n = 7 is Heawood.
// Control: S = {0,1,2}, which does have C_4.
//
// ALGORITHM.  Transfer matrix / frontier DP along the cyclic order, NOT subset memoization.
// Every edge joins L_i to R_{i+k}, k in S, so the graph has bandwidth w = max(S).
// State entering column i = matched/unmatched status of L_{i-w},...,L_{i-1}: w bits.
// At column i we introduce L_i (unmatched) and process R_i, whose neighbours are L_{i-k},
// k in S; then L_{i-w} leaves the frontier for good.  The state exiting column n-1 carries
// exactly the same vertices L_{n-w},...,L_{n-1} as the state entering column 0, so the number
// of k-matchings of the cyclic graph is the trace of the n-th power of the transfer matrix:
// run the DP once per boundary state s0 and keep the s0 -> s0 entry.
//   MEMORY: 2^w * (n+1) big integers, w in {2,3}.  Nothing of size 2^n is ever allocated.
//
// ROOT FINDING.  Exact.  f is real-rooted (roots = squares of matching-polynomial roots), so
// Descartes' rule of signs is an equality: the number of roots of f above A/2^t equals the
// number of sign changes in the coefficients of the integer polynomial
//    f~(u+A),   f~(u) = 2^(t*p) f(u/2^t) = sum_i f_i u^i 2^(t(p-i)).
// Bisecting on that count locates the least and the greatest root with a certificate, in
// exact integer arithmetic; f64 evaluation of f would lose 20+ digits to cancellation.

use std::cmp::Ordering;
use std::time::Instant;

// ============================ unsigned magnitudes ============================
type Mag = Vec<u64>; // little-endian base 2^64, no leading zero words, empty = 0

fn mag_trim(a: &mut Mag) {
    while a.last() == Some(&0) {
        a.pop();
    }
}

fn mag_cmp(a: &[u64], b: &[u64]) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}

fn mag_addto(d: &mut Mag, s: &[u64]) {
    if s.is_empty() {
        return;
    }
    if d.len() < s.len() {
        d.resize(s.len(), 0);
    }
    let mut carry = 0u64;
    for i in 0..s.len() {
        let (x, c1) = d[i].overflowing_add(s[i]);
        let (y, c2) = x.overflowing_add(carry);
        d[i] = y;
        carry = (c1 as u64) + (c2 as u64);
    }
    let mut i = s.len();
    while carry > 0 {
        if i == d.len() {
            d.push(0);
        }
        let (x, c1) = d[i].overflowing_add(carry);
        d[i] = x;
        carry = c1 as u64;
        i += 1;
    }
}

fn mag_sub(a: &[u64], b: &[u64]) -> Mag {
    // requires a >= b
    let mut r = Vec::with_capacity(a.len());
    let mut borrow = 0u64;
    for i in 0..a.len() {
        let bi = *b.get(i).unwrap_or(&0);
        let (x, c1) = a[i].overflowing_sub(bi);
        let (y, c2) = x.overflowing_sub(borrow);
        r.push(y);
        borrow = (c1 as u64) + (c2 as u64);
    }
    mag_trim(&mut r);
    r
}

fn mag_mul_u64_into(a: &[u64], k: u64, out: &mut Mag) {
    out.clear();
    if a.is_empty() || k == 0 {
        return;
    }
    let mut carry = 0u128;
    for i in 0..a.len() {
        let t = (a[i] as u128) * (k as u128) + carry;
        out.push(t as u64);
        carry = t >> 64;
    }
    if carry > 0 {
        out.push(carry as u64);
    }
    mag_trim(out);
}

fn mag_shl(a: &[u64], bits: usize) -> Mag {
    if a.is_empty() {
        return vec![];
    }
    let words = bits / 64;
    let sh = bits % 64;
    let mut r = vec![0u64; words];
    if sh == 0 {
        r.extend_from_slice(a);
    } else {
        let mut carry = 0u64;
        for &x in a {
            r.push((x << sh) | carry);
            carry = x >> (64 - sh);
        }
        if carry > 0 {
            r.push(carry);
        }
    }
    mag_trim(&mut r);
    r
}

fn mag_to_dec(a: &[u64]) -> String {
    if a.is_empty() {
        return "0".into();
    }
    let mut t = a.to_vec();
    let mut parts: Vec<u64> = vec![];
    const D: u128 = 10_000_000_000_000_000_000;
    while !t.is_empty() {
        let mut rem = 0u128;
        let mut q = vec![0u64; t.len()];
        for i in (0..t.len()).rev() {
            let cur = (rem << 64) | (t[i] as u128);
            q[i] = (cur / D) as u64;
            rem = cur % D;
        }
        mag_trim(&mut q);
        parts.push(rem as u64);
        t = q;
    }
    let mut s = format!("{}", parts.pop().unwrap());
    while let Some(p) = parts.pop() {
        s.push_str(&format!("{:019}", p));
    }
    s
}

// ============================ signed integers ============================
#[derive(Clone)]
struct Int {
    neg: bool,
    m: Mag,
}

impl Int {
    fn zero() -> Int {
        Int { neg: false, m: vec![] }
    }
    fn is_zero(&self) -> bool {
        self.m.is_empty()
    }
    fn sign(&self) -> i32 {
        if self.m.is_empty() {
            0
        } else if self.neg {
            -1
        } else {
            1
        }
    }
    fn shl(&self, b: usize) -> Int {
        let m = mag_shl(&self.m, b);
        Int { neg: self.neg && !m.is_empty(), m }
    }
    fn to_dec(&self) -> String {
        if self.is_zero() {
            "0".into()
        } else if self.neg {
            format!("-{}", mag_to_dec(&self.m))
        } else {
            mag_to_dec(&self.m)
        }
    }
}

// dst += src * k   (k >= 0)
fn int_addmul(dst: &mut Int, src: &Int, k: u64, scratch: &mut Mag) {
    if k == 0 || src.is_zero() {
        return;
    }
    mag_mul_u64_into(&src.m, k, scratch);
    if dst.is_zero() {
        dst.neg = src.neg;
        dst.m.clear();
        dst.m.extend_from_slice(scratch);
        return;
    }
    if dst.neg == src.neg {
        mag_addto(&mut dst.m, scratch);
    } else {
        match mag_cmp(&dst.m, scratch) {
            Ordering::Greater => {
                dst.m = mag_sub(&dst.m, scratch);
            }
            Ordering::Less => {
                dst.m = mag_sub(scratch, &dst.m);
                dst.neg = src.neg;
            }
            Ordering::Equal => {
                dst.m.clear();
                dst.neg = false;
            }
        }
    }
    if dst.m.is_empty() {
        dst.neg = false;
    }
}

// ============================ the transfer-matrix DP ============================
// m_k = number of k-matchings of the bipartite circulant B(n,S), k = 0..n.
fn matchings_transfer(n: usize, s: &[usize]) -> Vec<Mag> {
    let w = *s.iter().max().unwrap();
    assert!(w >= 1, "connection set must not be {{0}}");
    assert!(n > w, "need n > max(S) for the frontier to hold distinct vertices");
    let ns = 1usize << w;
    let mut tot: Vec<Mag> = vec![vec![]; n + 1];
    for s0 in 0..ns {
        let mut dp: Vec<Vec<Mag>> = vec![vec![vec![]; n + 1]; ns];
        dp[s0][0] = vec![1u64];
        for col in 0..n {
            let kmax = col.min(n); // at most `col` edges chosen so far
            let mut nd: Vec<Vec<Mag>> = vec![vec![vec![]; n + 1]; ns];
            for st in 0..ns {
                let base = (st >> 1) & (ns - 1); // drop L_{i-w}, shift down, L_i bit = 0
                for k in 0..=kmax {
                    if dp[st][k].is_empty() {
                        continue;
                    }
                    // R_i left unmatched
                    mag_addto(&mut nd[base][k], &dp[st][k]);
                    if k == n {
                        continue;
                    }
                    // R_i matched to L_{i-kk}
                    for &kk in s {
                        let t = if kk == 0 {
                            base | (1 << (w - 1)) // L_i newly matched
                        } else {
                            let bit = w - kk;
                            if (st >> bit) & 1 == 1 {
                                continue; // already matched
                            }
                            ((st | (1 << bit)) >> 1) & (ns - 1)
                        };
                        mag_addto(&mut nd[t][k + 1], &dp[st][k]);
                    }
                }
            }
            dp = nd;
        }
        for k in 0..=n {
            let v = std::mem::take(&mut dp[s0][k]);
            mag_addto(&mut tot[k], &v);
        }
    }
    tot
}

// ============================ independent brute force ============================
// Plain DFS over matchings: O(#vertices) memory, no subset table at all.
fn matchings_brute(n: usize, s: &[usize]) -> Vec<u128> {
    let nv = 2 * n;
    assert!(nv <= 64);
    let mut adj = vec![0u64; nv];
    for i in 0..n {
        for &k in s {
            let j = n + (i + k) % n;
            adj[i] |= 1u64 << j;
            adj[j] |= 1u64 << i;
        }
    }
    fn go(used: u64, k: usize, nv: usize, adj: &[u64], res: &mut Vec<u128>) {
        let mut u = 0usize;
        while u < nv && (used >> u) & 1 == 1 {
            u += 1;
        }
        if u == nv {
            res[k] += 1;
            return;
        }
        go(used | (1u64 << u), k, nv, adj, res); // u left unmatched
        let mut nb = adj[u] & !used;
        while nb != 0 {
            let x = nb.trailing_zeros() as usize;
            nb &= nb - 1;
            go(used | (1u64 << u) | (1u64 << x), k + 1, nv, adj, res);
        }
    }
    let mut res = vec![0u128; n + 1];
    go(0, 0, nv, &adj, &mut res);
    res
}

// ============================ polynomials ============================
// f_G(y): mu_G(x) = sum_k (-1)^k m_k x^(2n-2k) = f_G(x^2), so f[i] = (-1)^(p-i) m_{p-i}.
fn build_f(mk: &[Mag], p: usize) -> Vec<Int> {
    (0..=p)
        .map(|i| {
            let k = p - i;
            Int { neg: k % 2 == 1 && !mk[k].is_empty(), m: mk[k].clone() }
        })
        .collect()
}

// Taylor shift: returns the coefficients of h(z) = f(z + c).
fn taylor_shift(f: &[Int], c: u64) -> Vec<Int> {
    let p = f.len() - 1;
    let mut a = f.to_vec();
    let mut sc = Mag::new();
    for i in 0..p {
        for j in (i..p).rev() {
            let (l, r) = a.split_at_mut(j + 1);
            int_addmul(&mut l[j], &r[0], c, &mut sc);
        }
    }
    a
}

// Number of roots of f strictly greater than a/2^t.  Exact, given that f is real-rooted.
fn count_gt(f: &[Int], a: u64, t: usize) -> usize {
    let p = f.len() - 1;
    let mut c: Vec<Int> = (0..=p).map(|i| f[i].shl(t * (p - i))).collect();
    let mut sc = Mag::new();
    if a > 0 {
        for i in 0..p {
            for j in (i..p).rev() {
                let (l, r) = c.split_at_mut(j + 1);
                int_addmul(&mut l[j], &r[0], a, &mut sc);
            }
        }
    }
    let mut v = 0usize;
    let mut last = 0i32;
    for ci in c.iter() {
        let s = ci.sign();
        if s != 0 {
            if last != 0 && s != last {
                v += 1;
            }
            last = s;
        }
    }
    v
}

// Least root: the largest A with count_gt(A) == p.  Returns the bracket (A, A+1)/2^t.
fn least_root(f: &[Int], t: usize, top: u64) -> (u64, u64) {
    let p = f.len() - 1;
    let mut lo = 0u64;
    let mut hi = top << t;
    assert_eq!(count_gt(f, lo, t), p, "f has a nonpositive root (no perfect matching?)");
    assert!(count_gt(f, hi, t) < p, "bracket too small");
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if count_gt(f, mid, t) == p {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    (lo, hi)
}

// Greatest root: the smallest A with count_gt(A) == 0.
fn greatest_root(f: &[Int], t: usize, top: u64) -> (u64, u64) {
    let mut lo = 0u64;
    let mut hi = top << t;
    assert_eq!(count_gt(f, hi, t), 0, "bracket too small");
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if count_gt(f, mid, t) == 0 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    (lo, hi)
}

// ============================ graph facts ============================
fn c4_count(n: usize, s: &[usize]) -> u128 {
    // pairs of left vertices at difference d share r(d) right neighbours
    let mut r = vec![0u128; n];
    for &k in s {
        for &kp in s {
            r[(k + n - kp) % n] += 1;
        }
    }
    let mut tot = 0u128;
    for d in 1..n {
        tot += r[d] * (r[d] - 1) / 2;
    }
    (n as u128) * tot / 2
}

fn connected(n: usize, s: &[usize]) -> bool {
    let nv = 2 * n;
    let mut adj = vec![vec![]; nv];
    for i in 0..n {
        for &k in s {
            let j = n + (i + k) % n;
            adj[i].push(j);
            adj[j].push(i);
        }
    }
    let mut seen = vec![false; nv];
    let mut st = vec![0usize];
    seen[0] = true;
    let mut cnt = 1;
    while let Some(v) = st.pop() {
        for &u in &adj[v] {
            if !seen[u] {
                seen[u] = true;
                cnt += 1;
                st.push(u);
            }
        }
    }
    cnt == nv
}

fn girth(n: usize, s: &[usize]) -> usize {
    // BFS from left vertex 0 (vertex-transitive on each side; circulant => enough to try 0 and n)
    let nv = 2 * n;
    let mut adj = vec![vec![]; nv];
    for i in 0..n {
        for &k in s {
            let j = n + (i + k) % n;
            adj[i].push(j);
            adj[j].push(i);
        }
    }
    let mut best = usize::MAX;
    for root in [0usize, n] {
        let mut dist = vec![usize::MAX; nv];
        let mut par = vec![usize::MAX; nv];
        dist[root] = 0;
        let mut q = std::collections::VecDeque::new();
        q.push_back(root);
        while let Some(v) = q.pop_front() {
            for &u in &adj[v] {
                if dist[u] == usize::MAX {
                    dist[u] = dist[v] + 1;
                    par[u] = v;
                    q.push_back(u);
                } else if u != par[v] {
                    best = best.min(dist[u] + dist[v] + 1);
                }
            }
        }
    }
    best
}

// ============================ analysis ============================
struct Row {
    n: usize,
    ymin: f64,
    ymax: f64,
    rho_min: f64,
    rho_max: f64,
    pct_lo: f64,
    pct_hi: f64,
    c4: u128,
    girth: usize,
    ymin_lo: f64,
    ymin_hi: f64,
}

const T: usize = 44; // dyadic denominator 2^44 ~ 5.7e-14 absolute resolution in y

fn analyze(n: usize, s: &[usize], a: usize, b: usize) -> (Row, Vec<Mag>) {
    let mk = matchings_transfer(n, s);
    let p = n;
    let f = build_f(&mk, p);
    let c = ((a - 1) + (b - 1)) as f64;
    let m = ((a - 1) * (b - 1)) as f64;
    let top = (2.0 * (a.max(b) as f64 - 1.0) * 2.0).ceil() as u64 + 2; // safe upper bound on y
    let (l1, h1) = least_root(&f, T, top);
    let (l2, h2) = greatest_root(&f, T, top);
    let sc = (1u64 << T) as f64;
    let ymin = 0.5 * (l1 as f64 + h1 as f64) / sc;
    let ymax = 0.5 * (l2 as f64 + h2 as f64) / sc;
    let edge = 2.0 * m.sqrt();
    let row = Row {
        n,
        ymin,
        ymax,
        rho_min: ymin - c,
        rho_max: ymax - c,
        pct_lo: 100.0 * (c - ymin) / edge,
        pct_hi: 100.0 * (ymax - c) / edge,
        c4: c4_count(n, s),
        girth: girth(n, s),
        ymin_lo: l1 as f64 / sc,
        ymin_hi: h1 as f64 / sc,
    };
    (row, mk)
}

fn canon_reflect(s: &[usize]) -> Vec<usize> {
    let w = *s.iter().max().unwrap();
    let mut v: Vec<usize> = s.iter().map(|&k| w - k).collect();
    v.sort();
    v
}

fn main() {
    println!("Bipartite circulants B(n,S): left i ~ right (i+k) mod n, k in S.");
    println!("3-regular, so a = b = 3, c = 4, m = 4, band = [-4, 4].");
    println!("Transfer-matrix DP over a frontier of max(S) bits; no 2^n table anywhere.\n");

    // ---------------- verification ----------------
    println!("=== VERIFICATION ===\n");
    println!("(1) transfer DP vs independent DFS brute force over all matchings");
    for &(n, s) in &[
        (7usize, &[0usize, 1, 3][..]),
        (8, &[0, 1, 3][..]),
        (9, &[0, 1, 3][..]),
        (10, &[0, 1, 3][..]),
        (6, &[0, 1, 2][..]),
        (7, &[0, 1, 2][..]),
        (8, &[0, 1, 2][..]),
        (9, &[0, 1, 2][..]),
        (10, &[0, 1, 2][..]),
        (11, &[0, 1, 2][..]),
    ] {
        let t0 = Instant::now();
        let tm = matchings_transfer(n, s);
        let t1 = t0.elapsed();
        let t0 = Instant::now();
        let bf = matchings_brute(n, s);
        let t2 = t0.elapsed();
        let tv: Vec<String> = tm.iter().map(|x| mag_to_dec(x)).collect();
        let bv: Vec<String> = bf.iter().map(|x| format!("{}", x)).collect();
        let ok = tv == bv;
        println!(
            "   n={:2} S={:?}  {}   (transfer {:?}, brute {:?})",
            n,
            s,
            if ok { "MATCH" } else { "*** MISMATCH ***" },
            t1,
            t2
        );
        if !ok {
            println!("      transfer: {:?}", tv);
            println!("      brute   : {:?}", bv);
            panic!("transfer matrix is wrong");
        }
    }

    println!("\n(2) isomorphism invariances of the DP (different window width / transitions)");
    for &n in &[7usize, 9, 12, 20, 31] {
        for s in [&[0usize, 1, 3][..], &[0, 1, 2][..]] {
            let base = matchings_transfer(n, s);
            let shifted: Vec<usize> = s.iter().map(|&k| k + 1).collect(); // B(n,S+1) ~ B(n,S)
            let refl = canon_reflect(s); //                                 B(n,-S) ~ B(n,S)
            let v1 = matchings_transfer(n, &shifted);
            let v2 = matchings_transfer(n, &refl);
            let ok = base == v1 && base == v2;
            println!(
                "   n={:2} S={:?} vs S+1={:?} (w={}) vs -S={:?}   {}",
                n,
                s,
                shifted,
                shifted.iter().max().unwrap(),
                refl,
                if ok { "MATCH" } else { "*** MISMATCH ***" }
            );
            assert!(ok, "invariance failure");
        }
    }

    println!("\n(3) Descartes root counter on a polynomial with known roots");
    {
        // (y-1)(y-2)(y-5) = y^3 - 8y^2 + 17y - 10
        let f: Vec<Int> = [-10i64, 17, -8, 1]
            .iter()
            .map(|&x| Int {
                neg: x < 0,
                m: if x == 0 { vec![] } else { vec![x.unsigned_abs()] },
            })
            .collect();
        let t = 10usize;
        let q = |y: f64| count_gt(&f, (y * (1u64 << t) as f64) as u64, t);
        println!(
            "   roots {{1,2,5}}: #>0 = {}, #>1.5 = {}, #>3 = {}, #>6 = {}   (expect 3,2,1,0)",
            q(0.0),
            q(1.5),
            q(3.0),
            q(6.0)
        );
        assert_eq!((q(0.0), q(1.5), q(3.0), q(6.0)), (3, 2, 1, 0));
        let (l, h) = least_root(&f, 30, 8);
        println!("   least root bracket = ({:.9}, {:.9})  expect 1", l as f64 / (1u64 << 30) as f64, h as f64 / (1u64 << 30) as f64);
        let (l, h) = greatest_root(&f, 30, 8);
        println!("   greatest root bracket = ({:.9}, {:.9})  expect 5", l as f64 / (1u64 << 30) as f64, h as f64 / (1u64 << 30) as f64);
    }

    println!("\n(4) Heawood graph = B(7,{{0,1,3}}): known [z^(p-4)]g = -126, least root ~ -3.902");
    {
        let (row, mk) = analyze(7, &[0, 1, 3], 3, 3);
        let f = build_f(&mk, 7);
        let g = taylor_shift(&f, 4);
        println!("   m_k = {:?}", mk.iter().map(|x| mag_to_dec(x)).collect::<Vec<_>>());
        println!(
            "   g coefficients [z^p ... z^0] = {:?}",
            g.iter().rev().map(|x| x.to_dec()).collect::<Vec<_>>()
        );
        println!(
            "   [z^(p-1)]={}  [z^(p-2)]={}  [z^(p-3)]={}  [z^(p-4)]={}   (last must be -126)",
            g[6].to_dec(),
            g[5].to_dec(),
            g[4].to_dec(),
            g[3].to_dec()
        );
        assert_eq!(g[3].to_dec(), "-126", "Heawood [z^(p-4)] mismatch");
        println!(
            "   least root of g = {:.6}  ({:.3}% of the lower edge)   greatest = {:.6} ({:.3}%)",
            row.rho_min, row.pct_lo, row.rho_max, row.pct_hi
        );
        println!("   (tree.rs reports -3.902 / 97.5% / 3.196 / 79.9% for the Heawood graph)");
    }
    println!("\n(5) B(7,{{0,1,2}}) should reproduce tree.rs circ7[0,1,2]: min -3.879 (97.0%), max 3.038 (75.9%)");
    {
        let (row, _) = analyze(7, &[0, 1, 2], 3, 3);
        println!(
            "   least root {:.6} ({:.3}%)   greatest {:.6} ({:.3}%)",
            row.rho_min, row.pct_lo, row.rho_max, row.pct_hi
        );
    }
    println!("\n(6) B(6,{{0,1,2}}) should reproduce tree.rs circ6[0,1,2]: min -3.855 (96.4%)");
    {
        let (row, _) = analyze(6, &[0, 1, 2], 3, 3);
        println!(
            "   least root {:.6} ({:.3}%)   greatest {:.6} ({:.3}%)",
            row.rho_min, row.pct_lo, row.rho_max, row.pct_hi
        );
    }

    // ---------------- the tables ----------------
    let ns: Vec<usize> = std::env::args()
        .nth(1)
        .map(|a| a.split(',').map(|x| x.parse().unwrap()).collect())
        .unwrap_or_else(|| {
            vec![7, 8, 9, 10, 11, 12, 15, 20, 25, 30, 40, 50, 60, 80, 100, 125, 150, 200]
        });

    for s in [&[0usize, 1, 3][..], &[0, 1, 2][..]] {
        println!("\n\n=== S = {:?} ===", s);
        println!(
            "  {:>4} {:>5} {:>7} {:>18} {:>10} {:>14} {:>12} {:>12} {:>9}",
            "n", "girth", "C_4", "least root of g", "-2 sqrt m", "% of lower edge", "y_min",
            "n^2*(1-pct)", "time"
        );
        let mut rows: Vec<Row> = vec![];
        for &n in &ns {
            if n <= *s.iter().max().unwrap() {
                println!("  n={} SKIPPED (n must exceed max(S))", n);
                continue;
            }
            // memory guard: 2 * 2^w * (n+1) big integers of ~3n bits
            let w = *s.iter().max().unwrap();
            let bytes = 2usize * (1 << w) * (n + 1) * (3 * n / 8 + 40);
            if bytes > 200_000_000 {
                println!("  n={} SKIPPED (DP would need {} MB)", n, bytes / 1_000_000);
                continue;
            }
            if !connected(n, s) {
                println!("  n={} SKIPPED (disconnected: double roots would break bisection)", n);
                continue;
            }
            let t0 = Instant::now();
            let (row, _) = analyze(n, s, 3, 3);
            let el = t0.elapsed();
            println!(
                "  {:>4} {:>5} {:>7} {:>18.10} {:>10.4} {:>13.5}% {:>12.3e} {:>12.4} {:>8.2}s",
                row.n,
                row.girth,
                row.c4,
                row.rho_min,
                -4.0,
                row.pct_lo,
                row.ymin,
                (row.n * row.n) as f64 * (1.0 - row.pct_lo / 100.0),
                el.as_secs_f64()
            );
            rows.push(row);
        }
        println!("\n  upper edge, same family:");
        println!("  {:>4} {:>18} {:>16} {:>12}", "n", "greatest root of g", "% of upper edge", "y_max");
        for r in &rows {
            println!("  {:>4} {:>18.10} {:>15.5}% {:>12.8}", r.n, r.rho_max, r.pct_hi, r.ymax);
        }
        println!("\n  exact certified brackets for y_min (dyadic, denominator 2^{}):", T);
        for r in &rows {
            println!(
                "  n={:>4}  y_min in ({:.16}, {:.16})   sqrt(y_min)*n = {:.6}",
                r.n,
                r.ymin_lo,
                r.ymin_hi,
                r.ymin.sqrt() * r.n as f64
            );
        }
    }
}
