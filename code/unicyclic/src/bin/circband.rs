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

// ============ generic frontier DP for an arbitrary graph (same idea, any order) ============
struct Graph {
    nv: usize,
    adj: Vec<Vec<usize>>,
}

impl Graph {
    fn new(nv: usize, edges: &[(usize, usize)]) -> Graph {
        let mut adj = vec![vec![]; nv];
        for &(u, v) in edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        for a in adj.iter_mut() {
            a.sort();
            a.dedup();
        }
        Graph { nv, adj }
    }
    fn edges(&self) -> Vec<(usize, usize)> {
        let mut e = vec![];
        for u in 0..self.nv {
            for &v in &self.adj[u] {
                if u < v {
                    e.push((u, v));
                }
            }
        }
        e
    }
}

// slot assignment mimicking the frontier: returns (slot[v], #slots, vertices freed after step i)
fn frontier_plan(g: &Graph, order: &[usize]) -> (Vec<usize>, usize, Vec<Vec<usize>>) {
    let mut pos = vec![0usize; g.nv];
    for (i, &v) in order.iter().enumerate() {
        pos[v] = i;
    }
    let mut slot = vec![usize::MAX; g.nv];
    let mut free: Vec<usize> = vec![];
    let mut used = 0usize;
    let mut live: Vec<usize> = vec![];
    let mut freed: Vec<Vec<usize>> = vec![vec![]; g.nv];
    for i in 0..g.nv {
        let v = order[i];
        let s = free.pop().unwrap_or_else(|| {
            let s = used;
            used += 1;
            s
        });
        slot[v] = s;
        live.push(v);
        let mut keep = vec![];
        for &x in &live {
            if g.adj[x].iter().any(|&y| pos[y] > i) {
                keep.push(x);
            } else {
                free.push(slot[x]);
                freed[i].push(x);
            }
        }
        live = keep;
    }
    (slot, used, freed)
}

fn best_order(g: &Graph) -> (Vec<usize>, usize) {
    let mut best: Option<(Vec<usize>, usize)> = None;
    let mut cands: Vec<Vec<usize>> = vec![(0..g.nv).collect()];
    let starts = if g.nv <= 40 { g.nv } else { 4 };
    let greedy = g.nv <= 40;
    for s in 0..starts {
        // BFS order from s
        let mut seen = vec![false; g.nv];
        let mut q = std::collections::VecDeque::new();
        let mut o = vec![];
        seen[s] = true;
        q.push_back(s);
        while let Some(v) = q.pop_front() {
            o.push(v);
            for &u in &g.adj[v] {
                if !seen[u] {
                    seen[u] = true;
                    q.push_back(u);
                }
            }
        }
        for v in 0..g.nv {
            if !seen[v] {
                o.push(v);
            }
        }
        cands.push(o);
        if !greedy {
            continue;
        }
        // greedy: extend by the vertex minimising the new frontier
        let mut o: Vec<usize> = vec![s];
        let mut inx = vec![false; g.nv];
        inx[s] = true;
        while o.len() < g.nv {
            let mut bestv = usize::MAX;
            let mut bestc = usize::MAX;
            for v in 0..g.nv {
                if inx[v] {
                    continue;
                }
                let touches = g.adj[v].iter().any(|&u| inx[u]);
                inx[v] = true;
                let c = (0..g.nv)
                    .filter(|&x| inx[x] && g.adj[x].iter().any(|&y| !inx[y]))
                    .count();
                inx[v] = false;
                let c = if touches { c } else { c + 1000 };
                if c < bestc {
                    bestc = c;
                    bestv = v;
                }
            }
            inx[bestv] = true;
            o.push(bestv);
        }
        cands.push(o);
    }
    for o in cands {
        let (_, w, _) = frontier_plan(g, &o);
        if best.as_ref().map_or(true, |(_, bw)| w < *bw) {
            best = Some((o, w));
        }
    }
    best.unwrap()
}

fn matchings_frontier(g: &Graph, maxbytes: usize) -> Option<(Vec<Mag>, usize)> {
    matchings_frontier_p(g, g.nv / 2, maxbytes)
}

fn matchings_frontier_p(g: &Graph, p: usize, maxbytes: usize) -> Option<(Vec<Mag>, usize)> {
    let (order, nslots) = best_order(g);
    if nslots > 30 {
        return None;
    }
    let ns = 1usize << nslots;
    if ns.saturating_mul(p + 1).saturating_mul(64) > maxbytes {
        return None;
    }
    let (slot, _, freed) = frontier_plan(g, &order);
    let mut pos = vec![0usize; g.nv];
    for (i, &v) in order.iter().enumerate() {
        pos[v] = i;
    }
    let mut dp: Vec<Vec<Mag>> = vec![vec![vec![]; p + 1]; ns];
    dp[0][0] = vec![1u64];
    for i in 0..g.nv {
        let v = order[i];
        let bv = 1usize << slot[v];
        let back: Vec<usize> = g.adj[v].iter().cloned().filter(|&u| pos[u] < i).collect();
        let mut nd: Vec<Vec<Mag>> = vec![vec![vec![]; p + 1]; ns];
        for st in 0..ns {
            if st & bv != 0 {
                continue;
            }
            for k in 0..=p {
                if dp[st][k].is_empty() {
                    continue;
                }
                mag_addto(&mut nd[st][k], &dp[st][k]); // v not matched backwards
                if k == p {
                    continue;
                }
                for &u in &back {
                    let bu = 1usize << slot[u];
                    if st & bu != 0 {
                        continue;
                    }
                    mag_addto(&mut nd[st | bu | bv][k + 1], &dp[st][k]);
                }
            }
        }
        dp = nd;
        for &x in &freed[i] {
            let b = 1usize << slot[x];
            for st in 0..ns {
                if st & b != 0 {
                    for k in 0..=p {
                        let val = std::mem::take(&mut dp[st][k]);
                        if !val.is_empty() {
                            mag_addto(&mut dp[st & !b][k], &val);
                        }
                    }
                }
            }
        }
    }
    Some((std::mem::take(&mut dp[0]), nslots))
}

fn girth_general(g: &Graph) -> usize {
    let mut best = usize::MAX;
    for root in 0..g.nv {
        let mut dist = vec![usize::MAX; g.nv];
        let mut par = vec![usize::MAX; g.nv];
        dist[root] = 0;
        let mut q = std::collections::VecDeque::new();
        q.push_back(root);
        while let Some(v) = q.pop_front() {
            for &u in &g.adj[v] {
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

fn c4_general(g: &Graph) -> u128 {
    let mut tot = 0u128;
    for u in 0..g.nv {
        for w in (u + 1)..g.nv {
            let c = g.adj[u].iter().filter(|x| g.adj[w].contains(x)).count() as u128;
            tot += c * (c.saturating_sub(1)) / 2;
        }
    }
    tot / 2
}

// ============================ independent brute force ============================
// Plain DFS over matchings: O(#vertices) memory, no subset table at all.
fn matchings_brute(n: usize, s: &[usize]) -> Vec<u128> {
    let nv = 2 * n;
    let mut adj = vec![0u64; nv];
    for i in 0..n {
        for &k in s {
            let j = n + (i + k) % n;
            adj[i] |= 1u64 << j;
            adj[j] |= 1u64 << i;
        }
    }
    brute_from_adj(&adj, nv, n)
}

fn matchings_brute_graph(g: &Graph, p: usize) -> Vec<u128> {
    let mut adj = vec![0u64; g.nv];
    for u in 0..g.nv {
        for &v in &g.adj[u] {
            adj[u] |= 1u64 << v;
        }
    }
    brute_from_adj(&adj, g.nv, p)
}

fn brute_from_adj(adj: &[u64], nv: usize, p: usize) -> Vec<u128> {
    assert!(nv <= 64);
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
    let mut res = vec![0u128; p + 1];
    go(0, 0, nv, adj, &mut res);
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

fn roots_of(mk: &[Mag], p: usize, a: usize, b: usize, n: usize) -> Row {
    let f = build_f(mk, p);
    let c = ((a - 1) + (b - 1)) as f64;
    let m = ((a - 1) * (b - 1)) as f64;
    let top = (2.0 * (a.max(b) as f64 - 1.0) * 2.0).ceil() as u64 + 2; // safe upper bound on y
    let (l1, h1) = least_root(&f, T, top);
    let (l2, h2) = greatest_root(&f, T, top);
    let sc = (1u64 << T) as f64;
    let ymin = 0.5 * (l1 as f64 + h1 as f64) / sc;
    let ymax = 0.5 * (l2 as f64 + h2 as f64) / sc;
    let edge = 2.0 * m.sqrt();
    Row {
        n,
        ymin,
        ymax,
        rho_min: ymin - c,
        rho_max: ymax - c,
        pct_lo: 100.0 * (c - ymin) / edge,
        pct_hi: 100.0 * (ymax - c) / edge,
        c4: 0,
        girth: 0,
        ymin_lo: l1 as f64 / sc,
        ymin_hi: h1 as f64 / sc,
    }
}

fn analyze(n: usize, s: &[usize], a: usize, b: usize) -> (Row, Vec<Mag>) {
    let mk = matchings_transfer(n, s);
    let mut row = roots_of(&mk, n, a, b, n);
    row.c4 = c4_count(n, s);
    row.girth = girth(n, s);
    (row, mk)
}

// ---------------- named cubic bipartite graphs ----------------
fn gp(n: usize, k: usize) -> Graph {
    // generalised Petersen GP(n,k); bipartite iff n even and k odd
    let mut e = vec![];
    for i in 0..n {
        e.push((i, (i + 1) % n));
        e.push((i, n + i));
        e.push((n + i, n + (i + k) % n));
    }
    Graph::new(2 * n, &e)
}

fn gp_interleaved(n: usize, k: usize) -> Graph {
    // GP(n,k) with vertices renumbered u_i -> 2i, v_i -> 2i+1 so the identity order
    // already has a narrow frontier (keeps the generic DP cheap for large n)
    let u = |i: usize| 2 * (i % n);
    let v = |i: usize| 2 * (i % n) + 1;
    let mut e = vec![];
    for i in 0..n {
        e.push((u(i), u(i + 1)));
        e.push((u(i), v(i)));
        e.push((v(i), v(i + k)));
    }
    Graph::new(2 * n, &e)
}

fn circ_graph(n: usize, s: &[usize]) -> Graph {
    let mut e = vec![];
    for i in 0..n {
        for &k in s {
            e.push((i, n + (i + k) % n));
        }
    }
    Graph::new(2 * n, &e)
}

fn biregular42(n: usize, s: &[usize]) -> Graph {
    // left i (0..n-1) ~ right (2i+k) mod 2n, k in S;  |S| = 4 with two even and two odd entries
    // gives a (4,2)-biregular bipartite graph.  Vertices interleaved for a narrow frontier.
    let mut e = vec![];
    for i in 0..n {
        for &k in s {
            let j = (2 * i + k) % (2 * n);
            e.push((3 * i + 2, 3 * (j / 2) + (j % 2)));
        }
    }
    Graph::new(3 * n, &e)
}

fn pappus() -> Graph {
    let lines: [[usize; 3]; 9] = [
        [0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7],
        [2, 5, 8], [0, 4, 8], [1, 5, 6], [2, 3, 7],
    ];
    let mut e = vec![];
    for (i, l) in lines.iter().enumerate() {
        for &v in l {
            e.push((v, 9 + i));
        }
    }
    Graph::new(18, &e)
}

fn tutte_coxeter() -> Graph {
    // Levi graph of GQ(2,2): duads (2-subsets of {0..5}) vs synthemes (perfect matchings of K_6)
    let mut duads: Vec<(usize, usize)> = vec![];
    for i in 0..6 {
        for j in (i + 1)..6 {
            duads.push((i, j));
        }
    }
    let mut synth: Vec<Vec<usize>> = vec![];
    fn rec(rem: &mut Vec<usize>, cur: &mut Vec<usize>, duads: &[(usize, usize)], out: &mut Vec<Vec<usize>>) {
        if rem.is_empty() {
            out.push(cur.clone());
            return;
        }
        let a = rem[0];
        for t in 1..rem.len() {
            let b = rem[t];
            let idx = duads.iter().position(|&(x, y)| x == a.min(b) && y == a.max(b)).unwrap();
            let mut r2: Vec<usize> = rem.iter().cloned().filter(|&x| x != a && x != b).collect();
            cur.push(idx);
            rec(&mut r2, cur, duads, out);
            cur.pop();
        }
    }
    rec(&mut (0..6).collect(), &mut vec![], &duads, &mut synth);
    assert_eq!(synth.len(), 15);
    let mut e = vec![];
    for (i, s) in synth.iter().enumerate() {
        for &d in s {
            e.push((d, 15 + i));
        }
    }
    Graph::new(30, &e)
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

    println!("\n(1b) generic frontier DP vs the same brute force, on non-circulant graphs");
    {
        let cases: Vec<(String, Graph, usize)> = vec![
            ("Pappus".into(), pappus(), 9),
            ("Moebius-Kantor GP(8,3)".into(), gp(8, 3), 8),
            ("Desargues GP(10,3)".into(), gp(10, 3), 10),
            ("(4,2)-biregular n=5 S={0,1,2,7}".into(), biregular42(5, &[0, 1, 2, 7]), 5),
            ("(4,2)-biregular n=6 S={0,1,2,3}".into(), biregular42(6, &[0, 1, 2, 3]), 6),
        ];
        for (name, g, p) in cases {
            let fr = matchings_frontier_p(&g, p, 400_000_000).unwrap().0;
            let bf = matchings_brute_graph(&g, p);
            let fv: Vec<String> = fr.iter().map(|x| mag_to_dec(x)).collect();
            let bv: Vec<String> = bf.iter().map(|x| format!("{}", x)).collect();
            println!("   {:34} {}", name, if fv == bv { "MATCH" } else { "*** MISMATCH ***" });
            assert_eq!(fv, bv, "frontier DP wrong on {}", name);
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

    println!("\n(2b) every cubic bipartite circulant has girth <= 6 (exhaustive scan)");
    {
        let mut worst = 0usize;
        let mut cnt = 0usize;
        for n in 5..=24usize {
            for i in 0..n {
                for j in (i + 1)..n {
                    for k in (j + 1)..n {
                        let s = [i, j, k];
                        let g = girth(n, &s);
                        worst = worst.max(g);
                        cnt += 1;
                    }
                }
            }
        }
        println!(
            "   {} connection sets, n = 5..24: maximum girth attained = {}   (hexagon from",
            cnt, worst
        );
        println!("    0, s1, s1-s2, s1-s2+s3, s3-s2, s3 is always present)");
        assert!(worst <= 6);
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
            vec![
                7, 8, 9, 10, 11, 12, 15, 20, 25, 30, 40, 50, 60, 80, 100, 125, 150, 200, 250, 300,
                400, 500,
            ]
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
        // Richardson extrapolation of y_min(n) = A + B/n^2 on consecutive pairs
        println!("\n  extrapolation assuming y_min(n) = A + B/n^2:");
        println!("  {:>10} {:>16} {:>18} {:>16}", "pair", "A (limit y_min)", "limit % of edge", "B");
        for i in 1..rows.len() {
            let (r1, r2) = (&rows[i - 1], &rows[i]);
            let (n1, n2) = (r1.n as f64, r2.n as f64);
            let (y1, y2) = (r1.ymin, r2.ymin);
            let a = (n2 * n2 * y2 - n1 * n1 * y1) / (n2 * n2 - n1 * n1);
            let b = (y1 - y2) / (1.0 / (n1 * n1) - 1.0 / (n2 * n2));
            println!(
                "  {:>10} {:>16.8} {:>17.5}% {:>16.4}",
                format!("{},{}", r1.n, r2.n),
                a,
                100.0 * (4.0 - a) / 4.0,
                b
            );
        }
    }

    // ---------------- the girth effect at fixed size ----------------
    println!("\n\n=== cubic bipartite graphs of higher girth (generic frontier DP) ===");
    println!("  girth 8 is the largest available: every cubic bipartite CIRCULANT has girth <= 6,");
    println!("  because s1-s2+s3-s1+s2-s3 = 0 always yields a genuine hexagon.");
    println!(
        "\n  {:22} {:>4} {:>5} {:>6} {:>6} {:>18} {:>15} {:>12}",
        "graph", "N", "girth", "C_4", "slots", "least root of g", "% of lower edge", "y_min"
    );
    let mut named: Vec<(String, Graph)> = vec![
        ("K_{3,3}".into(), circ_graph(3, &[0, 1, 2])),
        // disconnected: every root of f is double.  tree.rs's sign-change bisection reports
        // "no real roots found" here; Descartes counting with multiplicity is immune.
        (
            "2 x K_{3,3} (disconn.)".into(),
            Graph::new(
                12,
                &(0..2)
                    .flat_map(|b| (0..3).flat_map(move |u| (0..3).map(move |v| (6 * b + u, 6 * b + 3 + v))))
                    .collect::<Vec<_>>(),
            ),
        ),
        ("cube Q_3".into(), gp(4, 1)),
        ("Heawood B(7,{0,1,3})".into(), circ_graph(7, &[0, 1, 3])),
        ("Moebius-Kantor GP(8,3)".into(), gp(8, 3)),
        ("Pappus".into(), pappus()),
        ("Desargues GP(10,3)".into(), gp(10, 3)),
        ("Nauru GP(12,5)".into(), gp(12, 5)),
        ("B(15,{0,1,2})".into(), circ_graph(15, &[0, 1, 2])),
        ("B(15,{0,1,3})".into(), circ_graph(15, &[0, 1, 3])),
        ("Tutte-Coxeter (8-cage)".into(), tutte_coxeter()),
        ("GP(16,3)".into(), gp(16, 3)),
        ("GP(20,3)".into(), gp(20, 3)),
    ];
    for (name, g) in named.drain(..) {
        let deg: Vec<usize> = g.adj.iter().map(|a| a.len()).collect();
        if deg.iter().any(|&d| d != 3) {
            println!("  {:22} not cubic, skipped", name);
            continue;
        }
        match matchings_frontier(&g, 400_000_000) {
            None => println!("  {:22} SKIPPED (frontier too wide: memory cap)", name),
            Some((mk, slots)) => {
                let p = g.nv / 2;
                let row = roots_of(&mk, p, 3, 3, g.nv);
                println!(
                    "  {:22} {:>4} {:>5} {:>6} {:>6} {:>18.10} {:>14.5}% {:>12.3e}",
                    name,
                    g.nv,
                    girth_general(&g),
                    c4_general(&g),
                    slots,
                    row.rho_min,
                    row.pct_lo,
                    row.ymin
                );
                // cross-check the generic DP against the circulant transfer DP where both apply
                if name.starts_with("Heawood") {
                    let tm = matchings_transfer(7, &[0, 1, 3]);
                    assert_eq!(tm, mk, "generic frontier DP disagrees with circulant DP");
                    println!("     (generic frontier DP == circulant transfer DP on this graph)");
                }
                if name.starts_with("B(15") {
                    let s: Vec<usize> = if name.contains("0,1,2") { vec![0, 1, 2] } else { vec![0, 1, 3] };
                    let tm = matchings_transfer(15, &s);
                    assert_eq!(tm, mk, "generic frontier DP disagrees with circulant DP");
                }
            }
        }
        let _ = g.edges();
    }

    // a second fixed-girth family, to see whether the plateau is a general phenomenon
    println!("\n  a second girth-6 family: generalised Petersen GP(n,3), N = 2n vertices");
    println!(
        "  {:>5} {:>5} {:>6} {:>6} {:>18} {:>15} {:>12} {:>12}",
        "n", "N", "girth", "slots", "least root of g", "% of lower edge", "y_min", "n^2*(1-pct)"
    );
    let mut gprows: Vec<(usize, f64, f64)> = vec![];
    for n in [8usize, 10, 12, 16, 20, 30, 40, 50, 60, 80, 100] {
        let g = gp_interleaved(n, 3);
        match matchings_frontier(&g, 400_000_000) {
            None => println!("  n={} SKIPPED (frontier too wide: memory cap)", n),
            Some((mk, slots)) => {
                let p = g.nv / 2;
                let row = roots_of(&mk, p, 3, 3, g.nv);
                println!(
                    "  {:>5} {:>5} {:>6} {:>6} {:>18.10} {:>14.5}% {:>12.3e} {:>12.4}",
                    n,
                    g.nv,
                    girth_general(&g),
                    slots,
                    row.rho_min,
                    row.pct_lo,
                    row.ymin,
                    (n * n) as f64 * (1.0 - row.pct_lo / 100.0)
                );
                gprows.push((n, row.ymin, row.pct_lo));
            }
        }
    }
    println!("\n  extrapolation assuming y_min(n) = A + B/n^2:");
    for i in 1..gprows.len() {
        let (n1, y1, _) = gprows[i - 1];
        let (n2, y2, _) = gprows[i];
        let (n1, n2) = (n1 as f64, n2 as f64);
        let a = (n2 * n2 * y2 - n1 * n1 * y1) / (n2 * n2 - n1 * n1);
        println!(
            "  pair {:>3},{:<3}  A = {:.8}   limit = {:.5}% of the lower edge",
            n1,
            n2,
            a,
            100.0 * (4.0 - a) / 4.0
        );
    }

    // ---------------- a != b: where the lower bound is NOT vacuous ----------------
    println!("\n\n=== the case a != b, where rho >= -2 sqrt(m) has content ===");
    println!("  For a = b the lower half of the conjecture is vacuous: c = 2 sqrt(m), so");
    println!("  rho = y - c >= -c = -2 sqrt(m) holds for every graph, with equality iff 0 is a");
    println!("  root of mu_G, i.e. iff G has no perfect matching -- impossible for regular");
    println!("  bipartite G.  For a != b, c > 2 sqrt(m) and the bound says y_min >= c - 2 sqrt(m)");
    println!("  = (sqrt(a-1) - sqrt(b-1))^2, a genuine gap in the matching-polynomial roots.");
    println!("\n  (4,2)-biregular: left i ~ right (2i+k) mod 2n, k in S.  c = 4, 2 sqrt(m) = 3.4641,");
    println!("  so the conjecture asserts y_min >= 4 - 2 sqrt 3 = 0.535898.");
    println!(
        "\n  {:14} {:>4} {:>4} {:>6} {:>6} {:>16} {:>12} {:>12} {:>14}",
        "S", "n", "N", "girth", "slots", "least root of g", "-2 sqrt m", "y_min", "% of lower edge"
    );
    for s in [&[0usize, 1, 2, 3][..], &[0, 1, 2, 7][..]] {
        let mut rr: Vec<(usize, f64)> = vec![];
        for n in [6usize, 8, 10, 12, 15, 20, 25, 30, 40, 50] {
            if 2 * n <= *s.iter().max().unwrap() {
                continue;
            }
            let g = biregular42(n, s);
            let ldeg: Vec<usize> = (0..n).map(|i| g.adj[3 * i + 2].len()).collect();
            let rdeg: Vec<usize> = (0..2 * n).map(|j| g.adj[3 * (j / 2) + (j % 2)].len()).collect();
            if ldeg.iter().any(|&d| d != 4) || rdeg.iter().any(|&d| d != 2) {
                println!("  S={:?} n={} not (4,2)-biregular, skipped", s, n);
                continue;
            }
            match matchings_frontier_p(&g, n, 400_000_000) {
                None => println!("  S={:?} n={} SKIPPED (frontier too wide: memory cap)", s, n),
                Some((mk, slots)) => {
                    let row = roots_of(&mk, n, 4, 2, n);
                    println!(
                        "  {:14} {:>4} {:>4} {:>6} {:>6} {:>16.9} {:>12.6} {:>12.8} {:>13.5}%",
                        format!("{:?}", s),
                        n,
                        g.nv,
                        girth_general(&g),
                        slots,
                        row.rho_min,
                        -2.0 * 3f64.sqrt(),
                        row.ymin,
                        row.pct_lo
                    );
                    rr.push((n, row.ymin));
                }
            }
        }
        if rr.len() >= 2 {
            let (n1, y1) = rr[rr.len() - 2];
            let (n2, y2) = rr[rr.len() - 1];
            let (n1, n2) = (n1 as f64, n2 as f64);
            let a = (n2 * n2 * y2 - n1 * n1 * y1) / (n2 * n2 - n1 * n1);
            println!(
                "  extrapolated (1/n^2, pair {},{}):  y_min -> {:.6}   i.e. {:.3}% of the lower edge   (bound needs y_min >= {:.6})",
                n1,
                n2,
                a,
                100.0 * (4.0 - a) / (2.0 * 3f64.sqrt()),
                4.0 - 2.0 * 3f64.sqrt()
            );
        }
        println!();
    }
}
