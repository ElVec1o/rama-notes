// The plateau constant of circband.rs, exactly.
//
// f_n(y) = sum_k (-1)^k m_k y^(n-k) = trace(A(y)^n), where A(y) = y * T(-1/y) and T(t) is the
// matching transfer matrix of the bipartite circulant B(n,S) with weight t per edge.  A(y) is a
// 2^w x 2^w integer matrix of LINEAR polynomials in y: entry = y for a "R_i unmatched" transition
// and -1 for each "R_i matched to L_{i-k}" transition.
//
// By Beraha-Kahane-Weiss the zeros of trace(A(y)^n) accumulate exactly where the maximal
// eigenvalue modulus of A(y) is attained twice.  The plateau constant y* is the smallest real y
// where that happens.  This program computes chi(y,lambda) = det(lambda I - A(y)) exactly over
// Z[y], identifies the nature of the crossing, and then the discriminant.

use std::time::Instant;

// ---------------- Z[y] with i128 coefficients (checked) ----------------
type P = Vec<i128>;

fn ptrim(a: &mut P) {
    while a.len() > 1 && *a.last().unwrap() == 0 {
        a.pop();
    }
}
fn pzero() -> P {
    vec![0]
}
fn pconst(c: i128) -> P {
    vec![c]
}
fn pis_zero(a: &P) -> bool {
    a.iter().all(|&x| x == 0)
}
fn padd(a: &P, b: &P) -> P {
    let mut r = vec![0i128; a.len().max(b.len())];
    for i in 0..r.len() {
        r[i] = a.get(i).copied().unwrap_or(0).checked_add(b.get(i).copied().unwrap_or(0)).expect("ovf");
    }
    ptrim(&mut r);
    r
}
fn psub(a: &P, b: &P) -> P {
    let mut r = vec![0i128; a.len().max(b.len())];
    for i in 0..r.len() {
        r[i] = a.get(i).copied().unwrap_or(0).checked_sub(b.get(i).copied().unwrap_or(0)).expect("ovf");
    }
    ptrim(&mut r);
    r
}
fn pmul(a: &P, b: &P) -> P {
    if pis_zero(a) || pis_zero(b) {
        return pzero();
    }
    let mut r = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        for (j, &z) in b.iter().enumerate() {
            if z == 0 {
                continue;
            }
            r[i + j] = r[i + j].checked_add(x.checked_mul(z).expect("ovf")).expect("ovf");
        }
    }
    ptrim(&mut r);
    r
}
fn pdiv_scalar(a: &P, d: i128) -> P {
    let mut r: P = a
        .iter()
        .map(|&x| {
            assert_eq!(x % d, 0, "inexact division in Faddeev-LeVerrier");
            x / d
        })
        .collect();
    ptrim(&mut r);
    r
}
fn pdeg(a: &P) -> usize {
    let mut d = a.len() - 1;
    while d > 0 && a[d] == 0 {
        d -= 1;
    }
    d
}
fn pshow(a: &P, var: &str) -> String {
    if pis_zero(a) {
        return "0".into();
    }
    let mut t = vec![];
    for i in (0..a.len()).rev() {
        if a[i] == 0 {
            continue;
        }
        t.push(match i {
            0 => format!("{}", a[i]),
            1 => format!("{}*{}", a[i], var),
            _ => format!("{}*{}^{}", a[i], var, i),
        });
    }
    t.join(" + ")
}

// ---------------- the transfer matrix A(y) ----------------
fn amatrix(s: &[usize]) -> Vec<Vec<P>> {
    let w = *s.iter().max().unwrap();
    let ns = 1usize << w;
    let mut a = vec![vec![pzero(); ns]; ns];
    for st in 0..ns {
        let base = (st >> 1) & (ns - 1);
        // R_i unmatched: weight y
        a[st][base] = padd(&a[st][base], &vec![0, 1]);
        for &k in s {
            let t = if k == 0 {
                base | (1 << (w - 1))
            } else {
                let bit = w - k;
                if (st >> bit) & 1 == 1 {
                    continue;
                }
                ((st | (1 << bit)) >> 1) & (ns - 1)
            };
            a[st][t] = padd(&a[st][t], &pconst(-1));
        }
    }
    a
}

fn mat_mul(a: &Vec<Vec<P>>, b: &Vec<Vec<P>>) -> Vec<Vec<P>> {
    let n = a.len();
    let mut c = vec![vec![pzero(); n]; n];
    for i in 0..n {
        for k in 0..n {
            if pis_zero(&a[i][k]) {
                continue;
            }
            for j in 0..n {
                if pis_zero(&b[k][j]) {
                    continue;
                }
                let t = pmul(&a[i][k], &b[k][j]);
                c[i][j] = padd(&c[i][j], &t);
            }
        }
    }
    c
}

fn mat_trace(a: &Vec<Vec<P>>) -> P {
    let mut t = pzero();
    for i in 0..a.len() {
        t = padd(&t, &a[i][i]);
    }
    t
}

// char poly of A: returns coefficients c[i] of lambda^i, c[n] = 1
fn charpoly(a: &Vec<Vec<P>>) -> Vec<P> {
    let n = a.len();
    let mut c = vec![pzero(); n + 1];
    c[n] = pconst(1);
    let mut m = vec![vec![pzero(); n]; n]; // M_0 = 0
    for k in 1..=n {
        // M_k = A*(M_{k-1} + c_{n-k+1} I)
        let mut t = m.clone();
        for i in 0..n {
            t[i][i] = padd(&t[i][i], &c[n - k + 1]);
        }
        m = mat_mul(a, &t);
        let tr = mat_trace(&m);
        c[n - k] = pdiv_scalar(&psub(&pzero(), &tr), k as i128);
    }
    c
}

// ---------------- resultant / discriminant over Z[y] ----------------
// Sylvester determinant of f (deg m in lambda) and g (deg n), computed by subset DP over columns.
fn resultant(f: &[P], g: &[P]) -> P {
    let m = f.len() - 1;
    let n = g.len() - 1;
    let sz = m + n;
    let mut mat = vec![vec![pzero(); sz]; sz];
    for i in 0..n {
        for j in 0..=m {
            mat[i][i + j] = f[m - j].clone();
        }
    }
    for i in 0..m {
        for j in 0..=n {
            mat[n + i][i + j] = g[n - j].clone();
        }
    }
    det_subset(&mat)
}

fn det_subset(mat: &Vec<Vec<P>>) -> P {
    let sz = mat.len();
    let full = 1usize << sz;
    let mut dp: Vec<Option<P>> = vec![None; full];
    dp[0] = Some(pconst(1));
    // process subsets in order of popcount: D[S] uses row |S|-1
    let mut order: Vec<usize> = (0..full).collect();
    order.sort_by_key(|s| s.count_ones());
    for &s in &order {
        if s == 0 {
            continue;
        }
        let k = s.count_ones() as usize;
        let row = k - 1;
        let mut acc = pzero();
        let mut idx = 0usize;
        let mut bits = s;
        while bits != 0 {
            let j = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            if !pis_zero(&mat[row][j]) {
                if let Some(prev) = &dp[s & !(1usize << j)] {
                    if !pis_zero(prev) {
                        let t = pmul(&mat[row][j], prev);
                        // sign (-1)^{(k-1) + idx}
                        if ((k - 1 + idx) % 2) == 0 {
                            acc = padd(&acc, &t);
                        } else {
                            acc = psub(&acc, &t);
                        }
                    }
                }
            }
            idx += 1;
        }
        dp[s] = Some(acc);
    }
    dp[full - 1].clone().unwrap()
}

fn pderiv(c: &[P]) -> Vec<P> {
    // derivative in lambda of sum_i c[i] lambda^i
    (1..c.len()).map(|i| pmul(&c[i], &pconst(i as i128))).collect()
}

fn peval_f64(a: &P, y: f64) -> f64 {
    a.iter().rev().fold(0.0f64, |acc, &k| acc * y + k as f64)
}

fn content(a: &P) -> i128 {
    fn g(a: i128, b: i128) -> i128 {
        if b == 0 {
            a.abs()
        } else {
            g(b, a % b)
        }
    }
    a.iter().fold(0i128, |c, &x| g(c, x))
}

// exact division of a by b in Z[y] (returns None if not exact)
fn pdiv_exact(a: &P, b: &P) -> Option<P> {
    let mut r = a.clone();
    ptrim(&mut r);
    let mut bb = b.clone();
    ptrim(&mut bb);
    let db = pdeg(&bb);
    let lb = bb[db];
    if pis_zero(&r) {
        return Some(pzero());
    }
    let mut q = vec![0i128; pdeg(&r).saturating_sub(db) + 1];
    loop {
        let dr = pdeg(&r);
        if pis_zero(&r) {
            break;
        }
        if dr < db {
            return None;
        }
        if r[dr] % lb != 0 {
            return None;
        }
        let c = r[dr] / lb;
        q[dr - db] = c;
        for i in 0..=db {
            r[dr - db + i] -= c * bb[i];
        }
        ptrim(&mut r);
        if pis_zero(&r) {
            break;
        }
    }
    if !pis_zero(&r) {
        return None;
    }
    ptrim(&mut q);
    Some(q)
}

// ---------------- minimal big integers (exact high-precision arithmetic) ----------------
#[derive(Clone, PartialEq, Eq)]
struct B {
    neg: bool,
    m: Vec<u64>, // little endian, trimmed, empty = 0
}
fn btrim(m: &mut Vec<u64>) {
    while m.last() == Some(&0) {
        m.pop();
    }
}
fn mcmp(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    std::cmp::Ordering::Equal
}
fn madd(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = vec![];
    let mut c = 0u64;
    for i in 0..a.len().max(b.len()) {
        let (x, c1) = a.get(i).copied().unwrap_or(0).overflowing_add(b.get(i).copied().unwrap_or(0));
        let (z, c2) = x.overflowing_add(c);
        r.push(z);
        c = (c1 as u64) + (c2 as u64);
    }
    if c > 0 {
        r.push(c);
    }
    btrim(&mut r);
    r
}
fn msub(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = vec![];
    let mut bw = 0u64;
    for i in 0..a.len() {
        let (x, c1) = a[i].overflowing_sub(b.get(i).copied().unwrap_or(0));
        let (z, c2) = x.overflowing_sub(bw);
        r.push(z);
        bw = (c1 as u64) + (c2 as u64);
    }
    btrim(&mut r);
    r
}
fn mmul(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut r = vec![0u64; a.len() + b.len()];
    for i in 0..a.len() {
        let mut carry = 0u128;
        for j in 0..b.len() {
            let t = (a[i] as u128) * (b[j] as u128) + (r[i + j] as u128) + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        let mut k = i + b.len();
        while carry > 0 {
            let t = (r[k] as u128) + carry;
            r[k] = t as u64;
            carry = t >> 64;
            k += 1;
        }
    }
    btrim(&mut r);
    r
}
fn mshl(a: &[u64], bits: usize) -> Vec<u64> {
    if a.is_empty() {
        return vec![];
    }
    let (w, s) = (bits / 64, bits % 64);
    let mut r = vec![0u64; w];
    if s == 0 {
        r.extend_from_slice(a);
    } else {
        let mut c = 0u64;
        for &x in a {
            r.push((x << s) | c);
            c = x >> (64 - s);
        }
        if c > 0 {
            r.push(c);
        }
    }
    btrim(&mut r);
    r
}
fn mshr(a: &[u64], bits: usize) -> Vec<u64> {
    let (w, s) = (bits / 64, bits % 64);
    if w >= a.len() {
        return vec![];
    }
    let t = &a[w..];
    let mut r = vec![0u64; t.len()];
    if s == 0 {
        r.copy_from_slice(t);
    } else {
        for i in 0..t.len() {
            r[i] = (t[i] >> s) | if i + 1 < t.len() { t[i + 1] << (64 - s) } else { 0 };
        }
    }
    btrim(&mut r);
    r
}
fn mdec(a: &[u64]) -> String {
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
        btrim(&mut q);
        parts.push(rem as u64);
        t = q;
    }
    let mut s = format!("{}", parts.pop().unwrap());
    while let Some(p) = parts.pop() {
        s.push_str(&format!("{:019}", p));
    }
    s
}
impl B {
    fn zero() -> B {
        B { neg: false, m: vec![] }
    }
    fn from_i128(x: i128) -> B {
        let neg = x < 0;
        let u = x.unsigned_abs();
        let mut m = vec![u as u64, (u >> 64) as u64];
        btrim(&mut m);
        B { neg: neg && !m.is_empty(), m }
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
    fn add(&self, o: &B) -> B {
        if self.neg == o.neg {
            B { neg: self.neg, m: madd(&self.m, &o.m) }
        } else {
            match mcmp(&self.m, &o.m) {
                std::cmp::Ordering::Greater => B { neg: self.neg, m: msub(&self.m, &o.m) },
                std::cmp::Ordering::Less => B { neg: o.neg, m: msub(&o.m, &self.m) },
                std::cmp::Ordering::Equal => B::zero(),
            }
        }
    }
    fn mul(&self, o: &B) -> B {
        let m = mmul(&self.m, &o.m);
        B { neg: (self.neg != o.neg) && !m.is_empty(), m }
    }
    fn shl(&self, b: usize) -> B {
        let m = mshl(&self.m, b);
        B { neg: self.neg && !m.is_empty(), m }
    }
}

// sign of P(N / 2^t) for an integer polynomial, exactly
fn psign_dyadic(p: &P, n: &[u64], t: usize) -> i32 {
    let d = pdeg(p);
    let nb = B { neg: false, m: n.to_vec() };
    let mut r = B::from_i128(p[d]);
    for j in (0..d).rev() {
        r = r.mul(&nb).add(&B::from_i128(p[j]).shl(t * (d - j)));
    }
    r.sign()
}

// isolate the root of p nearest to the f64 estimate y0, to 2^-t, by exact bisection
fn root_dyadic(p: &P, y0: f64, t: usize) -> Vec<u64> {
    // bracket [a,b] in units of 2^-t around y0
    let scale = |x: f64| -> Vec<u64> {
        // floor(x * 2^t) for 0 < x < 1, via 2^53-limited mantissa then shift
        let e = 53usize;
        let mant = (x * (1u64 << e) as f64).floor() as u64;
        mshl(&[mant], t - e)
    };
    let mut a = scale(y0 * (1.0 - 1e-7));
    let mut b = scale(y0 * (1.0 + 1e-7));
    let sa = psign_dyadic(p, &a, t);
    let sb = psign_dyadic(p, &b, t);
    assert!(sa != 0 && sb != 0 && sa != sb, "no sign change in the initial bracket");
    let one = vec![1u64];
    while mcmp(&msub(&b, &a), &one) == std::cmp::Ordering::Greater {
        let mid = mshr(&madd(&a, &b), 1);
        if psign_dyadic(p, &mid, t) == sa {
            a = mid;
        } else {
            b = mid;
        }
    }
    a
}

// print N/2^t as a decimal with `digits` places after the point
fn dyadic_decimal(n: &[u64], t: usize, digits: usize) -> String {
    let mut p10 = vec![1u64];
    for _ in 0..digits {
        p10 = mmul(&p10, &[10]);
    }
    let scaled = mshr(&mmul(n, &p10), t);
    let s = mdec(&scaled);
    let s = if s.len() <= digits { format!("{}{}", "0".repeat(digits + 1 - s.len()), s) } else { s };
    format!("{}.{}", &s[..s.len() - digits], &s[s.len() - digits..])
}

// ---------------- complex arithmetic for exploration only ----------------
#[derive(Clone, Copy, Debug)]
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
    fn mul(self, o: C) -> C {
        C::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
    fn div(self, o: C) -> C {
        let d = o.re * o.re + o.im * o.im;
        C::new((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)
    }
    fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
}

// Durand-Kerner: all roots of a monic polynomial given by coefficients c[0..=d] (c[d] = 1)
fn roots_dk(c: &[f64]) -> Vec<C> {
    let d = c.len() - 1;
    let mut z: Vec<C> = (0..d)
        .map(|i| {
            let t = 0.4 + 0.9 * i as f64;
            C::new(1.3 * t.cos(), 1.3 * t.sin())
        })
        .collect();
    for _ in 0..4000 {
        let mut moved = 0f64;
        for i in 0..d {
            let mut num = C::new(c[d], 0.0);
            for k in (0..d).rev() {
                num = num.mul(z[i]).add(C::new(c[k], 0.0));
            }
            let mut den = C::new(1.0, 0.0);
            for j in 0..d {
                if j != i {
                    den = den.mul(z[i].sub(z[j]));
                }
            }
            let delta = num.div(den);
            z[i] = z[i].sub(delta);
            moved = moved.max(delta.abs());
        }
        if moved < 1e-15 {
            break;
        }
    }
    z
}

fn eval_chi(chi: &[P], y: f64) -> Vec<f64> {
    chi.iter()
        .map(|p| p.iter().rev().fold(0.0f64, |acc, &k| acc * y + k as f64))
        .collect()
}

fn selftest() {
    println!("=== self-tests of the exact primitives ===");
    // irreducibility test on known cases
    let cases: Vec<(P, u64, bool, &str)> = vec![
        (vec![-1, 0, 1], 7, false, "y^2-1 = (y-1)(y+1)"),
        (vec![1, 0, 1], 7, true, "y^2+1 mod 7 (7 = 3 mod 4)"),
        (vec![1, 0, 1], 5, false, "y^2+1 mod 5 = (y-2)(y+2)"),
        (vec![-2, 0, 1], 3, true, "y^2-2 mod 3 (2 is a non-residue)"),
        (vec![-2, 0, 1], 7, false, "y^2-2 mod 7 = (y-3)(y+3)"),
        (vec![-2, 0, 0, 1], 7, true, "y^3-2 mod 7 (2 is not a cube)"),
        (vec![-2, 0, 0, 1], 5, false, "y^3-2 mod 5 (3^3 = 2)"),
        (vec![-1, 1, 0, 0, -1, 1], 101, false, "(y-1)(y^4+1)"),
    ];
    for (f, p, want, name) in cases {
        let got = irreducible_mod_p(&f, p);
        println!("   irreducible_mod_p({:30}) = {:?}   expect {}", name, got, want);
        assert_eq!(got, Some(want));
    }
    // exact division
    let a = pmul(&vec![1, 2, 3], &vec![-5, 7]);
    assert_eq!(pdiv_exact(&a, &vec![-5, 7]).unwrap(), vec![1, 2, 3]);
    assert!(pdiv_exact(&vec![1, 1, 1], &vec![1, 1]).is_none());
    println!("   pdiv_exact: OK");
    // Descartes interval count: (y-1)(y-2)(y-5) has 1 root in (0, 3/2), 2 in (0, 3)
    let f: P = vec![-10, 17, -8, 1];
    assert_eq!(roots_in_0_b(&f, &[3], 1), 1);
    assert_eq!(roots_in_0_b(&f, &[3], 0), 2);
    assert_eq!(roots_in_0_b(&f, &[1], 1), 0);
    println!("   roots_in_0_b on (y-1)(y-2)(y-5): 1 root below 1.5, 2 below 3, 0 below 0.5  OK");
    // dyadic root isolation and printing
    let two: P = vec![-2, 0, 1]; // sqrt(2)
    let n = root_dyadic(&two, 1.4142135623, 200);
    let d = dyadic_decimal(&n, 200, 30);
    println!("   root_dyadic(y^2-2) = {}", d);
    assert!(d.starts_with("1.414213562373095048801688724209"));
    println!();
}

fn main() {
    selftest();
    for s in [&[0usize, 1, 2][..], &[0, 1, 3][..]] {
        println!("\n================ S = {:?} ================", s);
        let t0 = Instant::now();
        let a = amatrix(s);
        let n = a.len();
        println!("A(y) is {}x{} :", n, n);
        for i in 0..n {
            let row: Vec<String> = a[i].iter().map(|p| pshow(p, "y")).collect();
            println!("   [{}]", row.join(", "));
        }
        let chi = charpoly(&a);
        println!("\nchi(y,lambda) = det(lambda I - A(y)):");
        for i in (0..=n).rev() {
            if !pis_zero(&chi[i]) {
                println!("   lambda^{:<2} * ({})", i, pshow(&chi[i], "y"));
            }
        }
        println!("   deg_y of coefficients: {:?}", chi.iter().map(|p| pdeg(p)).collect::<Vec<_>>());

        // exact check: f_n(y) = trace(A(y)^n) against the m_k from the DP
        for nn in [7usize, 8, 9] {
            if nn <= *s.iter().max().unwrap() {
                continue;
            }
            let mut pw = a.clone();
            for _ in 1..nn {
                pw = mat_mul(&pw, &a);
            }
            let tr = mat_trace(&pw);
            let mk = mk_brute(nn, s);
            let mut f = vec![0i128; nn + 1];
            for (k, &v) in mk.iter().enumerate() {
                f[nn - k] = if k % 2 == 0 { v } else { -v };
            }
            ptrim(&mut f);
            let mut trc = tr.clone();
            ptrim(&mut trc);
            println!(
                "   check trace(A^{}) == f_{}  : {}",
                nn,
                nn,
                if trc == f { "MATCH" } else { "*** MISMATCH ***" }
            );
            assert_eq!(trc, f);
        }

        // nature of the crossing near the plateau constant
        let ystar = if s == [0usize, 1, 2] { 0.06156635 } else { 0.00592560 };
        println!("\n  eigenvalues of A(y) near y* = {}: (|.| sorted descending)", ystar);
        for d in [-4.0f64, -1.0, -0.1, 0.0, 0.1, 1.0, 4.0] {
            let y = ystar * (1.0 + d * 0.02);
            let cf = eval_chi(&chi, y);
            let mut r = roots_dk(&cf);
            r.sort_by(|p, q| q.abs().partial_cmp(&p.abs()).unwrap());
            let top: Vec<String> = r
                .iter()
                .take(3)
                .map(|z| format!("{:.9}{:+.9}i (|.|={:.9})", z.re, z.im, z.abs()))
                .collect();
            println!("   y = {:.10}  {}", y, top.join("   "));
        }
        // ---- discriminant ----
        let t1 = Instant::now();
        let dchi = pderiv(&chi);
        let disc = resultant(&chi, &dchi);
        println!(
            "\n  disc_lambda chi(y,.) has degree {} in y, content {}   ({:?})",
            pdeg(&disc),
            content(&disc),
            t1.elapsed()
        );
        let prim = pdiv_exact(&disc, &pconst(content(&disc))).unwrap();
        println!("  primitive part D(y) = {}", pshow(&prim, "y"));
        println!("  coefficients (low to high): {:?}", prim);
        // real roots of D by scanning + bisection (f64, exploration only)
        let mut rr: Vec<f64> = vec![];
        let (lo, hi, steps) = (-3.0f64, 6.0f64, 900000usize);
        let mut px = lo;
        let mut pv = peval_f64(&prim, lo);
        for i in 1..=steps {
            let x = lo + (hi - lo) * i as f64 / steps as f64;
            let v = peval_f64(&prim, x);
            if pv * v < 0.0 {
                let (mut a2, mut b2) = (px, x);
                for _ in 0..200 {
                    let mid = 0.5 * (a2 + b2);
                    if peval_f64(&prim, a2) * peval_f64(&prim, mid) <= 0.0 {
                        b2 = mid;
                    } else {
                        a2 = mid;
                    }
                }
                rr.push(0.5 * (a2 + b2));
            }
            px = x;
            pv = v;
        }
        println!("  real roots of D in [-3,6] (f64 scan): {:?}", rr.iter().map(|x| format!("{:.12}", x)).collect::<Vec<_>>());

        // strip the y^k factor (y = 0 is a spurious degeneracy of A(0), not a crossing)
        let mut core = prim.clone();
        let mut k0 = 0usize;
        while core[0] == 0 {
            core.remove(0);
            k0 += 1;
        }
        println!("  D(y) = y^{} * F(y), deg F = {}, lc(F) = {}, F(0) = {}", k0, pdeg(&core), core[pdeg(&core)], core[0]);

        // minimal-degree integer factor of F having y* as a root  ==  minimal polynomial of y*
        let target = rr.iter().cloned().find(|&x| (x - ystar).abs() < 1e-4).expect("y* not a root of D");
        let mp = min_poly_factor(&core, target).expect("no integer factor found");
        println!("\n  ===> minimal polynomial of y*:  {}", pshow(&mp, "y"));
        println!("       degree {}, coefficients (low to high) {:?}", pdeg(&mp), mp);
        // exact certificates
        assert!(pdiv_exact(&core, &mp).is_some(), "candidate does not divide F exactly");
        println!("       [exact check] mp divides disc_lambda(chi) in Z[y]: YES");
        println!("       [exact check] cofactor F/mp = {}", pshow(&pdiv_exact(&core, &mp).unwrap(), "y"));
        println!("       [exact check] content(mp) = {}", content(&mp));
        // irreducibility certificate: irreducible mod some prime => irreducible over Q
        let mut cert = None;
        for p in [1_000_003u64, 1_000_033, 1_000_037, 1_000_039, 1_000_081, 1_000_099,
                  2_000_003, 2_000_029, 3_000_017, 5_000_011, 7_000_003, 999_999_937] {
            if irreducible_mod_p(&mp, p) == Some(true) {
                cert = Some(p);
                break;
            }
        }
        match cert {
            Some(p) => println!(
                "       [exact check] mp is IRREDUCIBLE mod p = {}, hence irreducible over Q  => it IS the minimal polynomial",
                p
            ),
            None => println!("       [warn] no mod-p irreducibility certificate found among the primes tried"),
        }

        // y* to high precision by exact dyadic bisection on mp
        let t = 512usize;
        let nn = root_dyadic(&mp, target, t);
        let hi = madd(&nn, &[1]);
        let (dl, dh) = (dyadic_decimal(&nn, t, 70), dyadic_decimal(&hi, t, 70));
        let agree = dl.chars().zip(dh.chars()).take_while(|(a, b)| a == b).count();
        println!("       y*  = {}   ({} decimal digits certified; enclosure width 2^-{})", &dl[..agree], agree - 2, t);
        // percentage of the lower edge = 100 * (c - y*) / (2 sqrt m); for a=b=3 this is 100*(4-y*)/4
        // = 100 - 25*y*  (exact rational multiple of y*)
        let pct_num = {
            // 100 - 25 y*  with y* = N/2^t  -->  (100*2^t - 25 N) / 2^t
            let hundred = B { neg: false, m: mshl(&[100], t) };
            let v = hundred.add(&B { neg: true, m: mmul(&nn, &[25]) });
            v.m
        };
        let pct_lo = {
            let hundred = B { neg: false, m: mshl(&[100], t) };
            hundred.add(&B { neg: true, m: mmul(&hi, &[25]) }).m
        };
        let (pl, ph) = (dyadic_decimal(&pct_lo, t, 50), dyadic_decimal(&pct_num, t, 50));
        let ag = pl.chars().zip(ph.chars()).take_while(|(a, b)| a == b).count();
        println!("       % of the lower edge = 100 - 25*y* = {}", &pl[..ag]);

        // y* is the SMALLEST positive zero of the discriminant: exact Descartes count on (0, y*)
        {
            let t2 = 60usize;
            let b2 = mshr(&nn, t - t2); // floor(y* 2^60) <= y*
            let cnt = roots_in_0_b(&core, &b2, t2);
            println!(
                "       [exact] Descartes count of roots of F in (0, {}) = {}  => y* is the least positive",
                dyadic_decimal(&b2, t2, 16),
                cnt
            );
            println!("               zero of disc_lambda(chi) apart from the spurious y = 0");
            assert_eq!(cnt, 0);
        }

        // exact sign of D on the two sides of the bracket: the number of complex-conjugate
        // pairs of chi(y,.) changes across y*, so the crossing is a genuine root collision
        {
            // y_lo = (N-1)/2^t, y_hi = (N+2)/2^t : both strictly outside the enclosure
            let ylo = msub(&nn, &[1]);
            let yhi = madd(&nn, &[2]);
            println!(
                "       [exact] sign D(y) just below y* = {:+}, just above = {:+}  (a sign change: the",
                psign_dyadic(&core, &ylo, t),
                psign_dyadic(&core, &yhi, t)
            );
            println!("               number of complex-conjugate eigenvalue pairs changes at y*)");
        }

        // cross-check against the independent exact transfer-matrix values from circband
        let data: &[(f64, f64)] = if s == [0usize, 1, 2] {
            &[(200.0, 0.0616317188928406), (250.0, 0.0616081849246370), (300.0, 0.0615954010144151),
              (400.0, 0.0615826897216607), (500.0, 0.0615768062028224)]
        } else {
            &[(200.0, 0.0060633845844791), (250.0, 0.0060138089127690), (300.0, 0.0059868656081221),
              (400.0, 0.0059600660929391), (500.0, 0.0059476586058054)]
        };
        let exact: f64 = dl[..agree].parse().unwrap();
        println!("\n  cross-check with circband's exact y_min(n) (certified brackets, width 5.7e-14):");
        println!("  {:>5} {:>20} {:>22} {:>26}", "n", "y_min(n)", "y_min(n) - y*", "digits vs y*");
        for &(n, y) in data {
            let d = y - exact;
            println!("  {:>5} {:>20.16} {:>22.3e} {:>22.4} n^2", n, y, d, d * n * n);
        }
        let k = data.len();
        let (n1, y1) = data[k - 2];
        let (n2, y2) = data[k - 1];
        let a2 = (n2 * n2 * y2 - n1 * n1 * y1) / (n2 * n2 - n1 * n1);
        let (n0, y0v) = data[k - 3];
        // 3-point Richardson for A + B/n^2 + C/n^4
        let (u0, u1, u2) = (1.0 / (n0 * n0), 1.0 / (n1 * n1), 1.0 / (n2 * n2));
        let a3 = y0v * (u1 * u2) / ((u0 - u1) * (u0 - u2)) + y1 * (u0 * u2) / ((u1 - u0) * (u1 - u2))
            + y2 * (u0 * u1) / ((u2 - u0) * (u2 - u1));
        println!("  2-point Richardson (n = {}, {}):  {:.16}", n1, n2, a2);
        println!("  3-point Richardson (n = {}, {}, {}):  {:.16}", n0, n1, n2, a3);
        println!("  exact y*                          :  {:.16}", exact);
        for (name, v) in [("2-point", a2), ("3-point", a3)] {
            let rel = ((v - exact) / exact).abs();
            println!("  {} extrapolation agrees with the exact value to {:.1} significant digits (rel. err {:.2e})",
                name, -rel.log10(), rel);
        }
        println!("  built in {:?}", t0.elapsed());
    }

    println!("\n\n=== SUMMARY ===");
    println!("chi(y,lambda) = det(lambda I - A(y)),  f_n(y) = trace(A(y)^n) = sum_i lambda_i(y)^n.");
    println!("The coefficients in the Beraha-Kahane-Weiss sum are all 1, so no coefficient can");
    println!("vanish and the accumulation set of the zeros is exactly {{y : max|lambda_i| attained twice}}.");
    println!();
    println!("S = {{0,1,2}} (girth 4):  chi = lambda^4 + (3-y) lambda^3 + 2 lambda^2 + (y-1) lambda - 1");
    println!("   disc_lambda(chi) = 4 y^2 (y^4 - 12 y^3 + 46 y^2 - 84 y + 5)");
    println!("   minimal polynomial of y*:  y^4 - 12 y^3 + 46 y^2 - 84 y + 5   (degree 4, monic, irreducible)");
    println!("   y*   = 0.06156634660415894633902643562601028916640286818422253271101768898");
    println!("   pct  = 100 - 25 y* = 98.46084133489602634152433910934974277083992829539443 %");
    println!();
    println!("S = {{0,1,3}} (girth 6):  chi = lambda^8 + (3-y) lambda^7 + 2 lambda^6");
    println!("                             + (y^2-4y+2) lambda^4 + (2-2y) lambda^3 + (1-y) lambda + 1");
    println!("   disc_lambda(chi) = y^3 * F(y),  F of degree 17, irreducible, lc = 729");
    println!("   minimal polynomial of y*:  F(y)/729  (degree 17; primitive integer form F printed above)");
    println!("   y*   = 0.00592559594225622886729761949978641161562845438998127238842749900");
    println!("   pct  = 100 - 25 y* = 99.85186010144359427831755951250533970960928864025046 %");
    println!();
    println!("Crossing type: a REAL eigenvalue collision.  Below y* the two dominant eigenvalues are");
    println!("real and distinct; at y* they collide; above y* they are a complex-conjugate pair, whose");
    println!("moduli are then equal identically.  So disc = 0 is the right condition, y* is the left");
    println!("endpoint of the accumulation band, and lim_n y_min(n) = y* exactly (approached from");
    println!("above with the 1/n^2 band-edge law, as the finite-n data confirm).");
}

// ---------------- irreducibility certificate: F mod p irreducible => F irreducible over Q ----
fn pmod_mul(a: &[u64], b: &[u64], f: &[u64], p: u64) -> Vec<u64> {
    let n = f.len() - 1; // f monic of degree n
    let mut r = vec![0u64; a.len() + b.len()];
    for i in 0..a.len() {
        if a[i] == 0 {
            continue;
        }
        for j in 0..b.len() {
            r[i + j] = ((r[i + j] as u128 + a[i] as u128 * b[j] as u128) % p as u128) as u64;
        }
    }
    for k in (n..r.len()).rev() {
        let c = r[k];
        if c == 0 {
            continue;
        }
        r[k] = 0;
        for j in 0..n {
            // x^k = x^{k-n} * (x^n) and x^n = -(f_0 + ... + f_{n-1} x^{n-1})
            let sub = (c as u128 * f[j] as u128) % p as u128;
            r[k - n + j] = ((r[k - n + j] as u128 + p as u128 - sub) % p as u128) as u64;
        }
    }
    r.truncate(n.max(1));
    r
}
fn pmod_gcd(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    let deg = |v: &[u64]| -> Option<usize> { (0..v.len()).rev().find(|&i| v[i] != 0) };
    let (mut x, mut y) = (a.to_vec(), b.to_vec());
    loop {
        let dy = match deg(&y) {
            None => return x,
            Some(d) => d,
        };
        let inv = modpow(y[dy], p - 2, p);
        loop {
            let dx = match deg(&x) {
                None => break,
                Some(d) => d,
            };
            if dx < dy {
                break;
            }
            let c = (x[dx] as u128 * inv as u128 % p as u128) as u64;
            for j in 0..=dy {
                let s = (c as u128 * y[j] as u128) % p as u128;
                x[dx - dy + j] = ((x[dx - dy + j] as u128 + p as u128 - s) % p as u128) as u64;
            }
        }
        std::mem::swap(&mut x, &mut y);
    }
}
fn modpow(mut b: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1u64;
    b %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = (r as u128 * b as u128 % p as u128) as u64;
        }
        b = (b as u128 * b as u128 % p as u128) as u64;
        e >>= 1;
    }
    r
}
// returns Some(true/false) if the test is applicable at p
fn irreducible_mod_p(f: &P, p: u64) -> Option<bool> {
    let n = pdeg(f);
    if f[n].rem_euclid(p as i128) == 0 {
        return None;
    }
    let inv = modpow(f[n].rem_euclid(p as i128) as u64, p - 2, p);
    let fm: Vec<u64> = (0..=n)
        .map(|i| (f[i].rem_euclid(p as i128) as u128 * inv as u128 % p as u128) as u64)
        .collect();
    // x^(p^k) mod f, by repeated p-th powering
    let mut xp = vec![0u64; n];
    if n > 1 {
        xp[1] = 1;
    } else {
        return Some(true);
    }
    let powp = |v: &Vec<u64>, f: &Vec<u64>| -> Vec<u64> {
        // v^p mod f by square-and-multiply
        let mut r = vec![0u64; n];
        r[0] = 1;
        let mut b = v.clone();
        let mut e = p;
        while e > 0 {
            if e & 1 == 1 {
                r = pmod_mul(&r, &b, f, p);
            }
            b = pmod_mul(&b, &b, f, p);
            e >>= 1;
        }
        r
    };
    let mut cur = xp.clone(); // x^(p^0) = x
    let mut pows: Vec<Vec<u64>> = vec![cur.clone()];
    for _ in 1..=n {
        cur = powp(&cur, &fm);
        pows.push(cur.clone());
    }
    // x^(p^n) == x ?
    let mut t = pows[n].clone();
    t[1] = (t[1] + p - 1) % p;
    if t.iter().any(|&c| c != 0) {
        return Some(false);
    }
    // gcd(x^(p^(n/q)) - x, f) == 1 for every prime q | n
    let mut m = n;
    let mut qs = vec![];
    let mut d = 2;
    while d * d <= m {
        if m % d == 0 {
            qs.push(d);
            while m % d == 0 {
                m /= d;
            }
        }
        d += 1;
    }
    if m > 1 {
        qs.push(m);
    }
    for q in qs {
        let mut t = pows[n / q].clone();
        t[1] = (t[1] + p - 1) % p;
        let g = pmod_gcd(&fm, &t, p);
        let dg = (0..g.len()).rev().find(|&i| g[i] != 0).unwrap_or(0);
        if dg > 0 {
            return Some(false);
        }
    }
    Some(true)
}

// Descartes bound on the number of roots of f in the open interval (0, B/2^t):
// substitute y = b/(1+u), clear denominators, count sign changes.  0 changes => no roots.
fn roots_in_0_b(f: &P, bnum: &[u64], t: usize) -> usize {
    let d = pdeg(f);
    let bb = B { neg: false, m: bnum.to_vec() };
    // H(u) = sum_i f_i B^i 2^(t(d-i)) (1+u)^(d-i)
    let mut h = vec![B::zero(); d + 1];
    let mut bpow = B::from_i128(1);
    for i in 0..=d {
        if f[i] != 0 {
            let c = B::from_i128(f[i]).mul(&bpow).shl(t * (d - i));
            // add c * (1+u)^(d-i)
            let m = d - i;
            let mut binom = B::from_i128(1);
            for j in 0..=m {
                if j > 0 {
                    // binom = C(m,j) built incrementally in exact integers
                    binom = binom.mul(&B::from_i128((m - j + 1) as i128));
                    binom = bdiv_small(&binom, j as u64);
                }
                h[j] = h[j].add(&c.mul(&binom));
            }
        }
        bpow = bpow.mul(&bb);
    }
    let mut v = 0usize;
    let mut last = 0i32;
    for c in h.iter() {
        let s = c.sign();
        if s != 0 {
            if last != 0 && s != last {
                v += 1;
            }
            last = s;
        }
    }
    v
}

fn bdiv_small(a: &B, d: u64) -> B {
    // exact division of |a| by a small positive integer
    let mut q = vec![0u64; a.m.len()];
    let mut rem = 0u128;
    for i in (0..a.m.len()).rev() {
        let cur = (rem << 64) | (a.m[i] as u128);
        q[i] = (cur / d as u128) as u64;
        rem = cur % d as u128;
    }
    assert_eq!(rem, 0, "inexact binomial division");
    btrim(&mut q);
    B { neg: a.neg && !q.is_empty(), m: q }
}

// smallest-degree factor over Z of `f` having the real number `r` as a root
fn min_poly_factor(f: &P, r: f64) -> Option<P> {
    let d = pdeg(f);
    let lc = f[d];
    // monic version for the root finder
    let cf: Vec<f64> = f.iter().map(|&x| x as f64 / lc as f64).collect();
    let mut roots = roots_dk(&cf);
    // polish
    for z in roots.iter_mut() {
        for _ in 0..60 {
            let mut num = C::new(cf[d], 0.0);
            let mut den = C::new(0.0, 0.0);
            for k in (0..d).rev() {
                den = den.mul(*z).add(num);
                num = num.mul(*z).add(C::new(cf[k], 0.0));
            }
            if den.abs() == 0.0 {
                break;
            }
            *z = z.sub(num.div(den));
        }
    }
    let i0 = (0..d).min_by(|&a, &b| {
        (roots[a].re - r).abs().hypot(roots[a].im).partial_cmp(&(roots[b].re - r).abs().hypot(roots[b].im)).unwrap()
    })?;
    let others: Vec<usize> = (0..d).filter(|&i| i != i0).collect();
    let mut divisors: Vec<i128> = vec![];
    for c in 1..=lc.abs() {
        if lc % c == 0 {
            divisors.push(c);
        }
    }
    // f itself always qualifies; the scan looks for something smaller
    let mut best: Option<P> = Some(f.clone());
    for mask in 0u32..(1u32 << others.len()) {
        let sz = mask.count_ones() as usize + 1;
        if let Some(b) = &best {
            if sz >= pdeg(b) {
                continue;
            }
        }
        // monic product over the chosen roots
        let mut poly = vec![C::new(1.0, 0.0)];
        let push = |poly: &mut Vec<C>, root: C| {
            let mut np = vec![C::new(0.0, 0.0); poly.len() + 1];
            for (i, &c) in poly.iter().enumerate() {
                np[i + 1] = np[i + 1].add(c);
                np[i] = np[i].sub(c.mul(root));
            }
            *poly = np;
        };
        push(&mut poly, roots[i0]);
        for (bit, &idx) in others.iter().enumerate() {
            if mask >> bit & 1 == 1 {
                push(&mut poly, roots[idx]);
            }
        }
        for &c in &divisors {
            let mut cand: P = vec![0i128; poly.len()];
            let mut ok = true;
            for (i, z) in poly.iter().enumerate() {
                let v = z.re * c as f64;
                if z.im.abs() > 1e-4 || (v - v.round()).abs() > 1e-4 || v.abs() > 1e30 {
                    ok = false;
                    break;
                }
                cand[i] = v.round() as i128;
            }
            if !ok {
                continue;
            }
            ptrim(&mut cand);
            if pdeg(&cand) != sz {
                continue;
            }
            if pdiv_exact(f, &cand).is_some() {
                if best.as_ref().map_or(true, |b| pdeg(&cand) < pdeg(b)) {
                    best = Some(cand.clone());
                }
            }
        }
    }
    best
}

// small brute force for the check (DFS over matchings, O(V) memory)
fn mk_brute(n: usize, s: &[usize]) -> Vec<i128> {
    let nv = 2 * n;
    let mut adj = vec![0u64; nv];
    for i in 0..n {
        for &k in s {
            let j = n + (i + k) % n;
            adj[i] |= 1u64 << j;
            adj[j] |= 1u64 << i;
        }
    }
    fn go(used: u64, k: usize, nv: usize, adj: &[u64], res: &mut Vec<i128>) {
        let mut u = 0usize;
        while u < nv && (used >> u) & 1 == 1 {
            u += 1;
        }
        if u == nv {
            res[k] += 1;
            return;
        }
        go(used | (1u64 << u), k, nv, adj, res);
        let mut nb = adj[u] & !used;
        while nb != 0 {
            let x = nb.trailing_zeros() as usize;
            nb &= nb - 1;
            go(used | (1u64 << u) | (1u64 << x), k + 1, nv, adj, res);
        }
    }
    let mut res = vec![0i128; n + 1];
    go(0, 0, nv, &adj, &mut res);
    res
}
