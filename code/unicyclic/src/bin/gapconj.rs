// CONJECTURE UNDER TEST.  Hall-Puder-Sawin: every root of mu_{d,G} lies in the Ramanujan
// INTERVAL [-rho,rho], rho = spectral radius of the universal cover T.  For b_1(G)=1 we proved
// the stronger statement: roots lie in spec(T), which has gaps.  Does that hold for ALL G?
//
// For d=1 this is classical (Godsil: matching-polynomial roots are eigenvalues of the path tree).
// Test d>=2 on BIREGULAR bipartite graphs, whose universal cover is an (a,b)-biregular tree with
// KNOWN spectrum  {0} u +-[ |sqrt(a-1)-sqrt(b-1)| , sqrt(a-1)+sqrt(b-1) ]  -- a genuine gap.
// K_{2,3}: degrees 3 and 2 -> gap (0, sqrt2 - 1) = (0, 0.41421).
// K_{2,4}: degrees 4 and 2 -> gap (0, sqrt3 - 1) = (0, 0.73205).
// A root strictly inside a gap refutes; none supports.

fn perms(r: usize) -> Vec<Vec<usize>> {
    let mut out = vec![]; let mut c: Vec<usize> = (0..r).collect();
    fn rec(k: usize, c: &mut Vec<usize>, o: &mut Vec<Vec<usize>>) {
        if k == c.len() { o.push(c.clone()); return; }
        for i in k..c.len() { c.swap(k, i); rec(k + 1, c, o); c.swap(k, i); } }
    rec(0, &mut c, &mut out); out
}
// matching polynomial sum_k (-1)^k m_k x^{n-2k}
fn matching_poly(n: usize, edges: &[(usize, usize)]) -> Vec<i128> {
    let mut cnt = vec![0i128; n / 2 + 2];
    fn rec(i: usize, used: u128, k: usize, e: &[(usize, usize)], c: &mut Vec<i128>) {
        c[k] += 1;
        for j in i..e.len() { let (u, v) = e[j];
            let b = (1u128 << u) | (1u128 << v);
            if used & b == 0 { rec(j + 1, used | b, k + 1, e, c); } } }
    rec(0, 0, 0, edges, &mut cnt);
    let mut p = vec![0i128; n + 1];
    for (k, &c) in cnt.iter().enumerate() { if 2 * k <= n {
        p[n - 2 * k] += if k % 2 == 0 { c } else { -c }; } }
    p
}
fn main() {
    // (name, n, edges, free-edge indices after gauge fixing, gap upper end)
    let tests: Vec<(&str, usize, Vec<(usize, usize)>, Vec<usize>, f64)> = vec![
        // K_{2,3}: parts {0,1} and {2,3,4}; spanning tree = (0,2),(0,3),(0,4),(1,2); free = (1,3),(1,4)
        ("K_{2,3}", 5, vec![(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)], vec![4,5], 2f64.sqrt() - 1.0),
        // K_{2,4}: parts {0,1} and {2,3,4,5}; free = (1,3),(1,4),(1,5)
        ("K_{2,4}", 6, vec![(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5)], vec![5,6,7], 3f64.sqrt() - 1.0),
    ];
    for (name, n, edges, free, gap_hi) in tests.iter() {
        println!("=== {}  universal cover gap = (0, {:.5}) ===", name, gap_hi);
        let dmax = if *name == "K_{2,3}" { 4 } else { 3 };
        for d in 1..=dmax {
            let ps = perms(d);
            let mut sel = vec![0usize; free.len()];
            let mut tot: Vec<i128> = vec![0; n * d + 1];
            let mut cnt = 0i128;
            loop {
                let mut le = vec![];
                for (ei, &(u, v)) in edges.iter().enumerate() {
                    let p: &Vec<usize> = match free.iter().position(|&f| f == ei) {
                        Some(k) => &ps[sel[k]], None => &ps[0] };
                    for i in 0..d { le.push((u * d + i, v * d + p[i])); }
                }
                let mp = matching_poly(n * d, &le);
                for (i, c) in mp.iter().enumerate() { tot[i] += c; }
                cnt += 1;
                let mut k = 0;
                loop { if k == free.len() { break; }
                    sel[k] += 1; if sel[k] < ps.len() { break; } sel[k] = 0; k += 1; }
                if k == free.len() { break; }
            }
            let poly: Vec<f64> = tot.iter().map(|&c| c as f64 / cnt as f64).collect();
            let ev = |x: f64| poly.iter().rev().fold(0.0, |a, &k| a * x + k);
            // find real roots by sign change + bisection on a fine grid
            let (lo, hi, m) = (-3.5f64, 3.5f64, 700_000usize);
            let mut roots = vec![]; let mut px = lo; let mut pv = ev(lo);
            for i in 1..=m {
                let x = lo + (hi - lo) * (i as f64) / (m as f64);
                let v = ev(x);
                if pv * v < 0.0 {
                    let (mut l, mut r) = (px, x);
                    for _ in 0..100 { let mid = 0.5*(l+r);
                        if ev(l) * ev(mid) <= 0.0 { r = mid; } else { l = mid; } }
                    roots.push(0.5*(l+r));
                }
                px = x; pv = v;
            }
            // any root strictly inside the gap (0, gap_hi) or its mirror, excluding 0 itself?
            let viol: Vec<f64> = roots.iter().cloned()
                .filter(|&r| r.abs() > 1e-6 && r.abs() < gap_hi - 1e-6).collect();
            println!("  d={}  deg={}  {:3} real roots  |  roots inside the gap: {}",
                     d, n * d, roots.len(),
                     if viol.is_empty() { "NONE".to_string() }
                     else { format!("{:?}", viol) });
        }
        println!();
    }
    println!("NONE at every d => the roots of mu_d respect the universal cover's spectral gap,");
    println!("for graphs of first Betti number 2 and 3, where the Floquet proof does not apply.");
}
