// Independent check: build V_d from the RECURRENCE (not the product formula), find its real roots
// by bisection, and confirm every root lies in a band {|y|<=1} and none in a gap.
fn ev(c: &[f64], x: f64) -> f64 { c.iter().rev().fold(0.0, |a, &k| a * x + k) }
fn mul(a: &[f64], b: &[f64]) -> Vec<f64> {
    let mut r = vec![0.0; a.len() + b.len() - 1];
    for (i, &u) in a.iter().enumerate() { for (j, &v) in b.iter().enumerate() { r[i + j] += u * v; } }
    r
}
fn sub(a: &[f64], b: &[f64]) -> Vec<f64> {
    let n = a.len().max(b.len());
    (0..n).map(|i| a.get(i).copied().unwrap_or(0.0) - b.get(i).copied().unwrap_or(0.0)).collect()
}
fn main() {
    let gs: Vec<(&str, Vec<f64>, Vec<f64>)> = vec![
        ("tadpole T(3,1)",   vec![1.,0.,-4.,0.,1.],            vec![0.,-1.]),
        ("C_3 + 2 pendants", vec![0.,3.,0.,-5.,0.,1.],         vec![0.,0.,-1.]),
        ("C_3 + path P2",    vec![0.,4.,0.,-5.,0.,1.],         vec![1.,0.,-1.]),
        ("C_3 + star K_1,3", vec![0.,0.,3.,0.,-6.,0.,1.],      vec![0.,0.,0.,-1.]),
        ("C_4 + path P3",    vec![0.,-6.,0.,13.,0.,-7.,0.,1.], vec![0.,2.,0.,-1.]),
    ];
    for (name, a, b) in gs.iter() {
        let b2 = mul(b, b);
        let mut prev = vec![1.0];
        let mut cur = a.clone();
        let mut worst_gap_hits = 0usize;
        let mut total_roots = 0usize;
        for d in 1..=3usize {
            if d >= 2 { let next = sub(&mul(a, &cur), &mul(&b2, &prev)); prev = cur; cur = next; }
            // find real roots of `cur` by sign change + bisection
            let (lo, hi, n) = (-4.0f64, 4.0f64, 400_000usize);
            let mut roots = vec![];
            let mut px = lo; let mut pv = ev(&cur, lo);
            for i in 1..=n {
                let x = lo + (hi - lo) * (i as f64) / (n as f64);
                let v = ev(&cur, x);
                if pv == 0.0 { roots.push(px); }
                else if pv * v < 0.0 {
                    let (mut l, mut r) = (px, x);
                    for _ in 0..80 { let m = 0.5 * (l + r);
                        if ev(&cur, l) * ev(&cur, m) <= 0.0 { r = m; } else { l = m; } }
                    roots.push(0.5 * (l + r));
                }
                px = x; pv = v;
            }
            for &r in &roots {
                total_roots += 1;
                let bb = ev(b, r); let aa = ev(a, r);
                let ok = if bb.abs() < 1e-7 { aa.abs() < 1e-5 }
                         else { (aa / (2.0 * bb)).abs() <= 1.0 + 1e-6 };
                if !ok { worst_gap_hits += 1; }
            }
            if d == 3 {
                println!("  {:20} d=1..3: {:3} roots found (expect deg sum), {} outside bands",
                         name, total_roots, worst_gap_hits);
            }
        }
    }
    println!("\n  0 outside => every root of mu_d, for every d tested, lies in a band.");
}
