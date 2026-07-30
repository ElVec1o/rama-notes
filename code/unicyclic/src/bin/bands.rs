// Roots of mu_{d,G} are eigenvalues of A_G(e^{i k pi/(d+1)}).  For b_1(G)=1 the pi_1 is Z, so the
// Z-cover IS the universal cover, and by Floquet-Bloch its spectrum is
//     S = union over theta of spec(A_G(e^{i theta})) = { x : |y(x)| <= 1 },  y = -A/(2B).
// HPS give: roots of mu_d lie in the Ramanujan INTERVAL [-rho, rho].  If S has gaps strictly
// inside that interval, then the Floquet description is strictly stronger: the roots lie in the
// BANDS, and can never enter a gap, for any d.  This program measures the gaps.
fn main() {
    // (name, A coeffs low->high, B coeffs low->high)
    let gs: Vec<(&str, Vec<f64>, Vec<f64>)> = vec![
        ("C_3",                vec![0.,-3.,0.,1.],              vec![-1.]),
        ("C_5",                vec![0.,5.,0.,-5.,0.,1.],        vec![-1.]),
        ("tadpole T(3,1)",     vec![1.,0.,-4.,0.,1.],           vec![0.,-1.]),
        ("tadpole T(4,1)",     vec![0.,4.,0.,-5.,0.,1.],        vec![0.,-1.]),
        ("C_3 + 2 pendants",   vec![0.,3.,0.,-5.,0.,1.],        vec![0.,0.,-1.]),
        ("C_3 + path P2",      vec![0.,4.,0.,-5.,0.,1.],        vec![1.,0.,-1.]),
        ("C_3 + star K_1,3",   vec![0.,0.,3.,0.,-6.,0.,1.],     vec![0.,0.,0.,-1.]),
        ("C_4 + path P3",      vec![0.,-6.,0.,13.,0.,-7.,0.,1.],vec![0.,2.,0.,-1.]),
    ];
    let ev = |c: &Vec<f64>, x: f64| c.iter().rev().fold(0.0, |a, &k| a * x + k);
    for (name, a, b) in gs.iter() {
        let (lo, hi, n) = (-4.0f64, 4.0f64, 4_000_000usize);
        let inband = |x: f64| {
            let bb = ev(b, x); let aa = ev(a, x);
            if bb.abs() < 1e-9 { return aa.abs() < 1e-6; }
            (aa / (2.0 * bb)).abs() <= 1.0
        };
        // collect maximal band intervals
        let mut bands: Vec<(f64, f64)> = vec![];
        let mut cur: Option<f64> = None;
        for i in 0..=n {
            let x = lo + (hi - lo) * (i as f64) / (n as f64);
            if inband(x) { if cur.is_none() { cur = Some(x); } }
            else if let Some(s) = cur.take() { if x - s > 1e-6 { bands.push((s, x)); } }
        }
        if let Some(s) = cur { bands.push((s, hi)); }
        if bands.is_empty() { println!("  {:20} (no bands found)", name); continue; }
        let rho = bands.iter().fold(0.0f64, |m, &(s, e)| m.max(s.abs()).max(e.abs()));
        let band_len: f64 = bands.iter().map(|&(s, e)| e - s).sum();
        let interval_len = 2.0 * rho;
        let gap_frac = 1.0 - band_len / interval_len;
        println!("  {:20} rho = {:.4}   bands = {}   gap fraction of [-rho,rho] = {:.1}%",
                 name, rho, bands.len(), 100.0 * gap_frac);
        let shown: Vec<String> = bands.iter().map(|&(s, e)| format!("[{:.3},{:.3}]", s, e)).collect();
        println!("       bands: {}", shown.join(" u "));
    }
    println!("\n  A nonzero gap fraction means: HPS place the roots of mu_d in [-rho,rho];");
    println!("  for b_1 = 1 they in fact lie in the bands, and never in a gap, for any d.");
}
// appended check runs via `bands check`
