// Grade profile of a(n) = per[gcd(i,j)] via the 2-adic grade decomposition
//   a(n) = sum_w N_w * 2^w,   N_w = grade of 2-adic weight w.
// Computes per(M(t)) = sum_w N_w t^w exactly mod 2^64, where
//   M(i,j) = gcd(odd(i),odd(j)) * t^{min(v2(i),v2(j))},
// via Ryser over (Z/2^64)[t] with Gray-code column updates.
//
// PURPOSE (deficit tension, Paper 3): at the peaks n=2^k+1, does the w=0 grade
//   strictly dominate (min of w+v2(N_w) uniquely at w=0)?  For k=3,4 the margin
//   was 1,4 (growing).  n=33 (k=5) is the decisive point: a large margin -> w=0
//   keeps dominating -> deficit BOUNDED (turnover at k=6, D(65)=5); a small or
//   negative margin -> a low grade competes -> deficit UNBOUNDED (D(65)=8).
//
// v2(N_w) is read as trailing_zeros of (N_w mod 2^64); correct whenever v2<64
// (here v2 <= v2(n!) = 31 for n=33).  Two's-complement wraparound handles the
// Ryser signs.  Resumable: checkpoints (g, acc, rows) every ~2 min.
//
// Build & run (one line):
//   rustc -C opt-level=3 -C target-cpu=native grade_profile.rs -o /tmp/gp && /tmp/gp 33
//
// Runtime ~ a few hours for n=33 (2^33 subsets).  Progress + ETA printed live;
// on Ctrl-C or crash, rerun the same command to resume from the last checkpoint.

use std::time::Instant;
use std::io::{Write, Read};
use std::convert::TryInto;

fn v2(mut x: u64) -> usize { if x == 0 { return 64; } let mut v = 0; while x & 1 == 0 { x >>= 1; v += 1; } v }
fn oddpart(mut x: u64) -> u64 { while x & 1 == 0 { x >>= 1; } x }
fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }

fn ckpt_path(n: usize) -> String { format!("/tmp/gp_ckpt_n{}.bin", n) }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(33);
    assert!(n >= 1 && n <= 40);

    // Matrix entries: monomial c[i][j] * t^{e[i][j]}.
    let mut e = vec![vec![0usize; n]; n];
    let mut c = vec![vec![0u64; n]; n];
    for i in 0..n {
        let vi = v2((i + 1) as u64);
        let oi = oddpart((i + 1) as u64);
        for j in 0..n {
            e[i][j] = vi.min(v2((j + 1) as u64));
            c[i][j] = gcd(oi, oddpart((j + 1) as u64));
        }
    }
    let maxdeg: usize = (1..=n).map(|i| v2(i as u64)).sum(); // = v2(n!)
    let dsize = maxdeg + 1;
    // per-row max degree = v2(i+1) (nonzero coeffs of rowsum_i live at exps <= this)
    let rideg: Vec<usize> = (0..n).map(|i| v2((i + 1) as u64).min(maxdeg)).collect();

    let mut rows = vec![vec![0u64; dsize]; n];  // rowsum_i(S)
    let mut acc = vec![0u64; dsize];            // partial Ryser sum -> N_w mod 2^64
    let total: u64 = 1u64 << n;
    let mut g_start: u64 = 1;
    let mut prev_gray: u64 = 0;

    // ---- resume from checkpoint if present ----
    if let Ok(mut f) = std::fs::File::open(ckpt_path(n)) {
        let mut buf = Vec::new();
        if f.read_to_end(&mut buf).is_ok() && buf.len() == 8 + 8 + dsize * 8 + n * dsize * 8 {
            let rd = |b: &[u8]| u64::from_le_bytes(b.try_into().unwrap());
            let mut p = 0usize;
            g_start = rd(&buf[p..p + 8]); p += 8;
            prev_gray = rd(&buf[p..p + 8]); p += 8;
            for w in 0..dsize { acc[w] = rd(&buf[p..p + 8]); p += 8; }
            for i in 0..n { for w in 0..dsize { rows[i][w] = rd(&buf[p..p + 8]); p += 8; } }
            g_start += 1;
            eprintln!("[resumed from g={} ({:.2}%)]", g_start, 100.0 * g_start as f64 / total as f64);
        }
    }

    let start = Instant::now();
    let report_every: u64 = 1 << 24;
    let mut prod = vec![0u64; dsize];
    let mut tmp = vec![0u64; dsize];

    for g in g_start..total {
        let gray = g ^ (g >> 1);
        let diff = gray ^ prev_gray;
        let j = diff.trailing_zeros() as usize;
        let add = (gray & diff) != 0;
        if add {
            for i in 0..n { let ei = e[i][j]; rows[i][ei] = rows[i][ei].wrapping_add(c[i][j]); }
        } else {
            for i in 0..n { let ei = e[i][j]; rows[i][ei] = rows[i][ei].wrapping_sub(c[i][j]); }
        }
        prev_gray = gray;

        // prod = product_i rowsum_i  (truncated to degree maxdeg)
        for x in prod.iter_mut() { *x = 0; }
        prod[0] = 1;
        let mut curdeg = 0usize;
        for i in 0..n {
            let rd_i = rideg[i];
            let newdeg = (curdeg + rd_i).min(maxdeg);
            for x in tmp[0..=newdeg].iter_mut() { *x = 0; }
            for a in 0..=curdeg {
                let pa = prod[a];
                if pa == 0 { continue; }
                for b in 0..=rd_i {
                    let cb = rows[i][b];
                    if cb != 0 && a + b <= maxdeg {
                        tmp[a + b] = tmp[a + b].wrapping_add(pa.wrapping_mul(cb));
                    }
                }
            }
            curdeg = newdeg;
            prod[0..=curdeg].copy_from_slice(&tmp[0..=curdeg]);
        }

        let k = gray.count_ones() as usize;
        if (n - k) & 1 == 0 {
            for w in 0..dsize { acc[w] = acc[w].wrapping_add(prod[w]); }
        } else {
            for w in 0..dsize { acc[w] = acc[w].wrapping_sub(prod[w]); }
        }

        if g % report_every == 0 {
            let done = g as f64 / total as f64;
            let el = start.elapsed().as_secs_f64();
            let rate = (g - g_start + 1) as f64 / el;
            let eta = (total - g) as f64 / rate;
            eprint!("\r  n={} {:6.2}%  elapsed {:.0}s  ETA {:.0}s   ", n, 100.0 * done, el, eta);
            std::io::stderr().flush().ok();
            // checkpoint
            let mut out = Vec::with_capacity(8 + 8 + dsize * 8 + n * dsize * 8);
            out.extend_from_slice(&g.to_le_bytes());
            out.extend_from_slice(&prev_gray.to_le_bytes());
            for w in 0..dsize { out.extend_from_slice(&acc[w].to_le_bytes()); }
            for i in 0..n { for w in 0..dsize { out.extend_from_slice(&rows[i][w].to_le_bytes()); } }
            let tmpf = format!("{}.tmp", ckpt_path(n));
            if let Ok(mut f) = std::fs::File::create(&tmpf) { f.write_all(&out).ok(); std::fs::rename(&tmpf, ckpt_path(n)).ok(); }
        }
    }
    eprintln!();

    // ---- report ----
    // a(n) = sum_w N_w 2^w  (mod 2^64): reconstruct v2(a) as a cross-check.
    let mut a_mod: u64 = 0;
    for w in 0..dsize { a_mod = a_mod.wrapping_add(acc[w].wrapping_shl(w as u32)); }
    println!("n = {}   maxdeg=v2(n!) = {}", n, maxdeg);
    println!("{:>3} {:>10} {:>12}", "w", "v2(N_w)", "w+v2(N_w)");
    let mut best = usize::MAX; let mut best2 = usize::MAX; let mut argmin = Vec::new();
    for w in 0..dsize {
        if acc[w] == 0 { continue; } // N_w == 0 mod 2^64 (v2>=64: impossible here) or truly 0
        let vn = acc[w].trailing_zeros() as usize;
        let tot = w + vn;
        println!("{:>3} {:>10} {:>12}", w, vn, tot);
        if tot < best { best2 = best; best = tot; argmin = vec![w]; }
        else if tot == best { argmin.push(w); }
        else if tot < best2 { best2 = tot; }
    }
    let margin = if best2 == usize::MAX { 999 } else { best2 - best };
    println!("\nmin_w (w+v2(N_w)) = {}   at w = {:?}   MARGIN to 2nd = {}", best, argmin, margin);
    println!("v2(a(n)) = {}  (should equal the min above if w=0 dominates w/o cancellation)", a_mod.trailing_zeros());
    println!("--> if argmin=[0] and MARGIN large: w=0 dominates => deficit turns over (BOUNDED, D(65)=5).");
    println!("--> if a low w competes/wins: => deficit UNBOUNDED (D(65)=8).");
    std::fs::remove_file(ckpt_path(n)).ok();
}
