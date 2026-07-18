// Fast achiever-parity C(k) at n=2^k+1 via the linearity-lemma divisor sieve (validated vs engine,
// k<=18, and vs normal form k<=21). O(n log log n + #{coprime prime-power pairs with product<=n}).
//   PA[v] = S0_A xor (sum_{D|v} r(D)),   r(D)=[floor(m/D) odd]
//   PB[v] = S0_B xor (sum_{D|v} beta_D)
//   beta_D = nod(D)&(RNr xor nod(D)r(D)) xor T(D),  T(D)=sum_{E!=D} nod(lcm(D,E)) r(E)
//   C(k) = xor_{v odd<=n} PA[v]&PB[v].     P = prime powers ≡3 (4), <= n.
// Build: rustc -O -C target-cpu=native fastC.rs -o /tmp/fastC && /tmp/fastC 24

use std::time::Instant;

fn main() {
    let k: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(24);
    let n: u64 = (1u64 << k) + 1;
    let m: u64 = 1u64 << (k - 1);
    let t0 = Instant::now();

    // --- bit-packed odd sieve for primes up to n ---
    let half = ((n >> 1) + 1) as usize; // index i <-> number 2i+1
    let mut comp = vec![0u64; (half >> 6) + 1];
    let is_set = |c: &Vec<u64>, i: usize| (c[i >> 6] >> (i & 63)) & 1 == 1;
    let set = |c: &mut Vec<u64>, i: usize| c[i >> 6] |= 1u64 << (i & 63);
    let mut i = 1usize;
    while (2 * i + 1) * (2 * i + 1) <= n as usize {
        if !is_set(&comp, i) {
            let p = 2 * i + 1;
            let mut j = (p * p - 1) / 2;
            while j < half {
                set(&mut comp, j);
                j += p;
            }
        }
        i += 1;
    }
    // prime powers ≡3 (4) up to n, with base-prime index; sorted by value
    let mut pp: Vec<u64> = Vec::new();
    let mut base: Vec<u64> = Vec::new();
    {
        let mut i = 1usize;
        while 2 * i + 1 <= n as usize {
            if !is_set(&comp, i) {
                let p = (2 * i + 1) as u64;
                if p % 4 == 3 {
                    let mut qa = p;
                    while qa <= n {
                        pp.push(qa);
                        base.push(p);
                        if qa > n / p { break; }
                        qa *= p;
                    }
                }
            }
            i += 1;
        }
    }
    // sort by value keeping base
    let mut order: Vec<usize> = (0..pp.len()).collect();
    order.sort_by_key(|&i| pp[i]);
    let ppv: Vec<u64> = order.iter().map(|&i| pp[i]).collect();
    let basev: Vec<u64> = order.iter().map(|&i| base[i]).collect();
    let np = ppv.len();
    eprintln!("k={} n={} |P|={} sieve {:.1}s", k, n, np, t0.elapsed().as_secs_f64());

    let r: Vec<u8> = ppv.iter().map(|&d| ((m / d) & 1) as u8).collect();
    let nod: Vec<u8> = ppv.iter().map(|&d| (((n / d + 1) / 2) & 1) as u8).collect();

    let mut s0a = 0u8;
    for i in 0..np { s0a ^= r[i] & nod[i]; }
    let rnr = s0a; // sum nod*r

    // t = #{nod&r=1}; binom(t,2) mod 2
    let mut tcnt: u64 = 0;
    for i in 0..np { if nod[i] & r[i] == 1 { tcnt += 1; } }
    let binom = ((tcnt * (tcnt.wrapping_sub(1)) / 2) & 1) as u8;

    // T[d] and S0B via unordered coprime pairs with product<=n, plus same-prime pairs
    let mut tarr = vec![0u8; np];
    let mut s0b = binom;
    // coprime pairs i<j, ppv[i]*ppv[j] <= n, different base
    for i in 0..np {
        let d = ppv[i];
        // j from i+1 while product<=n
        let mut j = i + 1;
        while j < np && d.checked_mul(ppv[j]).map_or(false, |x| x <= n) {
            if basev[j] != basev[i] {
                let de = d * ppv[j];
                let nde = (((n / de + 1) / 2) & 1) as u8;
                let rde = ((m / de) & 1) as u8;
                // T updates
                tarr[i] ^= nde & r[j];
                tarr[j] ^= nde & r[i];
                // S0B exact for this coprime pair (DE<=n)
                let act = (nod[i] & nod[j]) ^ nde;
                let mat = (r[i] & r[j]) ^ rde;
                if act == 1 { s0b ^= mat; }
                // remove binom overcount for this pair (it belongs to (i), not (ii))
                if nod[i] & nod[j] == 1 { s0b ^= r[i] & r[j]; }
            }
            j += 1;
        }
    }
    // same-prime pairs: group indices by base prime (base groups are NOT contiguous in value order)
    {
        use std::collections::HashMap;
        let mut groups: HashMap<u64, Vec<usize>> = HashMap::new();
        for i in 0..np { groups.entry(basev[i]).or_default().push(i); }
        for (_, g) in groups.iter() {
            if g.len() < 2 { continue; }
            // T updates: ordered a!=b
            for &a in g {
                for &b in g {
                    if a == b { continue; }
                    let l = ppv[a].max(ppv[b]);
                    let nl = (((n / l + 1) / 2) & 1) as u8;
                    tarr[a] ^= nl & r[b];
                }
            }
            // S0B same-prime (unordered a<b)
            for ia in 0..g.len() {
                for ib in (ia + 1)..g.len() {
                    let a = g[ia]; let b = g[ib];
                    let l = ppv[a].max(ppv[b]);
                    let nl = (((n / l + 1) / 2) & 1) as u8;
                    let rl = ((m / l) & 1) as u8;
                    let act = (nod[a] & nod[b]) ^ nl;
                    let mat = (r[a] & r[b]) ^ rl;
                    if act == 1 { s0b ^= mat; }
                }
            }
        }
    }
    let beta: Vec<u8> = (0..np)
        .map(|i| (nod[i] & (rnr ^ (nod[i] & r[i]))) ^ tarr[i])
        .collect();
    eprintln!("coeffs done {:.1}s  S0A={} S0B={}", t0.elapsed().as_secs_f64(), s0a, s0b);

    // sieve aA, aB over odd v (bit-packed): index (v-1)/2
    let vbits = ((n - 1) / 2 + 1) as usize;
    let words = (vbits >> 6) + 1;
    let mut aa = vec![0u64; words];
    let mut ab = vec![0u64; words];
    let flip = |arr: &mut Vec<u64>, d: u64| {
        // flip at all odd multiples of d: w = d, 3d, 5d, ... ; index (w-1)/2 = (d-1)/2 + step*d?
        // w = d*(2s+1), index = (w-1)/2. step in w is 2d, so index step is d.
        let mut w = d;
        while w <= n {
            let idx = ((w - 1) / 2) as usize;
            arr[idx >> 6] ^= 1u64 << (idx & 63);
            w += 2 * d;
        }
    };
    for i in 0..np { if r[i] == 1 { flip(&mut aa, ppv[i]); } }
    for i in 0..np { if beta[i] == 1 { flip(&mut ab, ppv[i]); } }

    // C = xor over odd v of (S0A^aA)&(S0B^aB)
    // = parity of #{v: (S0A^aA(v))=1 and (S0B^aB(v))=1}
    let mut cnt: u64 = 0;
    for widx in 0..words {
        // for each bit, aA and aB; account S0A,S0B flips
        let mut wa = aa[widx];
        let mut wb = ab[widx];
        if s0a == 1 { wa = !wa; }
        if s0b == 1 { wb = !wb; }
        let mut both = wa & wb;
        // mask off bits beyond vbits in the last word
        if widx == words - 1 {
            let valid = vbits - (widx << 6);
            if valid < 64 { both &= (1u64 << valid) - 1; }
        }
        cnt += both.count_ones() as u64;
    }
    let c = (cnt & 1) as u8;
    println!("k={} C={} ({})  {:.1}s", k, c, if c == 1 { "ODD" } else { "EVEN" }, t0.elapsed().as_secs_f64());
}
