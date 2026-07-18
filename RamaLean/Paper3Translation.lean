import Mathlib
open Finset

/-!
# The translation identity: the gcd-χ₄ window count is periodic with period `2v`

The engine of Theorem A (word-sum invariant) and of the words' very well-definedness: the boundary
window counts of the deficit mechanism (Paper 3 §7) are periodic in the scale because the map
`w ↦ w + 2v` preserves oddness (`2v` even) and the gcd (`gcd(v, w + 2v) = gcd(v, w)`, as `2v` is a
multiple of `v`). Hence the gcd-χ₄ odd-count of any window of length `2v` is a constant `t₃(v)`, the
count of one period, and the deficit word `word_v[i]` is a well-defined periodic sequence.

Machine-checked here as `count_period_shift`; with the reflection identity
(`Paper3Negation.count_reflect`) these are the two symmetries on which the entire word theory —
periodicity, the anti-period law, and the class-number ladder — rests.
-/
namespace Paper3Translation

/-- Shifting a window by the period `2v` preserves the gcd-χ₄ odd-count. -/
theorem count_period_shift (v a b : ℕ) :
    ((Finset.Ioc a b).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = ((Finset.Ioc (a + 2 * v) (b + 2 * v)).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  apply Finset.card_bij (fun w _ => w + 2 * v)
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_Ioc] at hw
    obtain ⟨⟨haw, hwb⟩, hodd, hgcd⟩ := hw
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [Nat.gcd_add_mul_right_right v w 2]
    exact hgcd
  · intro w hw w' hw' h
    omega
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_Ioc] at hu
    obtain ⟨⟨hau, hub⟩, hodd, hgcd⟩ := hu
    refine ⟨u - 2 * v, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    have hbig : 2 * v ≤ u := by omega
    have hg : Nat.gcd v ((u - 2 * v) + 2 * v) = Nat.gcd v (u - 2 * v) :=
      Nat.gcd_add_mul_right_right v (u - 2 * v) 2
    rw [show (u - 2 * v) + 2 * v = u by omega] at hg
    rw [← hg]
    exact hgcd

/-- Consequence: any two length-`2v` windows carry the same gcd-χ₄ odd-count (the constant `t₃(v)`).
The words are therefore periodic; `Paper3Negation.count_reflect` gives the reflection symmetry. -/
theorem count_period_eq (v a k : ℕ) :
    ((Finset.Ioc a (a + 2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = ((Finset.Ioc (a + 2 * v * k) (a + 2 * v * k + 2 * v)).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  have gcdshift : ∀ x, Nat.gcd v (x + 2 * v * k) = Nat.gcd v x := by
    intro x
    have h := Nat.gcd_add_mul_right_right v x (2 * k)
    rwa [show 2 * k * v = 2 * v * k by ring] at h
  have hpar : (2 * v * k) % 2 = 0 := by
    rw [show 2 * v * k = 2 * (v * k) by ring]; omega
  apply Finset.card_bij (fun w _ => w + 2 * v * k)
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_Ioc] at hw
    obtain ⟨⟨haw, hwb⟩, hodd, hgcd⟩ := hw
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [gcdshift w]
    exact hgcd
  · intro w hw w' hw' h
    omega
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_Ioc] at hu
    obtain ⟨⟨hau, hub⟩, hodd, hgcd⟩ := hu
    refine ⟨u - 2 * v * k, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    have hg := gcdshift (u - 2 * v * k)
    rw [show (u - 2 * v * k) + 2 * v * k = u by omega] at hg
    rw [← hg]
    exact hgcd

/-- **Full-period block count** (the quantitative core of Theorem A's strip decomposition): the
gcd-χ₄ odd-count over `q` consecutive periods is `q · t₃(v)`, where `t₃(v)` is the single-period
count. This is the "full periods" term of `strip = q·t₃ + boundary` in the word-sum invariant. -/
theorem count_qperiods (v a q : ℕ) :
    ((Finset.Ioc a (a + 2 * v * q)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = q * ((Finset.Ioc a (a + 2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  induction q with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Ioc a (a + 2 * v * (n + 1))
        = Finset.Ioc a (a + 2 * v * n) ∪ Finset.Ioc (a + 2 * v * n) (a + 2 * v * (n + 1)) := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by nlinarith [Nat.zero_le v])]
    have hdisj : Disjoint
        ((Finset.Ioc a (a + 2 * v * n)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3))
        ((Finset.Ioc (a + 2 * v * n) (a + 2 * v * (n + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)) := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Ioc] at hx hx'
      omega
    -- the second block is one period shifted by `2*v*n`, hence has the single-period count
    have hblock : ((Finset.Ioc (a + 2 * v * n) (a + 2 * v * (n + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
        = ((Finset.Ioc a (a + 2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
      have h := count_period_eq v a n
      have e1 : a + 2 * v * n = a + 2 * v * n := rfl
      have e2 : a + 2 * v * (n + 1) = a + 2 * v * n + 2 * v := by ring
      rw [e2, ← h]
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih, hblock]
    ring

/-- **Strip decomposition** (Theorem A's Euclidean structure): the gcd-χ₄ odd-count over an interval
`(a, a + 2v·q + s]` splits as `q · t₃(v)` (full periods) plus the boundary-window count over the
remaining length `s`. This is exactly `strip = (full periods)·t₃ + boundary` — the shape the
word-sum invariant telescopes. -/
theorem count_strip_decomp (v a q s : ℕ) :
    ((Finset.Ioc a (a + 2 * v * q + s)).filter
        (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = q * ((Finset.Ioc a (a + 2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
        + ((Finset.Ioc (a + 2 * v * q) (a + 2 * v * q + s)).filter
            (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  have hsplit : Finset.Ioc a (a + 2 * v * q + s)
      = Finset.Ioc a (a + 2 * v * q) ∪ Finset.Ioc (a + 2 * v * q) (a + 2 * v * q + s) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
  have hdisj : Disjoint
      ((Finset.Ioc a (a + 2 * v * q)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3))
      ((Finset.Ioc (a + 2 * v * q) (a + 2 * v * q + s)).filter
        (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, count_qperiods]

/-- Additivity of the gcd-χ₄ count over a split interval `(x, z] = (x, y] ⊔ (y, z]`. -/
private lemma count_add_split {v x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    ((Finset.Ioc x z).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = ((Finset.Ioc x y).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
        + ((Finset.Ioc y z).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  have hu : Finset.Ioc x z = Finset.Ioc x y ∪ Finset.Ioc y z :=
    (Finset.Ioc_union_Ioc_eq_Ioc hxy hyz).symm
  have hd : Disjoint
      ((Finset.Ioc x y).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3))
      ((Finset.Ioc y z).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro p hp hp'
    rw [Finset.mem_Ioc] at hp hp'; omega
  rw [hu, Finset.filter_union, Finset.card_union_of_disjoint hd]

/-- **Offset-independence of the period count** (the telescoping core of Theorem A): every window of
length `2v` carries the same gcd-χ₄ odd-count `t₃(v)`, regardless of where it starts, since the
indicator `w ↦ [w odd ∧ gcd(v,w) ≡ 3 (4)]` has period `2v`. Hence the counting function increments by
exactly `t₃(v)` each period — the identity that telescopes in the word-sum invariant. -/
theorem count_window_offset (v a : ℕ) :
    ((Finset.Ioc a (a + 2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  rcases Nat.eq_zero_or_pos v with hv0 | hvpos
  · subst hv0; simp
  · set s := a % (2 * v) with hs
    have hslt : s < 2 * v := Nat.mod_lt a (by omega)
    have hk : s + 2 * v * (a / (2 * v)) = a := by
      have := Nat.mod_add_div a (2 * v); omega
    -- reduce offset a to s (mod 2v)
    have h1 := count_period_eq v s (a / (2 * v))
    rw [hk] at h1
    rw [← h1]
    -- count over (s, s+2v] = count over (s, 2v] + count over (2v, s+2v]
    rw [count_add_split (v := v) (by omega : s ≤ 2 * v) (by omega : 2 * v ≤ s + 2 * v)]
    -- count over (2v, s+2v] = count over (0, s]  (shift by 2v)
    have h2 := count_period_shift v 0 s
    simp only [Nat.zero_add] at h2
    rw [← h2]
    -- count over (0, 2v] = count over (0, s] + count over (s, 2v]
    rw [count_add_split (v := v) (by omega : (0:ℕ) ≤ s) (by omega : s ≤ 2 * v)]
    ring

/-- **Strip-sum telescoping** (the range half of Theorem A's telescoping): the per-scale strip counts
over the dyadic strips `(2^i, 2^{i+1}]`, `i < m`, sum to the single count over `(1, 2^m]`, because the
strips tile that range. -/
theorem count_strip_telescope (v m : ℕ) :
    (Finset.range m).sum
        (fun i => ((Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card)
      = ((Finset.Ioc 1 (2 ^ m)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 2 ^ n ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
    rw [← count_add_split (v := v) h2 h3]

/-- **Per-scale strip decomposition** (dyadic form): the gcd-χ₄ count over the strip
`(2^i, 2^{i+1}]` equals `q_i · t₃(v)` (full periods, `q_i = 2^i /(2v)`, `t₃(v)` = period count over
`(0,2v]`) plus the boundary count over `(2^i + 2v·q_i, 2^{i+1}]`. -/
theorem strip_dyadic (v i : ℕ) (hv : 0 < v) :
    ((Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
      = (2 ^ i / (2 * v))
          * ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
        + ((Finset.Ioc (2 ^ i + 2 * v * (2 ^ i / (2 * v))) (2 ^ (i + 1))).filter
            (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  classical
  set q := 2 ^ i / (2 * v) with hq
  set r := 2 ^ i % (2 * v) with hr
  have hdm : 2 * v * q + r = 2 ^ i := by rw [hq, hr]; exact Nat.div_add_mod (2 ^ i) (2 * v)
  have hpow : 2 ^ (i + 1) = 2 ^ i + 2 * v * q + r := by rw [pow_succ]; omega
  -- rewrite the strip's upper endpoint and apply count_strip_decomp
  have hkey := count_strip_decomp v (2 ^ i) q r
  rw [show 2 ^ i + 2 * v * q + r = 2 ^ (i + 1) from hpow.symm] at hkey
  rw [hkey]
  -- the local period count over (2^i, 2^i+2v] equals t₃(v) = count over (0,2v]
  rw [count_window_offset v (2 ^ i)]

/-- **Boundary-sum assembly** (the telescoping identity behind the word-sum invariant): summed over
any set of scales, `Σ strip = t₃(v)·Σ q + Σ boundary`, i.e. the boundary counts (whose parities are
the deficit word bits) sum to `Σ strip − t₃·Σ q`. With `count_strip_telescope` this reduces the
word-sum to `(Σ strip) ⊕ t₃·(Σ q)` (mod 2), the last step before the orbit/`wt` evaluation. -/
theorem boundary_sum (v : ℕ) (s : Finset ℕ) (hv : 0 < v) :
    s.sum (fun i => ((Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter
        (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card)
      = ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card
          * s.sum (fun i => 2 ^ i / (2 * v))
        + s.sum (fun i => ((Finset.Ioc (2 ^ i + 2 * v * (2 ^ i / (2 * v))) (2 ^ (i + 1))).filter
            (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [strip_dyadic v i hv, Nat.mul_comm]

/-- **Full-range evenness** (orbit fact (1) of the word-sum invariant): if `2^m ≡ 1 (mod v)` (e.g.
`m = ord_v(2)`) and `base ≥ 2`, the gcd-χ₄ count over `(2^base, 2^{base+m}]` is even, because the
range spans exactly `q = 2^{base-1}·(2^m-1)/v` full periods and `q` is even. This is the term that
vanishes mod 2 in `Σstrip ⊕ t₃·Σq ≡ wt·t₃`. -/
theorem count_full_range_even (v m base : ℕ) (hv : 0 < v) (hb : 2 ≤ base) (hm : 2 ^ m % v = 1) :
    ((Finset.Ioc (2 ^ base) (2 ^ (base + m))).filter
        (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card % 2 = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ m = v * c + 1 := by
    refine ⟨2 ^ m / v, ?_⟩
    have h := Nat.div_add_mod (2 ^ m) v; omega
  have hthis : 2 * 2 ^ (base - 1) = 2 ^ base := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ base)]
  have key : 2 * v * (2 ^ (base - 1) * c) = 2 ^ base * v * c := by
    calc 2 * v * (2 ^ (base - 1) * c) = (2 * 2 ^ (base - 1)) * v * c := by ring
      _ = 2 ^ base * v * c := by rw [hthis]
  have hbm : 2 ^ (base + m) = 2 ^ base + 2 * v * (2 ^ (base - 1) * c) := by
    rw [key, pow_add, hc]; ring
  rw [hbm, count_qperiods]
  have hqeven : (2 : ℕ) ∣ (2 ^ (base - 1) * c) := by
    refine Dvd.dvd.mul_right ?_ c
    rw [show base - 1 = (base - 2) + 1 by omega, pow_succ]
    exact ⟨2 ^ (base - 2), by ring⟩
  obtain ⟨q', hq'⟩ := hqeven
  rw [hq', Nat.mul_assoc]
  omega

/-- Shifted strip telescoping: the strips `(2^i, 2^{i+1}]` for `i ∈ [base, base+m)` tile
`(2^base, 2^{base+m}]`. -/
theorem strip_telescope_ico (v base m : ℕ) :
    (Finset.Ico base (base + m)).sum
        (fun i => ((Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card)
      = ((Finset.Ioc (2 ^ base) (2 ^ (base + m))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show base + (n + 1) = (base + n) + 1 by ring,
        Finset.sum_Ico_succ_top (by omega : base ≤ base + n), ih]
    have h2 : (2 : ℕ) ^ base ≤ 2 ^ (base + n) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (2 : ℕ) ^ (base + n) ≤ 2 ^ (base + n + 1) := by rw [pow_succ]; omega
    rw [← count_add_split (v := v) h2 h3]

/-- **The word-sum invariant (Theorem A), machine-checked.** For odd `v>0` with `2^m ≡ 1 (mod v)`
(`m = ord_v(2)`) and `base ≥ 2`, the sum of the deficit word bits over one period equals
`wt(v)·t₃(v) (mod 2)`, where `wt(v) = Σ_{i} ⌊2^i/(2v)⌋ mod 2` is the number of `1`s in the binary
period of `1/v` and `t₃(v)` is the single-period gcd-χ₄ count. Assembled from the telescoping core:
`Σ strip = t₃·Σ q + Σ boundary` (`boundary_sum`), `Σ strip` = the full-range count which is even
(`count_full_range_even`), and `Σ q ≡ wt (mod 2)`. -/
theorem word_sum_invariant (v m base : ℕ) (hv : 0 < v) (hb : 2 ≤ base) (hm : 2 ^ m % v = 1) :
    ((Finset.Ico base (base + m)).sum (fun i =>
        ((Finset.Ioc (2 ^ i + 2 * v * (2 ^ i / (2 * v))) (2 ^ (i + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card)) % 2
      = (((Finset.Ico base (base + m)).sum (fun i => 2 ^ i / (2 * v) % 2))
          * ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card) % 2 := by
  classical
  -- Σ strip = t₃·Σ q + Σ boundary
  have hbs := boundary_sum v (Finset.Ico base (base + m)) hv
  -- Σ strip = count over (2^base, 2^{base+m}]
  rw [strip_telescope_ico v base m] at hbs
  -- that full-range count is even
  have hzero := count_full_range_even v m base hv hb hm
  -- Σ q ≡ Σ (q mod 2) = wt
  have hq := Finset.sum_nat_mod (Finset.Ico base (base + m)) 2 (fun i => 2 ^ i / (2 * v))
  -- abbreviations
  set Q := (Finset.Ico base (base + m)).sum (fun i => 2 ^ i / (2 * v)) with hQ
  set W := (Finset.Ico base (base + m)).sum (fun i => 2 ^ i / (2 * v) % 2) with hW
  set T := ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card with hT
  set B := (Finset.Ico base (base + m)).sum (fun i =>
      ((Finset.Ioc (2 ^ i + 2 * v * (2 ^ i / (2 * v))) (2 ^ (i + 1))).filter
        (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card) with hB
  -- hbs : count = T * Q + B ; hzero : count % 2 = 0
  -- T*Q ≡ T*W (mod 2) since Q ≡ W
  have hmodq : Q ≡ W [MOD 2] := by unfold Nat.ModEq; omega
  have hTQW : T * Q ≡ T * W [MOD 2] := hmodq.mul_left T
  rw [Nat.mul_comm W T]
  unfold Nat.ModEq at hTQW
  omega

/-- **The word-sum invariant, unconditional in `m`** (the multiplicative order supplied via Euler).
For odd `v ≥ 3` and scale `base ≥ 2`, taking `m = φ(v)` (so `2^m ≡ 1 (mod v)` by Euler's theorem,
`v` being coprime to `2`), the word-sum invariant `Σ word ≡ wt·t₃ (mod 2)` holds with no hypothesis
on the period. -/
theorem word_sum_invariant_totient (v base : ℕ) (hodd : v % 2 = 1) (hv : 2 ≤ v) (hb : 2 ≤ base) :
    ((Finset.Ico base (base + v.totient)).sum (fun i =>
        ((Finset.Ioc (2 ^ i + 2 * v * (2 ^ i / (2 * v))) (2 ^ (i + 1))).filter
          (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card)) % 2
      = (((Finset.Ico base (base + v.totient)).sum (fun i => 2 ^ i / (2 * v) % 2))
          * ((Finset.Ioc 0 (2 * v)).filter (fun w => w % 2 = 1 ∧ Nat.gcd v w % 4 = 3)).card) % 2 := by
  have hm : 2 ^ v.totient % v = 1 := by
    have hcop : Nat.Coprime 2 v := by rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hodd
    have h := Nat.ModEq.pow_totient hcop
    have h1 : (1 : ℕ) % v = 1 := Nat.mod_eq_of_lt (by omega)
    unfold Nat.ModEq at h; omega
  exact word_sum_invariant v v.totient base (by omega) hb hm

end Paper3Translation
