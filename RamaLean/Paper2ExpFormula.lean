/-
# The exponential formula for `Sᵣ` — removing the last citation from Paper 2

Statement (integer form, any commutative ring `R`): for `f : ℕ → R`, let

    A r := Σ_{σ : Perm (Fin r)} f(1)^{r − |cycleType σ|.sum} · ∏_{ℓ ∈ cycleType σ} f(ℓ)

(the total cycle-weight of `σ`, counting fixed points with weight `f 1`). Then

    r · A r = Σ_{k=1}^{r} r^{(k)} · f k · A (r − k),      r^{(k)} = r!/(r−k)!.

Dividing by `r!` this is exactly the recurrence `r·Φᵣ = Σ f_k·Φᵣ₋ₖ` for the
`Sᵣ`-average `Φ r = A r / r!` — the hypothesis `hexp` of `thm1_general` in
`Paper2General.lean`. Together with that theorem, the *entire* chain from
"per-permutation cycle weights" to the Chebyshev closed form is machine-checked;
the only remaining cited input for Paper 2's Theorem 1 is the elementary
spectral fact that a lift of `Cₙ` by `σ` has characteristic polynomial
`∏_{cycles ℓ of σ} (2T_{nℓ}(x/2) − 2)`.

Proof strategy:
1. Group the sum over `Perm (Fin r)` by cycle type (`Finset.sum_comp`).
2. Cauchy's formula (Mathlib: `Equiv.Perm.card_of_cycleType_mul_eq`) in
   product form `N(m)·z(m) = r!` — no division anywhere.
3. The recurrence at the cycle-type level by re-indexing "(type, marked part)"
   pairs, with the coefficient identities proved in `ℕ` by cancellation.
-/
import RamaLean.Paper2General

namespace Paper2

open Equiv Finset

variable {R : Type*} [CommRing R]

/-! ## Cycle-type weights and counts -/

/-- Weight of a cycle type `m` in ambient size `r`: fixed points (there are
`r − m.sum` of them) contribute `f 1`, and each genuine cycle `ℓ ∈ m`
contributes `f ℓ`. -/
def typeWeight (f : ℕ → R) (r : ℕ) (m : Multiset ℕ) : R :=
  f 1 ^ (r - m.sum) * (m.map f).prod

/-- Total cycle-weight of a permutation. -/
def permWeight (f : ℕ → R) {r : ℕ} (σ : Perm (Fin r)) : R :=
  typeWeight f r σ.cycleType

/-- The `Sᵣ`-total `A r = Σ_σ permWeight σ`. -/
def permTotal (f : ℕ → R) (r : ℕ) : R :=
  ∑ σ : Perm (Fin r), permWeight f σ

/-- Valid cycle types for ambient size `r`. -/
def IsType (r : ℕ) (m : Multiset ℕ) : Prop := m.sum ≤ r ∧ ∀ a ∈ m, 2 ≤ a

instance {r : ℕ} {m : Multiset ℕ} : Decidable (IsType r m) := by
  unfold IsType; infer_instance

/-- Number of permutations of `Fin r` with cycle type `m`. -/
def typeCount (r : ℕ) (m : Multiset ℕ) : ℕ :=
  #({σ | σ.cycleType = m} : Finset (Perm (Fin r)))

/-- The Cauchy denominator `z(m)` for ambient size `r`:
`(r − m.sum)! · ∏_{ℓ∈m} ℓ · ∏_n (count n)!`. -/
def zFactor (r : ℕ) (m : Multiset ℕ) : ℕ :=
  (r - m.sum).factorial * m.prod * ∏ n ∈ m.toFinset, (m.count n).factorial

/-- The finset of achieved cycle types. -/
def types (r : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ : Finset (Perm (Fin r))).image Equiv.Perm.cycleType

lemma mem_types_iff {r : ℕ} {m : Multiset ℕ} : m ∈ types r ↔ IsType r m := by
  rw [types, Finset.mem_image]
  constructor
  · rintro ⟨σ, -, rfl⟩
    exact ⟨by simpa using σ.sum_cycleType_le,
           fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin r)).mpr
      ⟨by simpa using h1, h2⟩
    exact ⟨σ, Finset.mem_univ σ, hσ⟩

/-- **Cauchy's formula** (Mathlib), specialized: `typeCount·zFactor = r!` for
valid types, `0` otherwise. -/
lemma typeCount_mul_zFactor (r : ℕ) (m : Multiset ℕ) :
    typeCount r m * zFactor r m = if IsType r m then r.factorial else 0 := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin r) m
  simpa [typeCount, zFactor, IsType, mul_assoc, Fintype.card_fin] using h

lemma zFactor_pos (r : ℕ) {m : Multiset ℕ} (hm : ∀ a ∈ m, 2 ≤ a) :
    0 < zFactor r m := by
  refine Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) ?_) ?_
  · exact Multiset.prod_pos fun a ha => lt_of_lt_of_le (by norm_num) (hm a ha)
  · exact Finset.prod_pos fun n _ => Nat.factorial_pos _

/-- Grouping the permutation sum by cycle type. -/
lemma permTotal_eq_type_sum (f : ℕ → R) (r : ℕ) :
    permTotal f r = ∑ m ∈ types r, (typeCount r m : R) * typeWeight f r m := by
  classical
  rw [permTotal, types]
  rw [show (∑ σ : Perm (Fin r), permWeight f σ)
      = ∑ σ ∈ (Finset.univ : Finset (Perm (Fin r))),
          typeWeight f r σ.cycleType from rfl]
  rw [Finset.sum_comp (typeWeight f r) Equiv.Perm.cycleType]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [nsmul_eq_mul]
  congr 1

/-! ## The `ℕ`-level coefficient identities (Cauchy cancellation) -/

/-- `r!/(r−k)!` in product form: `descFactorial · (r−k)! = r!`. -/
lemma descFactorial_mul_factorial {k r : ℕ} (h : k ≤ r) :
    r.descFactorial k * (r - k).factorial = r.factorial := by
  rw [mul_comm, Nat.factorial_mul_descFactorial h]

/-- `zFactor` under incrementing the ambient size. -/
lemma zFactor_ambient {r : ℕ} {m : Multiset ℕ} (hr : 1 ≤ r) (h : m.sum ≤ r - 1) :
    zFactor r m = (r - m.sum) * zFactor (r - 1) m := by
  unfold zFactor
  have e1 : r - m.sum = (r - 1 - m.sum) + 1 := by omega
  rw [e1, Nat.factorial_succ]
  ring

/-- `zFactor` of a cons: pulls out `k · (count k + 1)`. -/
lemma zFactor_cons {r k : ℕ} {m : Multiset ℕ} (h : k + m.sum ≤ r) :
    zFactor r (k ::ₘ m) = k * (m.count k + 1) * zFactor (r - k) m := by
  classical
  unfold zFactor
  have e1 : r - (k ::ₘ m).sum = (r - k) - m.sum := by
    rw [Multiset.sum_cons]; omega
  have e2 : (k ::ₘ m).prod = k * m.prod := Multiset.prod_cons k m
  have e3 : (∏ n ∈ (k ::ₘ m).toFinset, ((k ::ₘ m).count n).factorial)
      = (m.count k + 1) * ∏ n ∈ m.toFinset, (m.count n).factorial := by
    by_cases hk : k ∈ m
    · have hkt : k ∈ m.toFinset := Multiset.mem_toFinset.mpr hk
      have ht : (k ::ₘ m).toFinset = m.toFinset := by
        rw [Multiset.toFinset_cons, Finset.insert_eq_self]
        exact hkt
      have hcongr : (∏ n ∈ m.toFinset.erase k, ((k ::ₘ m).count n).factorial)
          = ∏ n ∈ m.toFinset.erase k, (m.count n).factorial := by
        refine Finset.prod_congr rfl fun n hn => ?_
        rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hn)]
      rw [ht, ← Finset.mul_prod_erase _ _ hkt, hcongr,
          Multiset.count_cons_self, Nat.factorial_succ,
          ← Finset.mul_prod_erase _ (fun n => (m.count n).factorial) hkt]
      ring
    · have hkt : k ∉ m.toFinset := fun hc => hk (Multiset.mem_toFinset.mp hc)
      have hcongr : (∏ n ∈ m.toFinset, ((k ::ₘ m).count n).factorial)
          = ∏ n ∈ m.toFinset, (m.count n).factorial := by
        refine Finset.prod_congr rfl fun n hn => ?_
        have : n ≠ k := by rintro rfl; exact hkt hn
        rw [Multiset.count_cons_of_ne this]
      rw [Multiset.toFinset_cons, Finset.prod_insert hkt, hcongr,
          Multiset.count_cons_self, Multiset.count_eq_zero_of_notMem hk]
      norm_num
  rw [e1, e2, e3]
  ring

/-- Coefficient identity, fixed-point case (`k = 1`):
`(r − m.sum)·N_r(m) = r·N_{r−1}(m)`. -/
lemma count_ambient {r : ℕ} {m : Multiset ℕ} (hr : 1 ≤ r)
    (hm : IsType (r - 1) m) :
    (r - m.sum) * typeCount r m = r * typeCount (r - 1) m := by
  have hz : 0 < zFactor r m := zFactor_pos r hm.2
  apply Nat.eq_of_mul_eq_mul_right hz
  have hmr : IsType r m := ⟨le_trans hm.1 (by omega), hm.2⟩
  have c1 := typeCount_mul_zFactor r m
  have c2 := typeCount_mul_zFactor (r - 1) m
  rw [if_pos hmr] at c1
  rw [if_pos hm] at c2
  calc (r - m.sum) * typeCount r m * zFactor r m
      = (r - m.sum) * (typeCount r m * zFactor r m) := by ring
    _ = (r - m.sum) * r.factorial := by rw [c1]
    _ = r * ((r - m.sum) * (r-1).factorial) := by
        have : r.factorial = r * (r-1).factorial := by
          conv_lhs => rw [show r = (r-1) + 1 by omega]
          rw [Nat.factorial_succ]
          congr 1 <;> omega
        rw [this]; ring
    _ = r * typeCount (r - 1) m * zFactor r m := by
        rw [← c2, zFactor_ambient hr hm.1]; ring

/-- Coefficient identity, cycle case (`k ≥ 2`):
`k·(count k + 1)·N_r(k ::ₘ m) = r^{(k)}·N_{r−k}(m)`. -/
lemma count_cons {r k : ℕ} {m : Multiset ℕ} (hk2 : 2 ≤ k)
    (hks : k + m.sum ≤ r) (hm : ∀ a ∈ m, 2 ≤ a) :
    k * (m.count k + 1) * typeCount r (k ::ₘ m)
      = r.descFactorial k * typeCount (r - k) m := by
  have hmc : ∀ a ∈ (k ::ₘ m), 2 ≤ a := by
    intro a ha
    rcases Multiset.mem_cons.mp ha with rfl | h
    · exact hk2
    · exact hm a h
  have hz : 0 < zFactor r (k ::ₘ m) := zFactor_pos r hmc
  apply Nat.eq_of_mul_eq_mul_right hz
  have hT1 : IsType r (k ::ₘ m) := by
    refine ⟨?_, hmc⟩
    rw [Multiset.sum_cons]; omega
  have hT2 : IsType (r - k) m := ⟨by omega, hm⟩
  have c1 := typeCount_mul_zFactor r (k ::ₘ m)
  have c2 := typeCount_mul_zFactor (r - k) m
  rw [if_pos hT1] at c1
  rw [if_pos hT2] at c2
  calc k * (m.count k + 1) * typeCount r (k ::ₘ m) * zFactor r (k ::ₘ m)
      = k * (m.count k + 1) * (typeCount r (k ::ₘ m) * zFactor r (k ::ₘ m)) := by ring
    _ = k * (m.count k + 1) * r.factorial := by rw [c1]
    _ = k * (m.count k + 1) * (r.descFactorial k * (r - k).factorial) := by
        rw [descFactorial_mul_factorial (by omega)]
    _ = r.descFactorial k * (typeCount (r-k) m * zFactor (r-k) m)
          * (k * (m.count k + 1)) := by rw [c2]; ring
    _ = r.descFactorial k * typeCount (r - k) m * zFactor r (k ::ₘ m) := by
        rw [zFactor_cons hks]; ring

/-! ## Weight identities -/

lemma typeWeight_ambient (f : ℕ → R) {r : ℕ} {m : Multiset ℕ}
    (hr : 1 ≤ r) (h : m.sum ≤ r - 1) :
    typeWeight f r m = f 1 * typeWeight f (r - 1) m := by
  unfold typeWeight
  rw [show r - m.sum = (r - 1 - m.sum) + 1 by omega, pow_succ]
  ring

lemma typeWeight_cons (f : ℕ → R) {r k : ℕ} {m : Multiset ℕ}
    (h : k + m.sum ≤ r) :
    typeWeight f r (k ::ₘ m) = f k * typeWeight f (r - k) m := by
  unfold typeWeight
  rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons,
      show r - (k + m.sum) = (r - k) - m.sum by omega]
  ring

/-! ## The two pieces of the marked-point double count -/

lemma types_mono {r : ℕ} (hr : 1 ≤ r) : types (r - 1) ⊆ types r := by
  intro m hm
  rw [mem_types_iff] at hm ⊢
  obtain ⟨h1, h2⟩ := hm
  exact ⟨by omega, h2⟩

/-- Fixed-point piece (`k = 1`). -/
lemma piece_one (f : ℕ → R) {r : ℕ} (hr : 1 ≤ r) :
    (∑ m ∈ types r, ((r - m.sum : ℕ) : R)
        * ((typeCount r m : R) * typeWeight f r m))
      = (r.descFactorial 1 : R) * f 1 * permTotal f (r - 1) := by
  classical
  have hvanish : ∀ m ∈ types r, m ∉ types (r - 1) →
      ((r - m.sum : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m) = 0 := by
    intro m hm hnot
    rw [mem_types_iff] at hm hnot
    obtain ⟨hm1, hm2⟩ := hm
    have hsum : m.sum = r := by
      by_contra hne
      have hlt : m.sum ≤ r - 1 := by omega
      exact hnot ⟨hlt, hm2⟩
    rw [hsum]
    simp
  rw [Nat.descFactorial_one, permTotal_eq_type_sum,
      ← Finset.sum_subset (types_mono hr) hvanish, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mem_types_iff] at hm
  obtain ⟨hm1, hm2⟩ := hm
  have hcount : ((r - m.sum) * typeCount r m : ℕ)
      = (r * typeCount (r - 1) m : ℕ) := count_ambient hr ⟨hm1, hm2⟩
  have hw := typeWeight_ambient f (r := r) hr hm1
  calc ((r - m.sum : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m)
      = (((r - m.sum) * typeCount r m : ℕ) : R) * typeWeight f r m := by
        push_cast; ring
    _ = ((r * typeCount (r - 1) m : ℕ) : R) * (f 1 * typeWeight f (r-1) m) := by
        rw [hcount, hw]
    _ = (r : R) * f 1 * ((typeCount (r - 1) m : R) * typeWeight f (r-1) m) := by
        push_cast; ring

/-- Cycle piece (`k ≥ 2`), by re-indexing (type, marked part) pairs. -/
lemma piece_two (f : ℕ → R) {r : ℕ} (hr : 1 ≤ r) :
    (∑ m ∈ types r, ((m.sum : ℕ) : R)
        * ((typeCount r m : R) * typeWeight f r m))
      = ∑ k ∈ Finset.Icc 2 r, (r.descFactorial k : R) * f k * permTotal f (r - k) := by
  classical
  -- expand m.sum over the parts of m
  have hsum_expand : ∀ m ∈ types r,
      ((m.sum : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m)
        = ∑ k ∈ m.toFinset, ((k * m.count k : ℕ) : R)
            * ((typeCount r m : R) * typeWeight f r m) := by
    intro m _
    rw [← Finset.sum_mul]
    congr 1
    have : m.sum = ∑ k ∈ m.toFinset, m.count k * k := by
      conv_lhs => rw [show m.sum = (m.map id).sum by simp]
      rw [Finset.sum_multiset_map_count]
      simp [smul_eq_mul]
    rw [this]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl hsum_expand]
  -- convert both sides to sigma sums and re-index
  rw [Finset.sum_sigma']
  have hR : ∀ k ∈ Finset.Icc 2 r,
      (r.descFactorial k : R) * f k * permTotal f (r - k)
        = ∑ m' ∈ types (r - k),
            (r.descFactorial k : R) * f k
              * ((typeCount (r-k) m' : R) * typeWeight f (r-k) m') := by
    intro k _
    rw [permTotal_eq_type_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl hR, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1.erase p.2⟩)
    (fun q => ⟨q.1 ::ₘ q.2, q.1⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    rintro ⟨m, k⟩ hp
    rw [Finset.mem_sigma] at hp ⊢
    dsimp only at hp ⊢
    obtain ⟨hm, hk⟩ := hp
    rw [mem_types_iff] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hkm : k ∈ m := Multiset.mem_toFinset.mp hk
    have hk2 : 2 ≤ k := hm2 k hkm
    have hks : k ≤ m.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) k hkm
    have herase_sum : (m.erase k).sum = m.sum - k := by
      have := Multiset.sum_cons k (m.erase k)
      rw [Multiset.cons_erase hkm] at this
      omega
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hk2, le_trans hks hm1⟩
    · rw [mem_types_iff]
      refine ⟨?_, fun a ha => hm2 a (Multiset.mem_of_mem_erase ha)⟩
      rw [herase_sum]
      omega
  · -- backward membership
    rintro ⟨k, m'⟩ hq
    rw [Finset.mem_sigma] at hq ⊢
    dsimp only at hq ⊢
    obtain ⟨hk, hm'⟩ := hq
    rw [Finset.mem_Icc] at hk
    rw [mem_types_iff] at hm'
    obtain ⟨hs', hp'⟩ := hm'
    constructor
    · rw [mem_types_iff]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [Multiset.sum_cons]; omega
      · rcases Multiset.mem_cons.mp ha with rfl | h
        · exact hk.1
        · exact hp' a h
    · rw [Multiset.mem_toFinset]
      exact Multiset.mem_cons_self k m'
  · -- left inverse
    rintro ⟨m, k⟩ hp
    dsimp only at hp ⊢
    rw [Finset.mem_sigma] at hp
    have hkm : k ∈ m := Multiset.mem_toFinset.mp hp.2
    simp only [Multiset.cons_erase hkm]
  · -- right inverse
    rintro ⟨k, m'⟩ _
    dsimp only
    simp only [Multiset.erase_cons_head]
  · -- term equality
    rintro ⟨m, k⟩ hp
    dsimp only at hp ⊢
    rw [Finset.mem_sigma] at hp
    obtain ⟨hm, hk⟩ := hp
    rw [mem_types_iff] at hm
    have hkm : k ∈ m := Multiset.mem_toFinset.mp hk
    have hk2 : 2 ≤ k := hm.2 k hkm
    have hparts : ∀ a ∈ m.erase k, 2 ≤ a :=
      fun a ha => hm.2 a (Multiset.mem_of_mem_erase ha)
    have herase_sum : k + (m.erase k).sum = m.sum := by
      have := Multiset.sum_cons k (m.erase k)
      rw [Multiset.cons_erase hkm] at this
      omega
    have hks : k + (m.erase k).sum ≤ r := by rw [herase_sum]; exact hm.1
    have hcount : (k * ((m.erase k).count k + 1) * typeCount r (k ::ₘ m.erase k) : ℕ)
        = (r.descFactorial k * typeCount (r - k) (m.erase k) : ℕ) :=
      count_cons hk2 hks hparts
    have hcc : (m.erase k).count k + 1 = m.count k := by
      have := Multiset.count_cons_self k (m.erase k)
      rw [show (k ::ₘ m.erase k) = m from Multiset.cons_erase hkm] at this
      omega
    have hw : typeWeight f r m = f k * typeWeight f (r - k) (m.erase k) := by
      conv_lhs => rw [show m = k ::ₘ m.erase k from (Multiset.cons_erase hkm).symm]
      exact typeWeight_cons f hks
    rw [hcc] at hcount
    have hcount' : (k * m.count k * typeCount r m : ℕ)
        = (r.descFactorial k * typeCount (r - k) (m.erase k) : ℕ) := by
      rwa [show (k ::ₘ m.erase k) = m from Multiset.cons_erase hkm] at hcount
    calc ((k * m.count k : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m)
        = ((k * m.count k * typeCount r m : ℕ) : R) * typeWeight f r m := by
          push_cast; ring
      _ = ((r.descFactorial k * typeCount (r - k) (m.erase k) : ℕ) : R)
            * (f k * typeWeight f (r - k) (m.erase k)) := by rw [hcount', hw]
      _ = (r.descFactorial k : R) * f k
            * ((typeCount (r-k) (m.erase k) : R) * typeWeight f (r-k) (m.erase k)) := by
          push_cast; ring

/-! ## The exponential formula (integer form) -/

/-- **Exponential formula for `Sᵣ`, integer form.** For any `f : ℕ → R`,

`r · Σ_{σ ∈ Sᵣ} W(σ) = Σ_{k=1}^{r} r^{(k)} · f k · Σ_{σ ∈ S_{r−k}} W(σ)`

where `W(σ) = f(1)^{#fixed points} · ∏_{ℓ ∈ cycleType σ} f(ℓ)` and `r^{(k)}`
is the descending factorial. Dividing by `r!` gives the Newton recurrence for
the `Sᵣ`-average of cycle weights. -/
theorem expFormula (f : ℕ → R) {r : ℕ} (hr : 1 ≤ r) :
    (r : R) * permTotal f r
      = ∑ k ∈ Finset.Icc 1 r,
          (r.descFactorial k : R) * f k * permTotal f (r - k) := by
  classical
  have hIcc : Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp), permTotal_eq_type_sum, Finset.mul_sum]
  have hsplit : ∀ m ∈ types r,
      (r : R) * ((typeCount r m : R) * typeWeight f r m)
        = ((r - m.sum : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m)
          + ((m.sum : ℕ) : R) * ((typeCount r m : R) * typeWeight f r m) := by
    intro m hm
    rw [mem_types_iff] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have : ((r : ℕ) : R) = ((r - m.sum : ℕ) : R) + ((m.sum : ℕ) : R) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [this]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      piece_one f hr, piece_two f hr]

/-! ## The `Sᵣ`-average version (over a `ℚ`-algebra) and the capstone -/

variable [Algebra ℚ R]

/-- The `Sᵣ`-average `Φ r = (1/r!)·Σ_σ W(σ)` — the expected cycle weight of a
uniformly random permutation. -/
noncomputable def permAvg (f : ℕ → R) (r : ℕ) : R :=
  algebraMap ℚ R (1 / r.factorial) * permTotal f r

lemma permAvg_zero (f : ℕ → R) : permAvg f 0 = 1 := by
  rw [permAvg, permTotal]
  rw [show (∑ σ : Perm (Fin 0), permWeight f σ) = 1 from ?_]
  · simp
  · rw [Finset.univ_unique, Finset.sum_singleton]
    show typeWeight f 0 (Equiv.Perm.cycleType _) = 1
    rw [show (default : Perm (Fin 0)) = 1 from Subsingleton.elim _ _,
        Equiv.Perm.cycleType_one]
    simp [typeWeight]

/-- **The Newton/exponential-formula recurrence for the `Sᵣ`-average.**
This is exactly the hypothesis `hexp` of `thm1_general`. -/
theorem permAvg_newton (f : ℕ → R) {r : ℕ} (hr : 1 ≤ r) :
    (r : R) * permAvg f r
      = ∑ k ∈ Finset.Icc 1 r, f k * permAvg f (r - k) := by
  unfold permAvg
  have h := expFormula f hr
  calc (r : R) * (algebraMap ℚ R (1 / r.factorial) * permTotal f r)
      = algebraMap ℚ R (1 / r.factorial) * ((r : R) * permTotal f r) := by ring
    _ = algebraMap ℚ R (1 / r.factorial)
          * ∑ k ∈ Finset.Icc 1 r,
              (r.descFactorial k : R) * f k * permTotal f (r - k) := by rw [h]
    _ = ∑ k ∈ Finset.Icc 1 r, f k
          * (algebraMap ℚ R (1 / (r-k).factorial) * permTotal f (r - k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        have key : algebraMap ℚ R (1 / r.factorial) * (r.descFactorial k : R)
            = algebraMap ℚ R (1 / (r - k).factorial) := by
          rw [show ((r.descFactorial k : ℕ) : R)
              = algebraMap ℚ R ((r.descFactorial k : ℕ) : ℚ) by
                rw [map_natCast], ← map_mul]
          congr 1
          rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff]
          · rw [one_mul, ← Nat.cast_mul, descFactorial_mul_factorial hk.2]
          · exact_mod_cast (Nat.factorial_pos r).ne'
          · exact_mod_cast (Nat.factorial_pos (r-k)).ne'
        calc algebraMap ℚ R (1 / r.factorial)
              * ((r.descFactorial k : R) * f k * permTotal f (r - k))
            = (algebraMap ℚ R (1 / r.factorial) * (r.descFactorial k : R))
                * f k * permTotal f (r - k) := by ring
          _ = algebraMap ℚ R (1 / (r-k).factorial) * f k * permTotal f (r-k) := by
              rw [key]
          _ = f k * (algebraMap ℚ R (1 / (r-k).factorial) * permTotal f (r-k)) := by
              ring

open Polynomial in
/-- **Capstone: Paper 2's Theorem 1 with the exponential formula built in.**

The expected cycle weight of a uniformly random `σ ∈ Sᵣ`, with per-cycle
factor `f(ℓ) = 2·T_{nℓ}(t) − 2` (the characteristic polynomial of `C_{nℓ}`
at `x = 2t`), equals the Chebyshev closed form `cG(Tₙ(t))` — for every `n`
and `r`, over any `ℚ`-algebra domain (e.g. `ℚ[x]`).

Since a permutation lift of `Cₙ` by `σ` decomposes into cycles `C_{nℓ}`,
`ℓ ∈ cycleType σ` (with fixed points giving copies of `Cₙ`), the left side
is exactly the expected characteristic polynomial `Φ_{Cₙ,r}(x)` at `x = 2t`;
THAT spectral decomposition is now the only unformalized input of Paper 2. -/
theorem thm1_Sr [IsDomain R] (t : R) (n : ℕ) (r : ℕ) :
    permAvg (fun k => 2 * (Chebyshev.T R ((n * k : ℕ) : ℤ)).eval t - 2) r
      = cG ((Chebyshev.T R (n : ℤ)).eval t) r := by
  haveI : CharZero R := charZero_of_injective_algebraMap
    (algebraMap ℚ R).injective
  exact thm1_general t n _ (permAvg_zero _)
    (fun s hs => permAvg_newton _ hs) r

end Paper2
