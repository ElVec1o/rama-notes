import RamaLean.ScratchTwoMatch

namespace ScratchTwoMatch

/-- K_{2,2}: all four edges of Fin 2 × Fin 2. -/
def K22 : Finset (Fin 2 × Fin 2) := Finset.univ

#eval (mCount K22 2, (confL K22).card, (confR K22).card, K22.card)
#eval ((Finset.univ : Finset (Fin 2)).image (fun v => dL K22 v))
#eval (2 * mCount K22 2 + (confL K22).card + (confR K22).card, K22.card * (K22.card - 1))

/-- A path P_3: edges (0,0),(0,1),(1,1) inside Fin 2 × Fin 2. -/
def P3 : Finset (Fin 2 × Fin 2) := {(0,0), (0,1), (1,1)}

#eval (mCount P3 2, (confL P3).card, (confR P3).card, P3.card)
#eval (2 * mCount P3 2 + (confL P3).card + (confR P3).card, P3.card * (P3.card - 1))
#eval ((confL P3).card, ∑ v ∈ P3.image Prod.fst, dL P3 v * (dL P3 v - 1))
#eval ((confR P3).card, ∑ u ∈ P3.image Prod.snd, dR P3 u * (dR P3 u - 1))

#print axioms two_mul_mCount_two_add_conflicts
#print axioms card_confL
#print axioms card_confR

end ScratchTwoMatch
