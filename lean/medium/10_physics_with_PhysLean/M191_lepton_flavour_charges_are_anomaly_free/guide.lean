/- Guide for M191 (Lepton-flavour charges are anomaly free).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on an object that is NOT the exercise's (a quark-flavour charge).
Assumed: Lean basics.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMRHN SMνCharges SMνACCs

namespace M191Guide

/-! # Part R · Reference entries -/

/-! ## Before anything: a hypothesis over the right index type -/

/-! ### R1. `have h' : T' := h` · context gains `h'`, the same fact at a type `T'` equal to `T` by unfolding
The `_decomp` sums run over `Fin (SMνSpecies n).numberCharges`; `SMνSpecies n` is defined with
`numberCharges := n`, so this is `Fin n` after unfolding, and `:= h` is accepted. Both print as `∑ i, g i`. -/
example {n : ℕ} (g : Fin n → ℚ) (c : ℚ) (h : ∑ i, g i = c) (P : ℚ → Prop) (hP : P c) :
    P (∑ i : Fin (SMνSpecies n).numberCharges, g i) := by
  have h' : ∑ i : Fin (SMνSpecies n).numberCharges, g i = c := h
  rw [h']
  exact hP

/-! ## From `IsSolution` to six anomaly equations -/

/-! ### R2. `ACCSystem.IsSolution` · goal: `χ.IsSolution S` is by definition `∃ sol, sol.val = S`
`(PlusU1 n).Sols` are the charge vectors bundled with proofs of all six ACCs; `sol.val` is the vector.
`unfold` shows the `∃`; `refine ⟨sol, rfl⟩` (R3) works without unfolding. -/
example {n : ℕ} (S : (PlusU1 n).Charges) (h : ∃ sol : (PlusU1 n).Sols, sol.val = S) :
    (PlusU1 n).IsSolution S := by
  unfold ACCSystem.IsSolution
  exact h

/-! ### R3. `refine ⟨PlusU1.chargeToAF S ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩` · goal list: one goal → six ACC goals
`PlusU1.chargeToAF S` takes the six proofs `accGrav S = 0`, …, `accCube S = 0` and returns a
`(PlusU1 n).Sols` whose `.val` is `S` by definition, so `rfl` proves the second component. -/
example {n : ℕ} (S : (PlusU1 n).Charges) (hG : accGrav S = 0) (h2 : accSU2 S = 0)
    (h3 : accSU3 S = 0) (hY : accYY S = 0) (hQ : accQuad S = 0) (hC : accCube S = 0) :
    (PlusU1 n).IsSolution S := by
  refine ⟨PlusU1.chargeToAF S ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
  exacts [hG, h2, h3, hY, hQ, hC]

/-! ## Each ACC as sums over families (`Q S i` is the charge of species `Q` in family `i`) -/

/-! ### R4. `rw [accGrav_decomp]` · goal -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i
      + ∑ i, N S i = 0) : accGrav S = 0 := by
  rw [accGrav_decomp]
  exact h

/-! ### R5. `rw [accSU2_decomp]` · goal (only the `SU(2)` doublets `Q`, `L`) -/
example {n : ℕ} (S : (SMνCharges n).Charges) (h : 3 * ∑ i, Q S i + ∑ i, L S i = 0) :
    accSU2 S = 0 := by
  rw [accSU2_decomp]
  exact h

/-! ### R6. `rw [accSU3_decomp]` · goal (only the quarks `Q`, `U`, `D`) -/
example {n : ℕ} (S : (SMνCharges n).Charges) (h : 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i = 0) :
    accSU3 S = 0 := by
  rw [accSU3_decomp]
  exact h

/-! ### R7. `rw [accYY_decomp]` · goal (no `N`: the neutrino has hypercharge 0) -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i = 0) :
    accYY S = 0 := by
  rw [accYY_decomp]
  exact h

/-! ### R8. `rw [accQuad_decomp]` · goal: sums of squares -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2
      + ∑ i, E S i ^ 2 = 0) : accQuad S = 0 := by
  rw [accQuad_decomp]
  exact h

/-! ### R9. `rw [accCube_decomp]` · goal: weighted sums of cubes -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3
      + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3 = 0) : accCube S = 0 := by
  rw [accCube_decomp]
  exact h

/-! ## Reading off the species charges -/

/-! ### R10. `simp only [C]` · goal: the name of a charge vector → its `toSpeciesEquiv.symm …` body
`C y` gives `y f` to `Q` and `−y f` to `U`, `D` in family `f` (a quark-flavour charge). -/
def C {n : ℕ} (y : Fin n → ℚ) : (PlusU1 n).Charges :=
  toSpeciesEquiv.symm fun s f => ![1, -1, -1, 0, 0, 0] s * y f

example {n : ℕ} (y : Fin n → ℚ) (i : Fin (SMνSpecies n).numberCharges) (P : ℚ → Prop)
    (h : P (Q (toSpeciesEquiv.symm fun s f => ![1, -1, -1, 0, 0, 0] s * y f) i)) :
    P (Q (C y) i) := by
  simp only [C]
  exact h

/-! ### R11. `toSMSpecies_toSpecies_inv` · goal: species `j` of `toSpeciesEquiv.symm g` → `g j`
`toSpeciesEquiv : (SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ)` views a charge vector as a table
(species, family) ↦ charge; `.symm` goes back. `Q` is `toSpecies 0`, …, `N` is `toSpecies 5`. -/
example {n : ℕ} (g : Fin 6 → Fin n → ℚ) (j : Fin 6) (P : (SMνSpecies n).Charges → Prop)
    (h : P (g j)) : P ((toSpecies j) (toSpeciesEquiv.symm g)) := by
  rw [toSMSpecies_toSpecies_inv]
  exact h

example {n : ℕ} (g : Fin 6 → Fin n → ℚ) (i : Fin (SMνSpecies n).numberCharges) (P : ℚ → Prop)
    (h : P (g 0 i)) : P (Q (toSpeciesEquiv.symm g) i) := by
  simp only [toSMSpecies_toSpecies_inv]
  exact h

/-! ## Cleaning up the numbers (`simp` applies R12–R16 by itself) -/

/-! ### R12. `Matrix.cons_val_…` · goal: entry `k` of a vector literal `![a₀, …, a₅] k` → `aₖ` -/
example {α : Type} (a b c d e f : α) (P : α → Prop) (h : P d) : P (![a, b, c, d, e, f] 3) := by
  simp
  exact h

/-! ### R13. `zero_mul`, `zero_pow`, `Finset.sum_const_zero` · goal: a species with charge 0 drops out -/
example {ι R : Type} [Fintype ι] [CommRing R] (f : ι → R) (P : R → Prop) (h : P 0) :
    P (∑ i, 0 * f i) := by
  simp only [zero_mul, Finset.sum_const_zero]
  exact h

example {ι R : Type} [Fintype ι] [CommRing R] (f : ι → R) (P : R → Prop) (h : P 0) :
    P (∑ i, (0 * f i) ^ 2) := by
  simp
  exact h

/-! ### R14. `neg_mul`, `one_mul` · goal: `-1 * a` → `-a` (inside a sum too) -/
example {ι R : Type} [Fintype ι] [CommRing R] (f : ι → R) (P : R → Prop) (h : P (∑ i, -f i)) :
    P (∑ i, -1 * f i) := by
  simp only [neg_mul, one_mul]
  exact h

/-! ### R15. `Finset.sum_neg_distrib` · `∑ i ∈ s, -f i = -∑ i ∈ s, f i` · goal: pull `-` out of a sum -/
example {ι R : Type} [Fintype ι] [CommRing R] (f : ι → R) (P : R → Prop) (h : P (-∑ i, f i)) :
    P (∑ i, -f i) := by
  rw [Finset.sum_neg_distrib]
  exact h

/-! ### R16. `Even.neg_pow` · `Even k → (-a) ^ k = a ^ k` · goal: squares forget the sign
`even_two : Even 2`; `simp` finds it by itself. -/
example {R : Type} [CommRing R] (a : R) (P : R → Prop) (h : P (a ^ 2)) : P ((-a) ^ 2) := by
  rw [Even.neg_pow even_two]
  exact h

/-! ### R17. `Odd.neg_pow` · `Odd k → (-a) ^ k = -a ^ k` · goal: cubes keep the sign
`simp` does NOT find `Odd 3` by itself: pass `Odd.neg_pow (by decide : Odd 3)`. -/
example {R : Type} [CommRing R] (a : R) (P : R → Prop) (h : P (-a ^ 3)) : P ((-a) ^ 3) := by
  rw [Odd.neg_pow (by decide : Odd 3)]
  exact h

/-! # Part W · Worked combinations on the quark-flavour charge `C y` (R10), not the exercise's -/

/-! ### W1. A linear ACC with no sum hypothesis: R6, R10 → R11, then `simp`, `ring` -/
example {n : ℕ} (y : Fin n → ℚ) : accSU3 (C y) = 0 := by
  rw [accSU3_decomp]
  simp only [C, toSMSpecies_toSpecies_inv]
  simp
  ring

/-! ### W2. A linear ACC that needs `∑ y = 0`: R1 first, then R5, R10 → R11, `simp [hy']` -/
example {n : ℕ} (y : Fin n → ℚ) (hy : ∑ f, y f = 0) : accSU2 (C y) = 0 := by
  have hy' : ∑ f : Fin (SMνSpecies n).numberCharges, y f = 0 := hy
  rw [accSU2_decomp]
  simp only [C, toSMSpecies_toSpecies_inv]
  simp [hy']

/-! ### W3. The cubic ACC: R9, R10 → R11, `simp` with R17 (R12–R15 automatic), then `ring` -/
example {n : ℕ} (y : Fin n → ℚ) : accCube (C y) = 0 := by
  rw [accCube_decomp]
  simp only [C, toSMSpecies_toSpecies_inv]
  simp [Odd.neg_pow (by decide : Odd 3)]
  ring

end M191Guide
