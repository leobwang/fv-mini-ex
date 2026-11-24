/- Guide for E126 (Hypercharge cancels the linear anomalies).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: a worked combination on a charge vector that is NOT the exercise's (B − L).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMνCharges SMνACCs

namespace E126Guide

/-! # Part R · Reference entries -/

/-! ## Splitting the goal -/

/-! ### R1. `refine ⟨?_, ?_, ?_⟩` · goal list: one goal `A ∧ B ∧ C` → three goals -/
example (A B C : Prop) (ha : A) (hb : B) (hc : C) : A ∧ B ∧ C := by
  refine ⟨?_, ?_, ?_⟩
  exacts [ha, hb, hc]

/-! ## Anomaly → sums over species and families (one lemma per anomaly) -/

/-! ### R2. `accGrav_decomp` · goal: `accGrav S` → weighted sum of the six species' charge sums
`S : (SMνCharges n).Charges` is a charge assignment for `n` families; `Q S i` is the charge of the
quark doublet `Q` in family `i` (likewise `U D L E N`). -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i +
      ∑ i, N S i)) : P (accGrav S) := by
  rw [accGrav_decomp]
  exact h

/-! ### R3. `accSU2_decomp` · goal: `accSU2 S` → `3 * ∑ Q + ∑ L` (only the SU(2) doublets) -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (3 * ∑ i, Q S i + ∑ i, L S i)) : P (accSU2 S) := by
  rw [accSU2_decomp]
  exact h

/-! ### R4. `accSU3_decomp` · goal: `accSU3 S` → `2 * ∑ Q + ∑ U + ∑ D` (only the colour triplets) -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i)) : P (accSU3 S) := by
  rw [accSU3_decomp]
  exact h

/-! ## One family: sums collapse, species projections become entries -/

/-! ### R5. `sum_one` · goal: a sum over the single family `Fin (SMνSpecies 1).numberCharges` → its one term
The index type has exactly one element, `⟨0, _⟩`. `simp only` rewrites every such sum in the goal. -/
example {M : Type} [AddCommMonoid M] (f : Fin (SMνSpecies 1).numberCharges → M)
    (hi : 0 < (SMνSpecies 1).numberCharges) (P : M → Prop) (h : P (f ⟨0, hi⟩)) :
    P (∑ i, f i) := by
  simp only [sum_one]
  exact h

/-! ### R6. `toSpecies_one` · `toSpecies j S ⟨0, _⟩ = S j` · goal: species `j`, family 0 → entry `j` of `S`
`Q U D L E N` are `toSpecies 0` … `toSpecies 5`, so `simp only [toSpecies_one]` rewrites all of them.
You cannot type `S 0` yourself (no numeral `0` in `Fin (SMνCharges 1).numberCharges`); `S (0 : Fin 6)` works. -/
example (S : (SMνCharges 1).Charges) (hi : 0 < (SMνSpecies 1).numberCharges) (P : ℚ → Prop)
    (h : P (S (0 : Fin 6) + S (1 : Fin 6))) : P (Q S ⟨0, hi⟩ + U S ⟨0, hi⟩) := by
  simp only [toSpecies_one]
  exact h

/-! ## Numbers -/

/-! ### R7. `simp [V]` · goal: unfold the vector `V := ![…]` and read off its entries
`simp` also tidies `x * 1`, `x * 0`, `x + 0` and `a * -b` (→ `-(a * b)`), but does no `ℚ` arithmetic. -/
def V : (SMνCharges 1).Charges := ![2, -5, 0, 0, 0, 1]

example (P : ℚ → Prop) (h : P (2 + -(3 * 5))) :
    P (V (0 : Fin 6) + 3 * V (1 : Fin 6) + 4 * V (2 : Fin 6)) := by
  simp [V]
  exact h

/-! ### R8. `norm_num` · closes an equation between rational numerals -/
example : (2 : ℚ) + -(3 * 4) + 5 * 2 = 0 := by norm_num

/-! # Part W · Worked combination (not the exercise's charges) -/

/-! ### W1. B − L (baryon minus lepton number, ×3) cancels the SU(3) anomaly: R4 → R5 → R6 → R7 → R8 -/
def BL : (SMνCharges 1).Charges := ![1, -1, -1, -3, 3, 3]

example : accSU3 BL = 0 := by
  rw [accSU3_decomp]
  simp only [sum_one]
  simp only [toSpecies_one]
  simp [BL]
  norm_num

end E126Guide
