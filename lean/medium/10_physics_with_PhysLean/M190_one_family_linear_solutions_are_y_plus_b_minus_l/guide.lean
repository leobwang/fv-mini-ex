/- Guide for M190 (One family: linear solutions are Y plus B−L).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (one ACC at a time, a 3-vector).
Assumed: Lean basics.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace M190Guide

/-! # Part R · Reference entries -/

/-! ## From a linear solution to four equations -/

/-! ### R1. `have h := PlusU1.gravSol S` (and `SU2Sol`, `SU3Sol`, `YYsol`) · context gains the ACC
`S : (PlusU1 n).LinSols` is a charge vector `S.val` bundled with proofs of the four linear ACCs;
these four lemmas take those proofs out, one equation each. -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (G : Prop)
    (g : accGrav S.val = 0 → accSU2 S.val = 0 → accSU3 S.val = 0 → accYY S.val = 0 → G) : G := by
  have hG := PlusU1.gravSol S
  have h2 := PlusU1.SU2Sol S
  have h3 := PlusU1.SU3Sol S
  have hY := PlusU1.YYsol S
  exact g hG h2 h3 hY

/-! ### R2. `rw [accGrav_decomp] at h` · context: `h` rewritten into sums over families
`Q S i` is the charge of species `Q` in family `i`; likewise `U D L E N`. -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (h : accGrav S.val = 0) :
    6 * ∑ i, Q S.val i + 3 * ∑ i, U S.val i + 3 * ∑ i, D S.val i + 2 * ∑ i, L S.val i
      + ∑ i, E S.val i + ∑ i, N S.val i = 0 := by
  rw [accGrav_decomp] at h
  exact h

/-! ### R3. `rw [accSU2_decomp] at h` · context -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (h : accSU2 S.val = 0) :
    3 * ∑ i, Q S.val i + ∑ i, L S.val i = 0 := by
  rw [accSU2_decomp] at h
  exact h

/-! ### R4. `rw [accSU3_decomp] at h` · context -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (h : accSU3 S.val = 0) :
    2 * ∑ i, Q S.val i + ∑ i, U S.val i + ∑ i, D S.val i = 0 := by
  rw [accSU3_decomp] at h
  exact h

/-! ### R5. `rw [accYY_decomp] at h` · context -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (h : accYY S.val = 0) :
    ∑ i, Q S.val i + 8 * ∑ i, U S.val i + 2 * ∑ i, D S.val i + 3 * ∑ i, L S.val i
      + 6 * ∑ i, E S.val i = 0 := by
  rw [accYY_decomp] at h
  exact h

/-! ## One family: sums and species disappear -/

/-! ### R6. `sum_one` · goal: a sum over the one family `Fin 1` → its single term `f ⟨0, _⟩` -/
example {M : Type} [AddCommMonoid M] (f : Fin (SMνSpecies 1).numberCharges → M) (P : M → Prop)
    (h : P (f ⟨0, by simp⟩)) : P (∑ i, f i) := by
  rw [sum_one]
  exact h

/-! ### R7. `toSpecies_one` · goal: species `j` of family 0 → entry `j` of the 6-vector
`D` is `toSpecies 2`, so `D S ⟨0, _⟩` becomes `S 2`. -/
example (S : (SMνCharges 1).Charges) (j : Fin 6) (P : ℚ → Prop) (h : P (S j)) :
    P ((toSpecies j) S ⟨0, Nat.zero_lt_succ 0⟩) := by
  rw [toSpecies_one]
  exact h

example (S : (SMνCharges 1).Charges) (P : ℚ → Prop) (h : P (S (2 : Fin 6))) :
    P (D S ⟨0, Nat.zero_lt_succ 0⟩) := by
  simp only [toSpecies_one]
  exact h

/-! ### R8. `simp only [sum_one, toSpecies_one] at h₁ h₂` · context: several hypotheses at once -/
example (S : (SMνCharges 1).Charges) (h₁ : 3 * ∑ i, Q S i + ∑ i, L S i = 0)
    (h₂ : ∑ i, N S i = 0) : 3 * S (0 : Fin 6) + S (3 : Fin 6) = 0 ∧ S (5 : Fin 6) = 0 := by
  simp only [sum_one, toSpecies_one] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-! ### R9. `linarith` · closes a linear (in)equality that follows from linear hypotheses
It treats each `S (k : Fin 6)` as an unknown and adds up hypotheses with rational coefficients. -/
example (x y z : ℚ) (h₁ : x + y + z = 0) (h₂ : 2 * x + y = 0) (h₃ : x - z = 3) : y = -2 := by
  linarith

/-! ## Quadratic and cubic ACCs -/

/-! ### R10. `rw [accQuad_decomp]` · goal: `accQuad S` → sums of squares (no `N` term) -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2
      + ∑ i, E S i ^ 2 = 0) : accQuad S = 0 := by
  rw [accQuad_decomp]
  exact h

/-! ### R11. `rw [accCube_decomp]` · goal: `accCube S` → weighted sums of cubes -/
example {n : ℕ} (S : (SMνCharges n).Charges)
    (h : 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3
      + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3 = 0) : accCube S = 0 := by
  rw [accCube_decomp]
  exact h

/-! ## A vector equation, entry by entry -/

/-! ### R12. `funext j` · goal `S = T` between charge vectors → one entry `S j = T j`
A charge vector is a function `Fin _ → ℚ`, so function extensionality applies. -/
example (S T : (SMνCharges 1).Charges) (h : ∀ j, S j = T j) : S = T := by
  funext j
  exact h j

/-! ### R13. `match j with | ⟨0, _⟩ => … | ⟨2, _⟩ => …` · goal list: one goal per index
Each branch sees the index as `⟨k, isLt✝⟩` (value `k`, proof `isLt✝ : k < 3`). -/
example (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (j : Fin 3) : P j := by
  match j with
    | ⟨0, _⟩ => exact h0
    | ⟨1, _⟩ => exact h1
    | ⟨2, _⟩ => exact h2

-- The same split written with `refine`, so all three branch goals are visible at once.
example (P : Fin 3 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) (j : Fin 3) : P j := by
  refine match j with
    | ⟨0, _⟩ => ?_
    | ⟨1, _⟩ => ?_
    | ⟨2, _⟩ => ?_
  exacts [h0, h1, h2]

/-! ### R14. `change G'` · goal `G` → `G'` when the two are equal by unfolding definitions
`(a • v + b • w) k` unfolds to `a * v k + b * w k`; a `match`-defined vector unfolds to its entry. -/
def V : Fin 3 → ℚ := fun i =>
  match i with
  | (0 : Fin 3) => 2
  | (1 : Fin 3) => -5
  | (2 : Fin 3) => 7

example (a b : ℚ) (w : Fin 3 → ℚ) (hk : 1 < 3) (P : ℚ → Prop) (h : P (a * -5 + b * w 1)) :
    P ((a • V + b • w) ⟨1, hk⟩) := by
  change P (a * -5 + b * w 1)
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One linear ACC on a bare charge vector: R4, R8, then R9 -/
example (S : (SMνCharges 1).Charges) (h : accSU3 S = 0) :
    S (2 : Fin 6) = -2 * S (0 : Fin 6) - S (1 : Fin 6) := by
  rw [accSU3_decomp] at h
  simp only [sum_one, toSpecies_one] at h
  linarith

/-! ### W2. Quadratic ACC after a substitution: R10, R8 (on the goal), `rw [hU]`, `ring` -/
example (S : (SMνCharges 1).Charges) (hU : S (1 : Fin 6) = 2 * S (0 : Fin 6)) :
    accQuad S = -7 * S (0 : Fin 6) ^ 2 + S (2 : Fin 6) ^ 2 - S (3 : Fin 6) ^ 2
      + S (4 : Fin 6) ^ 2 := by
  rw [accQuad_decomp]
  simp only [sum_one, toSpecies_one]
  rw [hU]
  ring

/-! ### W3. A 3-vector as a combination: R12, R13, then R14 and R9 in each branch -/
def W : Fin 3 → ℚ := fun i =>
  match i with
  | (0 : Fin 3) => 0
  | (1 : Fin 3) => 1
  | (2 : Fin 3) => 1

def Ones : Fin 3 → ℚ := fun _ => 1

example (x : Fin 3 → ℚ) (h : x 2 = x 1) : x = x 0 • Ones + (x 1 - x 0) • W := by
  funext j
  match j with
    | ⟨0, _⟩ =>
      change x 0 = x 0 * 1 + (x 1 - x 0) * 0
      ring
    | ⟨1, _⟩ =>
      change x 1 = x 0 * 1 + (x 1 - x 0) * 1
      ring
    | ⟨2, _⟩ =>
      change x 2 = x 0 * 1 + (x 1 - x 0) * 1
      linarith

end M190Guide
