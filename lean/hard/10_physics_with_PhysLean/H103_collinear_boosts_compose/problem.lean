/- H103 | Collinear boosts compose (velocity addition) | 45-75 min | LorentzGroup, boost, mulVec, ext, field identities, physlib
GOAL
  Two boosts along the same spatial axis `i` compose to one boost along `i` with the relativistic
  sum of speeds `(β₁ + β₂) / (1 + β₁β₂)`; part of the claim is that this speed is again `< 1`.

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup Matrix

namespace H103

/- SKELETON · abs_add_lt   (milestone; prove it FIRST: boost_mul_boost uses it as the ∃ witness)
  1. Turn every `|·| < 1`, in the hypotheses and the goal, into two inequalities:        R1
  2. Prove the denominator positive, `hpos : 0 < 1 + β₁ * β₂`, from h₁ h₂:              have, R2
  3. Split `-1 < β₃ ∧ β₃ < 1`:                                                          constructor
  4. Left:  clear the denominator with hpos, then the polynomial inequality:            R3, R2
     Right: the same on the other side:                                                 R4, R2
-/
-- MILESTONE (optional: change or delete)
theorem abs_add_lt {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    |(β₁ + β₂) / (1 + β₁ * β₂)| < 1 := by
  sorry

/- SKELETON · gamma_add   (milestone; prove it SECOND: boost_mul_boost rewrites with it in step 4)
  1. Positivity facts, each by `rw [abs_lt] at …` and then R2:                          R1, R2
       hpos : 0 < 1 + β₁ * β₂     a1 : 0 < 1 - β₁ ^ 2     a2 : 0 < 1 - β₂ ^ 2
  2. The key identity, by clearing denominators and then `ring`:                        R6, ring
       key : 1 - ((β₁ + β₂) / (1 + β₁ * β₂)) ^ 2 = (1 - β₁ ^ 2) * (1 - β₂ ^ 2) / (1 + β₁ * β₂) ^ 2
  3. Open the three `γ`s:                                                               R5
  4. rw [key], then split the square root: quotient (side goal by R8), square of the
     positive denominator (hpos.le), product (a1.le):                                   R7, R8, R9, R11, R10
  5. Clear the remaining fractions:                                                     R6
-/
-- MILESTONE (optional: change or delete)
theorem gamma_add {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    γ ((β₁ + β₂) / (1 + β₁ * β₂)) = γ β₁ * γ β₂ * (1 + β₁ * β₂) := by
  sorry

/- SKELETON · mul_smul_apply   (milestone; boost_mul_boost uses it in step 4 to split the product)
  1. Acting by a product is acting twice: one instance of the action law.               R12
-/
-- MILESTONE (optional: change or delete)
theorem mul_smul_apply {d : ℕ} (i : Fin d) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1)
    (p : Lorentz.Vector d) :
    (boost i β₁ h₁ * boost i β₂ h₂) • p = boost i β₁ h₁ • (boost i β₂ h₂ • p) := by
  sorry

/- SKELETON · boost_mul_boost
  0. Prove the milestones first: abs_add_lt (step 1), gamma_add and mul_smul_apply (step 4).
  1. Give the speed bound as the witness of the ∃, using abs_add_lt:                    R13
  2. Equal Lorentz transformations ← equal on every vector; introduce the vector x:     R14, intro x
  3. Facts for later:
       hpos : 0 < 1 + β₁ * β₂                                                           R1, R2
       h3 : (β₁ + β₂) / (1 + β₁ * β₂) * (1 + β₁ * β₂) = β₁ + β₂                         R15, R11
  4. Into coordinates, in this order:
       both matrix-vector products back to actions                                      R16, R16
       the product acts as two boosts                                                   rw [mul_smul_apply] (R12)
       the three boosts in coordinates                                                  R17, R17, R17
       merge the γ factors                                                              rw [gamma_add h₁ h₂]
  5. Compare coordinate by coordinate, time or space:                                   R18, R19
  6. Time row `Sum.inl 0`: evaluate, then close with a multiple of h3:                  R20, R21
  7. Space row `Sum.inr j`: split on `j = i`:                                           R22
       j = i:  R23, R20, R21 with a multiple of h3
       j ≠ i:  R24
-/
-- BEGIN SPEC
theorem boost_mul_boost {d : ℕ} (i : Fin d) {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    ∃ h : |(β₁ + β₂) / (1 + β₁ * β₂)| < 1,
      boost i β₁ h₁ * boost i β₂ h₂ = boost i ((β₁ + β₂) / (1 + β₁ * β₂)) h :=
-- END SPEC
  sorry

end H103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two Lorentz transformations are equal if they act the same on every vector (R14), and a boost acting
    on a vector has an explicit coordinate formula (R17). The `∃` asks for a proof: start with
    `refine ⟨abs_add_lt h₁ h₂, ?_⟩`. All the analysis sits in the two scalar milestones.
H2. `abs_add_lt`: `rw [abs_lt] at *`, `hpos : 0 < 1 + β₁ * β₂` by `nlinarith`, then `constructor` and
    `lt_div_iff₀ hpos` / `div_lt_iff₀ hpos` with `nlinarith`. `gamma_add`: the key is
    `1 - β₃ ^ 2 = (1 - β₁ ^ 2) * (1 - β₂ ^ 2) / (1 + β₁ * β₂) ^ 2` (`field_simp; ring`); then `unfold γ`,
    `rw [key]`, split the root with `Real.sqrt_div'`, `Real.sqrt_sq`, `Real.sqrt_mul`, and `field_simp`.
    Main theorem: compare the time row, the boosted row `i`, and the other rows.
H3. `apply eq_of_mulVec_eq; intro x`, `have h3 : (β₁ + β₂) / (1 + β₁ * β₂) * (1 + β₁ * β₂) = β₁ + β₂ :=
    div_mul_cancel₀ _ hpos.ne'`, then `rw [← Lorentz.Vector.smul_eq_mulVec, ← Lorentz.Vector.smul_eq_mulVec,
    mul_smul_apply, boost_toCoord_eq, boost_toCoord_eq, boost_toCoord_eq, gamma_add h₁ h₂]`, `funext j`,
    `match j with`. Time row: `simp only [if_true]; linear_combination (γ β₁ * γ β₂ * x (Sum.inr i)) * h3`.
    Row `Sum.inr j`: `by_cases hj : j = i`; if so `subst hj; simp only [if_true]` and
    `linear_combination (γ β₁ * γ β₂ * x (Sum.inl 0)) * h3`; otherwise `simp [hj]`.
-/
