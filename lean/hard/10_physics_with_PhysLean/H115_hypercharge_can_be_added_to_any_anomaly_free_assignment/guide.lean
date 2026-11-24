/- Guide for H115 (Hypercharge can be added to any anomaly-free assignment).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a B−L-like charge `BL₁`, plain
sums `S + T`, a rescaled solution).
Assumed: Lean basics (E001–E033). No Mathlib or physlib familiarity: cheatsheet.md explains each name.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace H115Guide

/-! # Part R · Reference entries -/

/-! ## Forms written out species by species -/

/-! ### R1. `quadBiLin_decomp` · goal: `quadBiLin S T` → five species sums -/
example {n : ℕ} (S T : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i + ∑ i, D S i * D T i
      - ∑ i, L S i * L T i + ∑ i, E S i * E T i)) :
    P (quadBiLin S T) := by
  rw [quadBiLin_decomp]
  exact h

/-! ### R2. `accYY_decomp` · goal: `accYY S` → weighted species sums -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i)) :
    P (accYY S) := by
  rw [accYY_decomp]
  exact h

/-! ### R3. `PlusU1.Y_val` · goal: `(PlusU1.Y n).val` → `familyUniversal n PlusU1.Y₁.val` -/
example {n : ℕ} (P : (SMνCharges n).Charges → Prop) (h : P (familyUniversal n PlusU1.Y₁.val)) :
    P (PlusU1.Y n).val := by
  rw [PlusU1.Y_val]
  exact h

/-! ## Sums over families of a family-universal charge -/

/-! ### R4. `sum_familyUniversal_two` · goal: `∑ i, X i * T i` with `X` the same in every family →
`X₀ * ∑ i, T i` (one species `j` at a time; here `j = 0`, the `Q` quarks) -/
example {n : ℕ} (S₁ : (SMνCharges 1).Charges) (T : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (toSpecies 0 S₁ ⟨0, Nat.zero_lt_one⟩ * ∑ i, toSpecies 0 T i)) :
    P (∑ i, Q (familyUniversal n S₁) i * Q T i) := by
  rw [sum_familyUniversal_two]
  exact h

/-! ### R5. `repeat rw [l]` · goal: rewrite with `l` again and again until `rw` fails
One `rw [l]` fixes `l`'s arguments at the first match (here `j = 0`), so the `U` sum (`j = 1`) is left. -/
example {n : ℕ} (S₁ : (SMνCharges 1).Charges) (T : (SMνCharges n).Charges) (P : ℚ → ℚ → Prop)
    (h : P (toSpecies 0 S₁ ⟨0, Nat.zero_lt_one⟩ * ∑ i, toSpecies 0 T i)
      (toSpecies 1 S₁ ⟨0, Nat.zero_lt_one⟩ * ∑ i, toSpecies 1 T i)) :
    P (∑ i, Q (familyUniversal n S₁) i * Q T i) (∑ i, U (familyUniversal n S₁) i * U T i) := by
  repeat rw [sum_familyUniversal_two]
  exact h

/-! ### R6. `simp only [toSpecies_one]` · goal: `toSpecies j S₁ ⟨0, _⟩` → `S₁ j` (one family: species `j`
of family 0 is just entry `j`) -/
example (S₁ : (SMνCharges 1).Charges) (P : ℚ → Prop) (h : P (S₁ (3 : Fin 6))) :
    P (toSpecies 3 S₁ ⟨0, Nat.zero_lt_one⟩) := by
  simp only [toSpecies_one]
  exact h

/-! ### R7. `simp [PlusU1.Y₁]` · goal: an entry `PlusU1.Y₁.val j` → its number
`Y₁ = (1, -4, 2, -3, 6, 0)` for `(Q, U, D, L, E, N)`; `simp only [PlusU1.Y₁_val]` does only this step. -/
example (P : ℚ → ℚ → Prop) (h : P (-4) 6) :
    P (PlusU1.Y₁.val (1 : Fin 6)) (PlusU1.Y₁.val (4 : Fin 6)) := by
  simp [PlusU1.Y₁]
  exact h

/-! ### R8. `ring` · closes a commutative-ring identity; a sum `∑ x, f x` is one unknown to it -/
example {n : ℕ} (f g : Fin n → ℚ) :
    2 * (4 * ∑ x, f x) + -∑ x, g x = 8 * ∑ x, f x - ∑ x, g x := by
  ring

/-! ### R9. `cubeTriLin_decomp` · goal: `cubeTriLin S T R` → six weighted species sums -/
example {n : ℕ} (S T R : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (6 * ∑ i, Q S i * Q T i * Q R i + 3 * ∑ i, U S i * U T i * U R i
      + 3 * ∑ i, D S i * D T i * D R i + 2 * ∑ i, L S i * L T i * L R i
      + ∑ i, E S i * E T i * E R i + ∑ i, N S i * N T i * N R i)) :
    P (cubeTriLin S T R) := by
  rw [cubeTriLin_decomp]
  exact h

/-! ### R10. `sum_familyUniversal_three` · goal: `∑ i, X i * T i * R i` with `X` universal →
`X₀ * ∑ i, T i * R i` -/
example {n : ℕ} (S₁ : (SMνCharges 1).Charges) (T R : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (toSpecies 0 S₁ ⟨0, Nat.zero_lt_one⟩ * ∑ i, toSpecies 0 T i * toSpecies 0 R i)) :
    P (∑ i, Q (familyUniversal n S₁) i * Q T i * Q R i) := by
  rw [sum_familyUniversal_three]
  exact h

/-! ### R11. `accQuad_decomp` · goal: `accQuad S` → sums of squares -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → Prop)
    (h : P (∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2
      + ∑ i, E S i ^ 2)) :
    P (accQuad S) := by
  rw [accQuad_decomp]
  exact h

/-! ### R12. `sq` · `a ^ 2 = a * a` · goal: a square → a product -/
example (x : ℚ) (P : ℚ → Prop) (h : P (x * x)) : P (x ^ 2) := by
  rw [sq]
  exact h

/-! ## The ACCs as forms: expanding sums and scalars -/

/-! ### R13. `change G'` · goal: replaced by `G'`, which must be equal to it by unfolding definitions
`accQuad` is defined as `quadBiLin.toHomogeneousQuad`, `accCube` as `cubeTriLin.toCubic`. -/
example {n : ℕ} (S : (SMνCharges n).Charges) (P : ℚ → ℚ → Prop)
    (h : P (quadBiLin.toHomogeneousQuad S) (cubeTriLin.toCubic S)) :
    P (accQuad S) (accCube S) := by
  change P (quadBiLin.toHomogeneousQuad S) (cubeTriLin.toCubic S)
  exact h

/-! ### R14. `BiLinearSymm.toHomogeneousQuad_add` · goal: `q (S + T)` → `q S + q T + 2 * B S T` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (B : BiLinearSymm V) (S T : V) (P : ℚ → Prop)
    (h : P (B.toHomogeneousQuad S + B.toHomogeneousQuad T + 2 * B S T)) :
    P (B.toHomogeneousQuad (S + T)) := by
  rw [BiLinearSymm.toHomogeneousQuad_add]
  exact h

/-! ### R15. `HomogeneousQuadratic.map_smul` · goal: `f (a • S)` → `a ^ 2 * f S` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (f : HomogeneousQuadratic V) (a : ℚ) (S : V)
    (P : ℚ → Prop) (h : P (a ^ 2 * f S)) : P (f (a • S)) := by
  rw [HomogeneousQuadratic.map_smul]
  exact h

/-! ### R16. `BiLinearSymm.map_smul₁` · goal: `B (a • S) T` → `a * B S T` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (B : BiLinearSymm V) (a : ℚ) (S T : V)
    (P : ℚ → Prop) (h : P (a * B S T)) : P (B (a • S) T) := by
  rw [BiLinearSymm.map_smul₁]
  exact h

/-! ### R17. `BiLinearSymm.map_smul₂` · goal: `B S (a • T)` → `a * B S T` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (B : BiLinearSymm V) (a : ℚ) (S T : V)
    (P : ℚ → Prop) (h : P (a * B S T)) : P (B S (a • T)) := by
  rw [BiLinearSymm.map_smul₂]
  exact h

/-! ### R18. `BiLinearSymm.swap` · `B S T = B T S` · goal: the arguments swap -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (B : BiLinearSymm V) (S T : V)
    (P : ℚ → Prop) (h : P (B T S)) : P (B S T) := by
  rw [BiLinearSymm.swap]
  exact h

/-! ### R19. `TriLinearSymm.toCubic_add` · goal: `c (S + T)` → `c S + c T + 3 * τ S S T + 3 * τ T T S` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (τ : TriLinearSymm V) (S T : V) (P : ℚ → Prop)
    (h : P (τ.toCubic S + τ.toCubic T + 3 * τ S S T + 3 * τ T T S)) :
    P (τ.toCubic (S + T)) := by
  rw [TriLinearSymm.toCubic_add]
  exact h

/-! ### R20. `HomogeneousCubic.map_smul` · goal: `f (a • S)` → `a ^ 3 * f S` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (f : HomogeneousCubic V) (a : ℚ) (S : V)
    (P : ℚ → Prop) (h : P (a ^ 3 * f S)) : P (f (a • S)) := by
  rw [HomogeneousCubic.map_smul]
  exact h

/-! ### R21. `simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]` ·
goal: every scalar leaves every slot of `τ` -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (τ : TriLinearSymm V) (a b c : ℚ) (S T R : V)
    (P : ℚ → Prop) (h : P (c * (b * (a * τ S T R)))) : P (τ (a • S) (b • T) (c • R)) := by
  simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]
  exact h

/-! ### R22. `TriLinearSymm.swap₃` · `τ S T R = τ R T S` · goal: first and third slots swap
`rw [TriLinearSymm.swap₃ τ S S]` fixes the first two arguments, so only `τ S S _` moves. -/
example {V : Type} [AddCommMonoid V] [Module ℚ V] (τ : TriLinearSymm V) (S T : V)
    (P : ℚ → Prop) (h : P (τ T S S)) : P (τ S S T) := by
  rw [TriLinearSymm.swap₃ τ S S]
  exact h

/-! ## Solutions of the ACC system -/

/-! ### R23. `S.1`, `S.1.1` · context gains `S.1.1.val = S.val` (printed `S.val = S.val`): forgetting
ACCs (`Sols → QuadSols → LinSols`) keeps the charges `.val`, by definition -/
example {n : ℕ} (S : (PlusU1 n).Sols) (P : (PlusU1 n).Charges → Prop) (h : P S.val) :
    P S.1.1.val := by
  have hL : S.1.1.val = S.val := rfl
  exact h

/-! ### R24. `PlusU1.YYsol` · context gains `accYY S.val = 0` from `S : LinSols` -/
example {n : ℕ} (S : (PlusU1 n).LinSols) (G : Prop) (g : accYY S.val = 0 → G) : G := by
  have hYY : accYY S.val = 0 := PlusU1.YYsol S
  exact g hYY

/-! ### R25. `refine ⟨sol, ?_⟩` on `IsSolution` · goal: `χ.IsSolution T` (`∃ sol, sol.val = T`) →
`sol.val = T` -/
example {n : ℕ} (S : (PlusU1 n).Sols) (T : (PlusU1 n).Charges) (h : S.val = T) :
    (PlusU1 n).IsSolution T := by
  refine ⟨S, ?_⟩
  exact h

/-! ### R26. `PlusU1.linearToAF T ?_ ?_` · goal list: a `Sols` from `T : LinSols`, owing two proofs -/
example {n : ℕ} (T : (PlusU1 n).LinSols) (hQ : accQuad T.val = 0) (hC : accCube T.val = 0) :
    (PlusU1 n).IsSolution T.val := by
  refine ⟨PlusU1.linearToAF T ?_ ?_, rfl⟩
  exact hQ
  exact hC

/-! ### R27. `.val` of a combination of `LinSols` · goal: `(a • S + b • T).val` is
`a • S.val + b • T.val` by definition (`change`, `rfl` and `exact` see through it) -/
example {n : ℕ} (S T : (PlusU1 n).LinSols) (a b : ℚ) (P : (PlusU1 n).Charges → Prop)
    (h : P (a • S.val + b • T.val)) : P (a • S + b • T).val := by
  change P (a • S.val + b • T.val)
  exact h

/-! ### R28. `PlusU1.quadSol` · context gains `accQuad S.val = 0` from `S : QuadSols` -/
example {n : ℕ} (S : (PlusU1 n).QuadSols) (G : Prop) (g : accQuad S.val = 0 → G) : G := by
  have hQ : accQuad S.val = 0 := PlusU1.quadSol S
  exact g hQ

/-! ### R29. `PlusU1.cubeSol` · context gains `accCube S.val = 0` from `S : Sols` -/
example {n : ℕ} (S : (PlusU1 n).Sols) (G : Prop) (g : accCube S.val = 0 → G) : G := by
  have hC : accCube S.val = 0 := PlusU1.cubeSol S
  exact g hC

/-! ### R30. `mul_zero` · `a * 0 = 0` · goal: `a * 0` → `0` -/
example (a : ℚ) (P : ℚ → Prop) (h : P 0) : P (a * 0) := by
  rw [mul_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- A one-family charge with the B−L pattern `(Q, U, D, L, E, N) = (1, -1, -1, -3, 3, 3)`. -/
def BL₁ : (SMνCharges 1).Charges := ![1, -1, -1, -3, 3, 3]

/-! ### W1. Pairing with a family-universal charge: R1, R5 with R4, R6, R7, R8 -/
example {n : ℕ} (S : (SMνCharges n).Charges) :
    quadBiLin (familyUniversal n BL₁) S
      = ∑ i, Q S i + 2 * ∑ i, U S i - ∑ i, D S i + 3 * ∑ i, L S i + 3 * ∑ i, E S i := by
  rw [quadBiLin_decomp]
  repeat rw [sum_familyUniversal_two]
  simp only [toSpecies_one]
  simp [BL₁]
  ring

/-! ### W2. The quadratic ACC of a sum: R13, R14, R13 back, R18, then the hypotheses -/
example {n : ℕ} (S T : (SMνCharges n).Charges) (hS : accQuad S = 0) (hT : accQuad T = 0)
    (hTS : quadBiLin T S = 0) : accQuad (S + T) = 0 := by
  change quadBiLin.toHomogeneousQuad (S + T) = 0
  rw [BiLinearSymm.toHomogeneousQuad_add]
  change accQuad S + accQuad T + 2 * quadBiLin S T = 0
  rw [BiLinearSymm.swap, hS, hT, hTS]
  norm_num

/-! ### W3. Scalars out of a trilinear term, then a swap so a hypothesis fits: R21, R22, R30 -/
example {n : ℕ} (S T : (SMνCharges n).Charges) (a b : ℚ) (h : cubeTriLin T S S = 0) :
    cubeTriLin (a • S) (a • S) (b • T) = 0 := by
  simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]
  rw [TriLinearSymm.swap₃ cubeTriLin S S, h]
  simp only [mul_zero]

/-! ### W4. A rescaled solution is a solution: helpers over `(SMνCharges n).Charges` (R15/R20, R30),
then R26 with R27 (`rfl`), and the helpers applied by `exact` to R28/R29 -/
example {n : ℕ} (S : (PlusU1 n).Sols) (c : ℚ) : (PlusU1 n).IsSolution (c • S.val) := by
  have hq : ∀ T : (SMνCharges n).Charges, accQuad T = 0 → accQuad (c • T) = 0 := by
    intro T hT
    rw [HomogeneousQuadratic.map_smul, hT, mul_zero]
  have hc : ∀ T : (SMνCharges n).Charges, accCube T = 0 → accCube (c • T) = 0 := by
    intro T hT
    rw [HomogeneousCubic.map_smul, hT, mul_zero]
  refine ⟨PlusU1.linearToAF (c • S.1.1) ?_ ?_, rfl⟩
  · exact hq S.val (PlusU1.quadSol S.1)
  · exact hc S.val (PlusU1.cubeSol S)

end H115Guide
