/- H115 | Hypercharge can be added to any anomaly-free assignment | 60-90 min | ACCSystem, Sols, bilinear and trilinear forms, sums over families, change, physlib
GOAL
  `n` SM families plus right-handed neutrinos: 6 species × `n` families of rational U(1) charges. If `S` solves
  every anomaly cancellation condition (ACC: linear `accGrav`, `accSU2`, `accSU3`, `accYY` (hypercharge²–charge);
  quadratic `accQuad`; cubic `accCube`), so does `a • S + b • Y` for all `a b : ℚ`, where `Y = PlusU1.Y n` is
  hypercharge copied to every family (`•` = scalar multiple).

REFERENCE
  `S : (PlusU1 n).Sols` bundles charges `S.val` with ACC proofs; `IsSolution χ T := ∃ sol : χ.Sols, sol.val = T`.
  -- B = `quadBiLin` (symmetric bilinear form behind `accQuad`), τ = `cubeTriLin` (symmetric trilinear form behind
  -- `accCube`); q / c / f = any quadratic / cubic / homogeneous form; Q = `toSpecies 0` (the Q-quark charges).
  #check PlusU1.linearToAF  -- (S : LinSols) → accQuad S.val = 0 → accCube S.val = 0 → Sols (`S.1.1 : LinSols`)
  #check PlusU1.YYsol       -- accYY S.val = 0 for `S : LinSols`  (`PlusU1.quadSol`: accQuad, QuadSols; `PlusU1.cubeSol`: accCube, Sols)
  #check BiLinearSymm.toHomogeneousQuad_add  -- q (S + T) = q S + q T + 2 * B S T;  `accQuad` := `quadBiLin.toHomogeneousQuad`
  #check TriLinearSymm.toCubic_add  -- c (S + T) = c S + c T + 3 * τ S S T + 3 * τ T T S;  `accCube` := `cubeTriLin.toCubic`
  #check HomogeneousQuadratic.map_smul  -- f (a • S) = a ^ 2 * f S   (`HomogeneousCubic.map_smul`: a ^ 3)
  #check BiLinearSymm.map_smul₁   -- B (a • S) T = a * B S T  (also `map_smul₂`, `swap`; `TriLinearSymm.map_smul₁/₂/₃`, `swap₃`)
  #check cubeTriLin_decomp  -- τ S T R = 6 * ∑ i, Q S i * Q T i * Q R i + ...  (`quadBiLin_decomp`, `accYY_decomp`, `accQuad_decomp`)
  #check PlusU1.Y_val       -- (Y n).val = familyUniversal n Y₁.val,  Y₁ = (1, -4, 2, -3, 6, 0) for (Q, U, D, L, E, N)
  #check sum_familyUniversal_two  -- ∑ i, toSpecies j (familyUniversal n S) i * toSpecies j T i = toSpecies j S ⟨0, _⟩ * ∑ ...
  #check toSpecies_one      -- toSpecies j S ⟨0, _⟩ = S j   (`Q = toSpecies 0`, ...;  `sum_familyUniversal_three` for triples)
  `change accQuad (a • S) + accQuad (b • Y) + 2 * quadBiLin (a • S) (b • Y) = 0` restates a goal up to unfolding.
BANNED: PlusU1.Y.on_quadBiLin, PlusU1.Y.on_quadBiLin_AFL, PlusU1.Y.add_AFL_quad, PlusU1.Y.add_quad, PlusU1.Y.addQuad, PlusU1.Y.addQuad_zero, PlusU1.Y.on_cubeTriLin, PlusU1.Y.on_cubeTriLin_AFL, PlusU1.Y.on_cubeTriLin', PlusU1.Y.on_cubeTriLin'_ALQ, PlusU1.Y.add_AFL_cube, PlusU1.Y.add_AFQ_cube, PlusU1.Y.add_AF_cube, PlusU1.Y.addCube, SMRHN.familyUniversal_quadBiLin, SMRHN.familyUniversal_cubeTriLin, SMRHN.familyUniversal_cubeTriLin', exact?, apply?, rw?, try?, hint, observe
NOTE: `(PlusU1 n).Charges` is a synonym of `(SMνCharges n).Charges` that `rw` and `+` do not see through: state helpers over `(SMνCharges n).Charges`.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace H115

-- MILESTONE (optional: change or delete)
/-- Pairing with hypercharge in the quadratic form gives the `accYY` (hypercharge²–charge) anomaly. -/
theorem quadBiLin_Y {n : ℕ} (S : (SMνCharges n).Charges) :
    quadBiLin (PlusU1.Y n).val S = accYY S := by
  rw [quadBiLin_decomp, accYY_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_two]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁]
  ring

-- MILESTONE (optional: change or delete)
theorem cubeTriLin_Y_Y {n : ℕ} (S : (SMνCharges n).Charges) :
    cubeTriLin (PlusU1.Y n).val (PlusU1.Y n).val S = 6 * accYY S := by
  rw [cubeTriLin_decomp, accYY_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_three]
  repeat rw [sum_familyUniversal_two]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁]
  ring

-- MILESTONE (optional: change or delete)
theorem cubeTriLin_Y_S_S {n : ℕ} (S : (SMνCharges n).Charges) :
    cubeTriLin (PlusU1.Y n).val S S = 6 * accQuad S := by
  rw [cubeTriLin_decomp, accQuad_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_three]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁, sq]
  ring

-- MILESTONE (optional: change or delete)
/-- Algebra only: the quadratic ACC of `a • S + b • Y` from the ACCs of `S`, `Y` and their cross term. -/
theorem accQuad_shift {n : ℕ} (S Y : (SMνCharges n).Charges) (a b : ℚ)
    (hYS : quadBiLin Y S = 0) (hQ : accQuad S = 0) (hQY : accQuad Y = 0) :
    accQuad (a • S + b • Y) = 0 := by
  change quadBiLin.toHomogeneousQuad (a • S + b • Y) = 0
  rw [BiLinearSymm.toHomogeneousQuad_add]
  change accQuad (a • S) + accQuad (b • Y) + 2 * quadBiLin (a • S) (b • Y) = 0
  rw [HomogeneousQuadratic.map_smul, HomogeneousQuadratic.map_smul, BiLinearSymm.map_smul₁,
    BiLinearSymm.map_smul₂, BiLinearSymm.swap, hYS, hQ, hQY]
  ring

-- MILESTONE (optional: change or delete)
theorem accCube_shift {n : ℕ} (S Y : (SMνCharges n).Charges) (a b : ℚ)
    (hYYS : cubeTriLin Y Y S = 0) (hYSS : cubeTriLin Y S S = 0) (hC : accCube S = 0)
    (hCY : accCube Y = 0) : accCube (a • S + b • Y) = 0 := by
  change cubeTriLin.toCubic (a • S + b • Y) = 0
  rw [TriLinearSymm.toCubic_add]
  change accCube (a • S) + accCube (b • Y) + 3 * cubeTriLin (a • S) (a • S) (b • Y)
    + 3 * cubeTriLin (b • Y) (b • Y) (a • S) = 0
  rw [HomogeneousCubic.map_smul, HomogeneousCubic.map_smul]
  simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]
  -- WHY: `τ S S Y` must be turned into `τ Y S S` before the milestone hypothesis applies.
  rw [TriLinearSymm.swap₃ cubeTriLin S S, hYYS, hYSS, hC, hCY]
  ring

-- BEGIN SPEC
theorem add_hypercharge_isSolution {n : ℕ} (S : (PlusU1 n).Sols) (a b : ℚ) :
    (PlusU1 n).IsSolution (a • S.val + b • (PlusU1.Y n).val) :=
-- END SPEC
  by
    have hYY : accYY S.val = 0 := PlusU1.YYsol S.1.1
    refine ⟨PlusU1.linearToAF (a • S.1.1 + b • (PlusU1.Y n).1.1) ?_ ?_, rfl⟩
    · exact accQuad_shift S.val (PlusU1.Y n).val a b (by rw [quadBiLin_Y, hYY])
        (PlusU1.quadSol S.1) (PlusU1.quadSol (PlusU1.Y n).1)
    · exact accCube_shift S.val (PlusU1.Y n).val a b (by rw [cubeTriLin_Y_Y, hYY, mul_zero])
        (by rw [cubeTriLin_Y_S_S, PlusU1.quadSol S.1, mul_zero])
        (PlusU1.cubeSol S) (PlusU1.cubeSol (PlusU1.Y n))

end H115

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The linear ACCs are linear, so `PlusU1.linearToAF` reduces the goal to `accQuad` and `accCube` of
    `a • S + b • Y`. Expanding those leaves the ACCs of `S` and `Y` plus the cross terms `B Y S`, `τ Y Y S`, `τ Y S S`.
H2. Because `Y` is the same in every family, each cross term collapses to an ACC of `S`:
    `quadBiLin Y S = accYY S`, `τ Y Y S = 6 * accYY S`, `τ Y S S = 6 * accQuad S` (milestones 1-3). Prove them by
    decomposing over families and pulling the constant factor out with `sum_familyUniversal_two`/`_three`.
H3. Milestone 1: `rw [quadBiLin_decomp, accYY_decomp, PlusU1.Y_val]; repeat rw [sum_familyUniversal_two]`, then
    `simp only [toSpecies_one]; simp [PlusU1.Y₁]; ring`. Milestone 4: `change quadBiLin.toHomogeneousQuad (a • S + b • Y) = 0`,
    `rw [BiLinearSymm.toHomogeneousQuad_add]`, the `change` from the card, then `map_smul` rewrites.
    Main: `refine ⟨PlusU1.linearToAF (a • S.1.1 + b • (PlusU1.Y n).1.1) ?_ ?_, rfl⟩`.
-/
