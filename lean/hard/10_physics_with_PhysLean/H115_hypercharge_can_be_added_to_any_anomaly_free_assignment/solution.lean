/- H115 | Hypercharge can be added to any anomaly-free assignment | 60-90 min | ACCSystem, Sols, bilinear and trilinear forms, sums over families, change, physlib
GOAL
  `n` SM families plus right-handed neutrinos: rational U(1) charges for 6 species × `n` families. If `S` solves
  every anomaly cancellation condition (ACC: linear `accGrav`, `accSU2`, `accSU3`, `accYY`; quadratic `accQuad`;
  cubic `accCube`), so does `a • S + b • Y` for all `a b : ℚ`, where `Y = PlusU1.Y n` is hypercharge in every family.
BANNED: PlusU1.Y.on_quadBiLin, PlusU1.Y.on_quadBiLin_AFL, PlusU1.Y.add_AFL_quad, PlusU1.Y.add_quad, PlusU1.Y.addQuad, PlusU1.Y.addQuad_zero, PlusU1.Y.on_cubeTriLin, PlusU1.Y.on_cubeTriLin_AFL, PlusU1.Y.on_cubeTriLin', PlusU1.Y.on_cubeTriLin'_ALQ, PlusU1.Y.add_AFL_cube, PlusU1.Y.add_AFQ_cube, PlusU1.Y.add_AF_cube, PlusU1.Y.addCube, SMRHN.familyUniversal_quadBiLin, SMRHN.familyUniversal_cubeTriLin, SMRHN.familyUniversal_cubeTriLin', exact?, apply?, rw?, try?, hint, observe

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace H115

-- MILESTONE (optional: change or delete)
/- SKELETON · quadBiLin_Y
  1. Both sides species by species, and Y as a family-universal charge:      R1, R2, R3
  2. Pull Y's per-family constant out of each of the five sums:              R5 with R4
  3. Family-0 entries of the one-family charge, then Y₁'s numbers:           R6, R7
  4. Close (each `∑` is an unknown):                                         R8
-/
/-- Pairing with hypercharge in the quadratic form gives the `accYY` (hypercharge²–charge) anomaly. -/
theorem quadBiLin_Y {n : ℕ} (S : (SMνCharges n).Charges) :
    quadBiLin (PlusU1.Y n).val S = accYY S := by
  rw [quadBiLin_decomp, accYY_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_two]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁]
  ring

-- MILESTONE (optional: change or delete)
/- SKELETON · cubeTriLin_Y_Y
  1. Both sides species by species, Y as a universal charge:                 R9, R2, R3
  2. Constant out of the three-factor sums, then out of the
     two-factor sums that leaves (in this order):                            R5 with R10, R5 with R4
  3. Family-0 entries, Y₁'s numbers:                                         R6, R7
  4. Close:                                                                  R8
-/
theorem cubeTriLin_Y_Y {n : ℕ} (S : (SMνCharges n).Charges) :
    cubeTriLin (PlusU1.Y n).val (PlusU1.Y n).val S = 6 * accYY S := by
  rw [cubeTriLin_decomp, accYY_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_three]
  repeat rw [sum_familyUniversal_two]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁]
  ring

-- MILESTONE (optional: change or delete)
/- SKELETON · cubeTriLin_Y_S_S
  1. Both sides species by species, Y as a universal charge:                 R9, R11, R3
  2. Constant out of each three-factor sum:                                  R5 with R10
  3. Family-0 entries:                                                       R6
  4. Y₁'s numbers and `^ 2` → `*` in ONE simp (`∑` hides the squares from ring): R7 with R12
  5. Close:                                                                  R8
-/
theorem cubeTriLin_Y_S_S {n : ℕ} (S : (SMνCharges n).Charges) :
    cubeTriLin (PlusU1.Y n).val S S = 6 * accQuad S := by
  rw [cubeTriLin_decomp, accQuad_decomp, PlusU1.Y_val]
  repeat rw [sum_familyUniversal_three]
  simp only [toSpecies_one]
  simp [PlusU1.Y₁, sq]
  ring

-- MILESTONE (optional: change or delete)
/- SKELETON · accQuad_shift
  1. accQuad → its definition, so the expansion lemma matches:               R13
  2. Expand q (a • S + b • Y):                                               R14
  3. Back to `accQuad` names, so hQ and hQY match:                           R13
  4. Scalars out: q twice, then both slots of B:                             R15, R15, R16, R17
  5. B S Y → B Y S, so hYS matches; then rw [hYS, hQ, hQY]:                  R18
  6. Close:                                                                  R8
-/
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
/- SKELETON · accCube_shift
  1. accCube → cubeTriLin.toCubic, expand, back to `accCube` names:          R13, R19, R13
  2. Scalars out of the two cubes:                                           R20, R20
  3. Scalars out of every slot of the two τ terms:                           R21
  4. τ S S Y → τ Y S S, so hYSS matches; then rw [hYYS, hYSS, hC, hCY]:      R22
  5. Close:                                                                  R8
-/
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

/- SKELETON · add_hypercharge_isSolution
  Prove the milestones first: quadBiLin_Y (step 3), cubeTriLin_Y_Y and cubeTriLin_Y_S_S (step 4),
  accQuad_shift (step 3), accCube_shift (step 4). They are stated over `(SMνCharges n).Charges`
  and applied here with `exact` (Traps: `(PlusU1 n).Charges` is a synonym `rw` does not see through).
  1. hYY : accYY S.val = 0, from the linear solution inside S:               R23, R24
  2. Witness: the LinSols combination a • S.1.1 + b • (PlusU1.Y n).1.1, made a
     Sols by linearToAF; its `.val` is the target by rfl. Two goals remain:   R25, R26, R27
       accQuad (…).val = 0        accCube (…).val = 0
  3. Quadratic goal: exact accQuad_shift with S.val, (PlusU1.Y n).val, a, b and
       quadBiLin Y S = 0       from quadBiLin_Y, hYY                         rw [quadBiLin_Y, hYY]
       accQuad S = 0, accQuad Y = 0   (on S.1 and (PlusU1.Y n).1)            R28
  4. Cubic goal: exact accCube_shift with
       τ Y Y S = 0             from cubeTriLin_Y_Y, hYY                      R30
       τ Y S S = 0             from cubeTriLin_Y_S_S, R28                    R30
       accCube S = 0, accCube Y = 0   (on S and PlusU1.Y n)                  R29
-/
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
H1. The linear ACCs are linear, so a `LinSols` combination `a • S.1.1 + b • (PlusU1.Y n).1.1` already satisfies
    them; `PlusU1.linearToAF` (R26) leaves only `accQuad` and `accCube` of `a • S + b • Y`. Expanded (R14, R19),
    those are the ACCs of `S` and `Y` plus the cross terms `B Y S`, `τ Y Y S`, `τ Y S S` (B = quadBiLin, τ = cubeTriLin).
H2. `Y` is the same in every family, so each cross term is an ACC of `S`: `quadBiLin Y S = accYY S`,
    `τ Y Y S = 6 * accYY S`, `τ Y S S = 6 * accQuad S` (milestones 1–3: decompose (R1, R9), pull the constant out
    with `repeat rw` (R4, R5, R10), evaluate `Y₁` (R6, R7), `ring`). `accYY S = 0` by `PlusU1.YYsol` (R24).
    Milestones 4–5 are pure form algebra: `change` (R13) so the expansion lemma matches, then scalars out (R15–R21)
    and swaps (R18, R22) until the hypotheses match.
H3. Milestone 1: `rw [quadBiLin_decomp, accYY_decomp, PlusU1.Y_val]; repeat rw [sum_familyUniversal_two]`, then
    `simp only [toSpecies_one]; simp [PlusU1.Y₁]; ring`. Milestone 4: `change quadBiLin.toHomogeneousQuad (a • S + b • Y) = 0`,
    `rw [BiLinearSymm.toHomogeneousQuad_add]`, `change accQuad (a • S) + accQuad (b • Y) + 2 * quadBiLin (a • S) (b • Y) = 0`.
    Main: `refine ⟨PlusU1.linearToAF (a • S.1.1 + b • (PlusU1.Y n).1.1) ?_ ?_, rfl⟩`.
-/
