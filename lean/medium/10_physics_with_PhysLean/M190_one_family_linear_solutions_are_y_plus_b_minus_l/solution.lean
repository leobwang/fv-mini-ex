/- M190 | One family: linear solutions are Y plus B−L | 15-20 min | ACCSystem, LinSols, decomp lemmas, linarith, funext/match, physlib
GOAL
  One SM family plus a right-handed neutrino has species `Q, U, D, L, E, N` (indices 0..5). Every charge vector
  `S` solving the four linear anomaly equations also solves the quadratic and cubic ones, and equals
  `(Q − N/3)·Y + (N/3)·(B−L)` with hypercharge `Y = (1, −4, 2, −3, 6, 0)` and `B−L = (1, −1, −1, −3, 3, 3)`.

REFERENCE
  `S : (PlusU1 1).LinSols` bundles a charge vector `S.val` (6 rational entries) with proofs of the linear ACCs.
  #check PlusU1.gravSol  -- accGrav S.val = 0   (likewise `PlusU1.SU2Sol`, `PlusU1.SU3Sol`, `PlusU1.YYsol`)
  #check accYY_decomp    -- accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + ...   (likewise `accGrav_decomp`, `accSU2_decomp`,
                         --   `accSU3_decomp`, `accQuad_decomp`, `accCube_decomp`; `Q S i` = charge of `Q` in family `i`)
  #check SMνCharges.sum_one       -- one family: `∑ i, f i = f ⟨0, _⟩`
  #check SMνCharges.toSpecies_one -- toSpecies j S ⟨0, _⟩ = S j   (`Q = toSpecies 0`, ..., `N = toSpecies 5`)
  `PlusU1.Y₁.val`, `PlusU1.BL₁.val` are the vectors `Y`, `B−L`; `(a • v) j = a * v j`.
  `funext j; match j with | ⟨0, _⟩ => ... | ⟨5, _⟩ => ...` proves a vector equation entry by entry;
  inside a branch, `change S.val (0 : Fin 6) = (...) * 1 + (...) * 1` exposes the concrete entries.
NOTE: the index type of `(PlusU1 1).Charges` has no numerals: write `S.val (0 : Fin 6)`, not `S.val 0`.
BANNED: add_AFL_quad, add_quad, addQuad, add_AFL_cube, add_AFQ_cube, add_AF_cube, addCube, on_quadBiLin_AFL, on_cubeTriLin_AFL
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace M190

-- BEGIN SPEC
theorem linSol_classification (S : (PlusU1 1).LinSols) :
    accQuad S.val = 0 ∧ accCube S.val = 0 ∧
    S.val = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) • PlusU1.Y₁.val
      + (S.val (5 : Fin 6) / 3) • PlusU1.BL₁.val :=
-- END SPEC
  by
    have hG := PlusU1.gravSol S
    have h2 := PlusU1.SU2Sol S
    have h3 := PlusU1.SU3Sol S
    have hY := PlusU1.YYsol S
    rw [accGrav_decomp] at hG
    rw [accSU2_decomp] at h2
    rw [accSU3_decomp] at h3
    rw [accYY_decomp] at hY
    simp only [sum_one, toSpecies_one] at hG h2 h3 hY
    have hU : S.val (1 : Fin 6) = S.val (5 : Fin 6) - 4 * S.val (0 : Fin 6) := by linarith
    have hD : S.val (2 : Fin 6) = 2 * S.val (0 : Fin 6) - S.val (5 : Fin 6) := by linarith
    have hL : S.val (3 : Fin 6) = -3 * S.val (0 : Fin 6) := by linarith
    have hE : S.val (4 : Fin 6) = 6 * S.val (0 : Fin 6) - S.val (5 : Fin 6) := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [accQuad_decomp]
      simp only [sum_one, toSpecies_one]
      rw [hU, hD, hL, hE]
      ring
    · rw [accCube_decomp]
      simp only [sum_one, toSpecies_one]
      rw [hU, hD, hL, hE]
      ring
    · -- WHY: `change` spells out the entries of `Y₁`, `BL₁`; `linarith` cannot see through the `match`.
      funext j
      match j with
      | ⟨0, _⟩ =>
        change S.val (0 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * 1
          + (S.val (5 : Fin 6) / 3) * 1
        linarith
      | ⟨1, _⟩ =>
        change S.val (1 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * (-4)
          + (S.val (5 : Fin 6) / 3) * (-1)
        linarith
      | ⟨2, _⟩ =>
        change S.val (2 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * 2
          + (S.val (5 : Fin 6) / 3) * (-1)
        linarith
      | ⟨3, _⟩ =>
        change S.val (3 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * (-3)
          + (S.val (5 : Fin 6) / 3) * (-3)
        linarith
      | ⟨4, _⟩ =>
        change S.val (4 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * 6
          + (S.val (5 : Fin 6) / 3) * 3
        linarith
      | ⟨5, _⟩ =>
        change S.val (5 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * 0
          + (S.val (5 : Fin 6) / 3) * 3
        linarith

end M190

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn the four linear ACCs into four linear equations in the six numbers `S.val (k : Fin 6)`. Solving
    them leaves `Q` and `N` free; then everything is algebra.
H2. `have hG := PlusU1.gravSol S` (and `h2`, `h3`, `hY`), `rw [accGrav_decomp] at hG` (etc.), then
    `simp only [sum_one, toSpecies_one] at hG h2 h3 hY`. `linarith` gives `U = N − 4Q`, `D = 2Q − N`,
    `L = −3Q`, `E = 6Q − N`. For the quadratic/cubic parts: decompose, substitute, `ring`.
H3. Last conjunct, one branch per index, e.g. `| ⟨1, _⟩ => change S.val (1 : Fin 6) = (S.val (0 : Fin 6) -
    S.val (5 : Fin 6) / 3) * (-4) + (S.val (5 : Fin 6) / 3) * (-1); linarith` (coefficients from `Y`, `B−L`).
-/
