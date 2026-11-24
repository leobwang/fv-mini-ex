/- M190 | One family: linear solutions are Y plus B−L | 15-20 min | ACCSystem, LinSols, decomp lemmas, linarith, funext/match, physlib
GOAL
  One SM family plus a right-handed neutrino has species `Q, U, D, L, E, N` (indices 0..5). Every charge vector
  `S` solving the four linear anomaly equations also solves the quadratic and cubic ones, and equals
  `(Q − N/3)·Y + (N/3)·(B−L)` with hypercharge `Y = (1, −4, 2, −3, 6, 0)` and `B−L = (1, −1, −1, −3, 3, 3)`.
BANNED: add_AFL_quad, add_quad, addQuad, add_AFL_cube, add_AFQ_cube, add_AF_cube, addCube, on_quadBiLin_AFL, on_cubeTriLin_AFL

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge

open SMνCharges SMνACCs SMRHN

namespace M190

/- SKELETON · linSol_classification
  Write an index as `S.val (k : Fin 6)`; a bare `S.val 0` does not type-check. Q = S.val (0 : Fin 6),
  N = S.val (5 : Fin 6).
  1. The four linear ACCs as hypotheses hG, h2, h3, hY:                    R1
  2. Expand each into the six entries S.val k:                              R2, R3, R4, R5, then R8 (R6 → R7)
  3. Solve the linear system BEFORE splitting, so all three goals get it:  R9, four times
       hU : S.val (1 : Fin 6) = N − 4Q      hD : S.val (2 : Fin 6) = 2Q − N
       hL : S.val (3 : Fin 6) = −3Q         hE : S.val (4 : Fin 6) = 6Q − N
  4. Split the three conjuncts:                                             refine ⟨?_, ?_, ?_⟩
  5. accQuad: decompose, one family, substitute, finish:                    R10, R8, rw [hU, hD, hL, hE], ring
  6. accCube: the same:                                                     R11, R8, rw [hU, hD, hL, hE], ring
  7. The vector equation: entries, then one branch per index ⟨0, _⟩ … ⟨5, _⟩: R12, R13
     in each branch: spell out the entry with the numbers of Y and B−L,
     at that index, then finish:                                            R14, R9
-/
-- BEGIN SPEC
theorem linSol_classification (S : (PlusU1 1).LinSols) :
    accQuad S.val = 0 ∧ accCube S.val = 0 ∧
    S.val = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) • PlusU1.Y₁.val
      + (S.val (5 : Fin 6) / 3) • PlusU1.BL₁.val :=
-- END SPEC
  sorry

end M190

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn the four linear ACCs into four linear equations in the six numbers `S.val (k : Fin 6)` (R1–R8).
    Two of them, `Q` and `N`, stay free; solve for the other four once, before splitting. After that
    every conjunct is algebra.
H2. `have hG := PlusU1.gravSol S` (and `h2`, `h3`, `hY`), `rw [accGrav_decomp] at hG` (etc.), then
    `simp only [sum_one, toSpecies_one] at hG h2 h3 hY`. Four `have … := by linarith` give `U = N − 4Q`,
    `D = 2Q − N`, `L = −3Q`, `E = 6Q − N`. Then `refine ⟨?_, ?_, ?_⟩`: the quadratic and cubic goals by
    decompose, `simp only`, `rw` the four facts, `ring`; the vector goal by `funext j; match j with …`.
H3. One branch, with the coefficients read off `Y` and `B−L` at index 1:
    `| ⟨1, _⟩ => change S.val (1 : Fin 6) = (S.val (0 : Fin 6) - S.val (5 : Fin 6) / 3) * (-4)
        + (S.val (5 : Fin 6) / 3) * (-1); linarith`.
-/
