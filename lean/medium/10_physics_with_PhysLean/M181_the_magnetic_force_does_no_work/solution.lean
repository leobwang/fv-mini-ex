/- M181 | The magnetic force does no work | 5-10 min | EuclideanSpace inner product, cross product, PiLp.inner_apply, physlib
GOAL
  A charge `q` moving with velocity `v` in fields `E`, `B` feels the Lorentz force `F = q (E + v × B)`.
  Show that the power `v · F` equals `q (v · E)`: the magnetic part `v × B` is orthogonal to `v`.
BANNED: inner_self_cross, inner_cross_self, dot_self_cross, dot_cross_self, exact?, apply?, rw?, hint, observe, try?

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.CrossProduct

open Space InnerProductSpace Matrix

namespace M181

-- BEGIN SPEC
/-- The Lorentz force on a charge `q` with velocity `v` in fields `E` and `B`. -/
noncomputable def lorentzForce (q : ℝ) (E B v : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  q • (E + v ⨯ₑ₃ B)
-- END SPEC

/- SKELETON · lorentzForce_power
  1. Prove the key fact first (a `have`, TACTIC_STATES):
       h : ⟪v, v ⨯ₑ₃ B⟫_ℝ = 0
     proof: dot product → sum of components                                R1
            one `simp` with the sum and cross-product lemmas: three terms,
            each component's formula, each real inner product → a product   R2, R3, R4
            the six products cancel in pairs                               R5
  2. Unfold the force:                                                      R6
  3. Linearity in the second slot, then substitute the fact and clean up:
       pull out `q`, split `E + v ⨯ₑ₃ B`                                    R7 → R8
       rw [h], then drop the `+ 0`                                         rw [h], R9
     (`rw` only here: `simp` would rewrite `v ⨯ₑ₃ B` and `h` would no longer match.)
-/
-- BEGIN SPEC
theorem lorentzForce_power (q : ℝ) (E B v : EuclideanSpace ℝ (Fin 3)) :
    ⟪v, lorentzForce q E B v⟫_ℝ = q * ⟪v, E⟫_ℝ :=
-- END SPEC
  by
    have h : ⟪v, v ⨯ₑ₃ B⟫_ℝ = 0 := by
      simp only [PiLp.inner_apply]
      simp [Fin.sum_univ_three, cross_apply]
      ring
    unfold lorentzForce
    rw [real_inner_smul_right, inner_add_right, h, add_zero]

end M181

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The electric part gives `q * ⟪v, E⟫_ℝ`; everything else must vanish because `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`.
    Prove that fact first as a `have`, then do the linear algebra.
H2. The fact by components: R1 (`PiLp.inner_apply`) turns the dot product into a sum, `simp` with R2, R3
    expands it into three products, and `ring` (R5) cancels them. The main goal: `unfold`, then `rw` with
    R7, R8, the fact, and R9.
H3. The key line is `have h : ⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`, proved by `simp only [PiLp.inner_apply]`, then `simp` with
    `Fin.sum_univ_three` and `cross_apply`, then `ring`. After `unfold lorentzForce`, one `rw [...]` chain
    of R7, R8, `h`, R9 closes the goal.
-/
