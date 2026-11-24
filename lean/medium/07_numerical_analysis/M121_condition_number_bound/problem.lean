/- M121 | Condition number bound | 10-15 min | Matrix norms, mulVec, operator norm, relative error, mathlib
GOAL
  If `A x = b`, `A x' = b'` and `B A = 1`, the relative error in the solution is at most
  `κ = ‖A‖ ‖B‖` (the condition number) times the relative error in the data, in the ∞-norm.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M121
open Matrix
open scoped Matrix.Norms.Operator

/- SKELETON · relative_error_le_cond
  Prove the MILESTONES 1–4 first (each a `have`); steps 5–6 use them.
  1. hdx : x' - x = B *ᵥ (b' - b)                                     → used in 4
       rw [← hx, ← hx'], then R1 (←), R2, rw [hBA], R3
  2. hxne : x ≠ 0                                                     → used in 3
       R4 (now hx : A *ᵥ 0 = b), then R5 with a proof of `b = 0`: rw [← hx], R6
  3. hxpos : 0 < ‖x‖ and hbpos : 0 < ‖b‖                    R7, R7    → used in 5, 6
  4. h1 : ‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖   (R8 rewritten by hdx)  R8, R9    → used in 6
     h2 : ‖b‖ ≤ ‖A‖ * ‖x‖              (R8 rewritten by hx)   R8, R9    → used in 6
  5. Clear the left denominator with hxpos:                 R10
  6. calc from ‖x' - x‖ to ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖) * ‖x‖:  R11
       ≤ ‖B‖ * ‖b' - b‖                                  h1
       = ‖B‖ * (‖b' - b‖ / ‖b‖) * ‖b‖                    R12 (needs hbpos)
       ≤ ‖B‖ * (‖b' - b‖ / ‖b‖) * (‖A‖ * ‖x‖)            R13 (uses h2)
       = the goal's right side                          ring
-/
-- BEGIN SPEC
theorem relative_error_le_cond {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hBA : B * A = 1)
    (x x' b b' : Fin n → ℝ) (hx : A *ᵥ x = b) (hx' : A *ᵥ x' = b') (hb : b ≠ 0) :
    ‖x' - x‖ / ‖x‖ ≤ ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖) :=
-- END SPEC
  sorry

end M121

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two bounds do all the work, both instances of `‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖` (R8): one on the error
    `x' - x` via `B`, one on `‖b‖` via `A`. Everything else is algebra on real numbers.
H2. First the milestones: `x' - x = B *ᵥ (b' - b)` (rewrite `hx`, `hx'` backwards, then R1–R3 and `hBA`),
    `x ≠ 0` (else `b = A *ᵥ 0 = 0`), and `0 < ‖x‖`, `0 < ‖b‖`. Then clear the denominator `‖x‖` with
    `div_le_iff₀` and finish with a `calc` chain.
H3. `have h1 : ‖x' - x‖ ≤ ‖B‖ * ‖b' - b‖ := hdx ▸ Matrix.linfty_opNorm_mulVec _ _`, and the same for
    `‖b‖ ≤ ‖A‖ * ‖x‖` with `hx`. After `rw [div_le_iff₀ hxpos]`, `calc` through
    `‖B‖ * (‖b' - b‖ / ‖b‖) * ‖b‖` (`field_simp`) and `‖B‖ * (‖b' - b‖ / ‖b‖) * (‖A‖ * ‖x‖)` (`gcongr`).
-/
