/- M053 | Sums of two squares mod 4 | 10-15 min | ZMod, Int.cast, push_cast, decide, mathlib
GOAL
  Squares are 0 or 1 in `ZMod 4`; conclude that no integer `a² + b²` is `3 mod 4`.

REFERENCE
  example : ∀ x : ZMod 3, x ^ 3 = x := by decide    -- ZMod n is finite: decide checks every element
  #check ZMod.intCast_mod   -- (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b)
  example (a : ℤ) : ((a ^ 2 + 1 : ℤ) : ZMod 4) = (a : ZMod 4) ^ 2 + 1 := by push_cast; ring
  example (a : ℤ) (P : ZMod 4 → Prop) (h : ∀ x, P x) : P a := by
    generalize (a : ZMod 4) = x; exact h x     -- forget that x came from a, to `decide` over it
  `push_cast [h] at h1` pushes casts inward and rewrites with `h` along the way.
-/
import Mathlib

namespace M053

-- BEGIN SPEC
theorem sq_mod_four (x : ZMod 4) : x ^ 2 = 0 ∨ x ^ 2 = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem two_squares_ne_three (a b : ℤ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 :=
-- END SPEC
  sorry

end M053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ZMod 4` has four elements, so statements about all of them are decidable.
H2. Cast the hypothesis `(a² + b²) % 4 = 3` into `ZMod 4`: it becomes `(a:ZMod 4)² + (b:ZMod 4)² = 3`.
H3. `have h1 := ZMod.intCast_mod (a ^ 2 + b ^ 2) 4; push_cast [h] at h1`, then `generalize` both casts and `revert x y; decide`.
-/
