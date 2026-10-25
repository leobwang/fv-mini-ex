/- M36 | Limit of a sum | 10-15 min | epsilon-N, epsilon/2, max, triangle inequality, mathlib
GOAL
  If `a n → La` and `b n → Lb`, then `a n + b n → La + Lb`, using the explicit ε-N definition.

REFERENCE
  #check abs_add_le   -- (a b : α) : |a + b| ≤ |a| + |b|
  example (N1 N2 n : ℕ) (h : max N1 N2 ≤ n) : N1 ≤ n := le_of_max_le_left h   -- (and _right)
  example (ε : ℝ) (h : 0 < ε) : 0 < ε / 2 := by positivity
  example (a b c d : ℝ) (h1 : a < c) (h2 : b < d) : a + b < c + d := add_lt_add h1 h2
  example (x y u v : ℝ) : x + y - (u + v) = (x - u) + (y - v) := by ring
  `calc` chains `=`, `≤`, `<` steps into a final `<`.
BANNED: Filter.Tendsto.add, tendsto_add
-/
import Mathlib

namespace M36

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
theorem converges_add (a b : ℕ → ℝ) (La Lb : ℝ) (ha : ConvergesTo a La) (hb : ConvergesTo b Lb) :
    ConvergesTo (fun n => a n + b n) (La + Lb) :=
-- END SPEC
  by
    intro ε hε
    obtain ⟨N1, h1⟩ := ha (ε / 2) (by positivity)
    obtain ⟨N2, h2⟩ := hb (ε / 2) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have e1 := h1 n (le_of_max_le_left hn)
    have e2 := h2 n (le_of_max_le_right hn)
    calc |a n + b n - (La + Lb)| = |(a n - La) + (b n - Lb)| := by ring_nf
      _ ≤ |a n - La| + |b n - Lb| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add e1 e2
      _ = ε := by ring

end M36

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Ask each hypothesis for precision `ε / 2`; take `N = max N1 N2`.
H2. Regroup `a n + b n - (La + Lb)` as `(a n - La) + (b n - Lb)` and apply the triangle inequality.
H3. `calc |a n + b n - (La + Lb)| = |(a n - La) + (b n - Lb)| := by ring_nf; _ ≤ ... := abs_add_le _ _; _ < ε / 2 + ε / 2 := add_lt_add e1 e2; _ = ε := by ring`.
-/
