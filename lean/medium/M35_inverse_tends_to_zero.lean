/- M35 | 1/(n+1) tends to 0 | 15 min | epsilon-N, Archimedean, abs, mathlib
GOAL
  With the explicit ε-N definition of convergence, prove that constant sequences converge and
  that `1 / (n + 1) → 0`.

REFERENCE
  #check exists_nat_gt   -- (x : R) : ∃ n : ℕ, x < n      (Archimedean property)
  #check div_lt_iff₀     -- 0 < c → (b / c < a ↔ b < a * c)
  #check abs_of_pos      -- 0 < a → |a| = a
  example (N n : ℕ) (h : N ≤ n) : (N : ℝ) ≤ n := by exact_mod_cast h   -- cast an ℕ fact to ℝ
  example (ε : ℝ) (h : 0 < ε) : |(0 : ℝ)| < ε := by simpa using h
  `refine ⟨N, fun n hn => ?_⟩` supplies the witness and leaves the inequality to prove.
-/
import Mathlib

namespace M35

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
theorem const_converges (c : ℝ) : ConvergesTo (fun _ => c) c :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem inv_succ_converges : ConvergesTo (fun n => 1 / ((n : ℝ) + 1)) 0 :=
-- END SPEC
  sorry

end M35

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold: given `ε > 0`, find `N` with `1 / (n + 1) < ε` for all `n ≥ N`. Choose `N > 1 / ε`.
H2. Get `N` from `exists_nat_gt (1 / ε)`; remove the absolute value (the term is positive) and clear denominators with `div_lt_iff₀`.
H3. `rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]`, `rw [div_lt_iff₀ hε] at hN`, then `nlinarith` using `(N : ℝ) ≤ n`.
-/
