/- M097 | Stationary distribution of a 2-state chain | 15 min | Markov chain, Matrix.vecMul, fin_cases, field_simp, mathlib
GOAL
  A chain on states {0, 1} leaves state 0 with probability `a` and state 1 with probability `b`
  (`a + b > 0`). Show its stationary distributions (probability vectors `π` with `π P = π`) are
  exactly `π = (b / (a + b), a / (a + b))`. The statement only assumes `a, b ≥ 0`, `a + b > 0`
  (more general than probabilities; `a, b ≤ 1` is never needed).

REFERENCE
  example : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]  -- matrix literal, rows split by `;`
  example : (![5, 6] : Fin 2 → ℝ) 1 = 6 := by simp      -- vector literal; `simp` reads entries
  example (v : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix.vecMul v M 0 = v 0 * M 0 0 + v 1 * M 1 0 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]   -- row vector times matrix, coordinate 0
  #check congrFun   -- f = g → ∀ a, f a = g a   (one coordinate of a vector equation)
  example (v w : Fin 2 → ℝ) (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
    ext i; fin_cases i <;> simpa                         -- vectors are equal coordinatewise
  `field_simp` clears denominators once `a + b ≠ 0` is a hypothesis; then `ring` or `nlinarith`.
-/
import Mathlib

namespace M097

-- BEGIN SPEC
/-- transition matrix: row `i` is the distribution of the next state from state `i`
    (leave state 0 w.p. `a`, leave state 1 w.p. `b`). -/
def P (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]

/-- `π` is a probability vector fixed by the chain: `π P = π`. -/
def IsStationary (a b : ℝ) (π : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ π 0 + π 1 = 1 ∧ Matrix.vecMul π (P a b) = π
-- END SPEC

-- BEGIN SPEC
theorem stationary_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (π : Fin 2 → ℝ) :
    IsStationary a b π ↔ π = ![b / (a + b), a / (a + b)] :=
-- END SPEC
  sorry

end M097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Coordinate 0 of `π P = π` reads `π 0 * (1 - a) + π 1 * b = π 0`, i.e. `a * π 0 = b * π 1`.
    With `π 0 + π 1 = 1` that pins `π` down. The converse is three direct checks.
H2. `constructor`. (→) `rintro ⟨-, hsum, hfix⟩`, take `congrFun hfix 0` and `simp [...]` it, then
    `ext i; fin_cases i` and solve each coordinate. (←) `rintro rfl; refine ⟨?_, ?_, ?_⟩`.
H3. `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] at h0`; each coordinate closes with
    `simp; field_simp; nlinarith`. Nonnegativity is `positivity`; the fixed point is
    `ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] <;> field_simp <;> ring`.
-/
