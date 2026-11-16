/- M104 | Floating-point products | 15-20 min | relative error model, list induction, abs, gcongr, mathlib
GOAL
  Standard model: every rounded operation returns `x (1 + δ)` with `|δ| ≤ u`. Then a product of `n`
  numbers computed right-to-left has relative error at most `(1 + u)ⁿ - 1` (≈ n u): products are benign.

REFERENCE
  #check abs_add_le     -- |a + b| ≤ |a| + |b|
  #check abs_mul        -- |a * b| = |a| * |b|
  #check List.prod_cons -- (a :: l).prod = a * l.prod
  example (a b : ℝ) (n : ℕ) : (a + b) ^ (n + 1) = (a + b) ^ n * (a + b) := pow_succ _ _
  example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
  example (θ δ : ℝ) : (1 + θ) * (1 + δ) = 1 + (θ + δ + θ * δ) := by ring   -- errors compose like this
  `fl : ℝ → ℝ` is an abstract rounding function; `RelErr u fl` is all you know about it (it forces `0 ≤ u`).
NOTE: this model also rounds the last factor `xₙ * 1`, so it makes `n` roundings; real hardware makes
  `n - 1`, and the same proof gives `(1 + u)^(n-1) - 1` (Higham's `γₙ₋₁ ≈ (n-1) u`).
-/
import Mathlib

namespace M104

-- BEGIN SPEC
/-- `fl` rounds every real with relative error at most `u`. -/
def RelErr (u : ℝ) (fl : ℝ → ℝ) : Prop := ∀ x, ∃ δ, |δ| ≤ u ∧ fl x = x * (1 + δ)

/-- floating-point product: `[x₁, x₂, …, xₙ] ↦ fl (x₁ * fl (x₂ * … fl (xₙ * 1)))` -/
def fprod (fl : ℝ → ℝ) : List ℝ → ℝ
  | [] => 1
  | x :: xs => fl (x * fprod fl xs)
-- END SPEC

-- BEGIN SPEC
theorem fprod_error (u : ℝ) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    ∃ θ, |θ| ≤ (1 + u) ^ xs.length - 1 ∧ fprod fl xs = xs.prod * (1 + θ) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fprod_abs_error (u : ℝ) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    |fprod fl xs - xs.prod| ≤ ((1 + u) ^ xs.length - 1) * |xs.prod| :=
-- END SPEC
  sorry

end M104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `xs`. Nil: `θ = 0`. Cons: you get `θ` for the tail from the IH and `δ` from
    `hfl (x * fprod fl xs)`; the new error is `θ + δ + θ * δ`.
H2. Bound `|θ + δ + θ δ| ≤ |θ| + |δ| + |θ| |δ|` (triangle inequality twice + `abs_mul`), then compare with
    `(1 + u)^(n+1) - 1 = ((1 + u)^n - 1) + u + ((1 + u)^n - 1) * u`. The second theorem follows from the first.
H3. Cons case: `obtain ⟨θ, hθ, hq⟩ := ih; obtain ⟨δ, hδ, hfx⟩ := hfl (x * fprod fl xs)`;
    `refine ⟨θ + δ + θ * δ, ?_, ?_⟩`. Bound: also prove `|θ| * |δ| ≤ ((1 + u) ^ xs.length - 1) * u` by `gcongr`
    (`gcongr` leaves `0 ≤ (1 + u) ^ xs.length - 1`; close it with `le_trans (abs_nonneg _) hθ`),
    then `simp only [List.length_cons, pow_succ]; nlinarith`. Equation: `rw [fprod, hfx, hq, List.prod_cons]; ring`.
-/
