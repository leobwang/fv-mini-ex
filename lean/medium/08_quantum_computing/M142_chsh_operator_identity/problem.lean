/- M142 | The CHSH operator identity | 15-20 min | CHSH, observables, commutators, noncommutative ring, abel, simp only, mathlib
GOAL
  Observables `A₀ A₁` (Alice) and `B₀ B₁` (Bob) in any ring square to 1, and every `Aᵢ` commutes with every `Bⱼ`.
  Prove the CHSH operator `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` satisfies `C² = 4 − [A₀, A₁][B₀, B₁]`
  (`[X, Y] = XY − YX`). If Alice's or Bob's pair commutes, `C² = 4`, so the CHSH value is at most 2.

REFERENCE
  example {R : Type} [Ring R] (a b : R) : (a + b) * (a - b) = a * a - a * b + b * a - b * b := by noncomm_ring
  -- `noncomm_ring` proves identities true in every ring; it cannot use hypotheses such as `A₀ * A₀ = 1`.
  example {R : Type} [Ring R] (a b c d : R) : a + b - c + d - b = d + a - c := by abel  -- `+`/`-` only, products are atoms
  #check @mul_assoc   -- a * b * c = a * (b * c)   (`simp only [mul_assoc]` makes every product right-nested)
  #check @add_mul     -- (a + b) * c = a * c + b * c   (also `mul_add`, `sub_mul`, `mul_sub`, `sq`)
  example {R : Type} [Ring R] (a b x : R) (h : a * b = b * a) : b * (a * x) = a * (b * x) := by
    rw [← mul_assoc, ← h, mul_assoc]
  example {R : Type} [Ring R] : (4 : R) = 1 + 1 + 1 + 1 := by norm_num
NOTE: `ring` does not apply: `R` is not commutative.
-/
import Mathlib

namespace M142

-- BEGIN SPEC
theorem chsh_sq {R : Type} [Ring R] (A₀ A₁ B₀ B₁ : R)
    (hA₀ : A₀ * A₀ = 1) (hA₁ : A₁ * A₁ = 1) (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1)
    (h₀₀ : A₀ * B₀ = B₀ * A₀) (h₀₁ : A₀ * B₁ = B₁ * A₀) (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₁₁ : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ^ 2 = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) :=
-- END SPEC
  sorry

end M142

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Expand everything into words of length 4 (right-nested with `mul_assoc`), then use the hypotheses to put every word
    into a normal form: all `A`s before all `B`s, and `XX = 1` removed. Once both sides are in normal form, `abel` finishes.
H2. Hypotheses in the shape `a * b = …` do not match inside `x * (a * (b * y))`. State two local helpers that do:
    `sw : a * b = b * a → ∀ x, b * (a * x) = a * (b * x)` (move an `A` left past a `B`) and
    `sq1 : a * a = 1 → ∀ x, a * (a * x) = x`. Replace `4` by `1 + 1 + 1 + 1` first so `abel` can match it.
H3. `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]`, then one `simp only [...]` with: `sq`, the four distributivity
    lemmas, `mul_assoc`, each helper applied to each matching hypothesis (`sw h₀₀`, …, `sq1 hA₀`, …), the squares
    themselves and `mul_one`; then `abel`. If `abel` fails, look for a word that is not yet in normal form.
-/
