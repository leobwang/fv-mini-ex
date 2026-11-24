/- M142 | The CHSH operator identity | 15-20 min | CHSH, observables, commutators, noncommutative ring, abel, simp only, mathlib
GOAL
  Observables `A₀ A₁` (Alice) and `B₀ B₁` (Bob) in any ring square to 1, and every `Aᵢ` commutes with every `Bⱼ`.
  Prove the CHSH operator `C = A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁` satisfies `C² = 4 − [A₀, A₁][B₀, B₁]`
  (`[X, Y] = XY − YX`). If Alice's or Bob's pair commutes, `C² = 4`, so the CHSH value is at most 2.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M142

/- SKELETON · chsh_sq
  1. State two helpers whose left sides have a free tail `x`, so they match inside a word:   R1
       sw  : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)
             proof: R2, R3, rw [← h], R4
       sq1 : ∀ {a : R}, a * a = 1 → ∀ x, a * (a * x) = x
             proof: R2, R3, rw [h], R5
  2. Split the numeral 4 so `abel` can cancel the four 1s later:                              R6
  3. One `simp only [...]` bringing every word to normal form (A's before B's, no squares):
       expand the square and distribute                                                      R7, R8
       right-nest every word                                                                 R9
       move each A left past each B: `sw h₀₀`, `sw h₀₁`, `sw h₁₀`, `sw h₁₁`                   R10
       cancel squares: `sq1 hA₀`, `sq1 hA₁` (with a tail)                                     R11
         and all four squares `hA₀ hA₁ hB₀ hB₁` themselves (at a word end; once `mul_one`
         fires, `A₀ * A₀` can end up there too)                                               R12
       drop the leftover `* 1`                                                               R13
  4. Both sides are now sums of the same words:                                              R14
-/
-- BEGIN SPEC
theorem chsh_sq {R : Type} [Ring R] (A₀ A₁ B₀ B₁ : R)
    (hA₀ : A₀ * A₀ = 1) (hA₁ : A₁ * A₁ = 1) (hB₀ : B₀ * B₀ = 1) (hB₁ : B₁ * B₁ = 1)
    (h₀₀ : A₀ * B₀ = B₀ * A₀) (h₀₁ : A₀ * B₁ = B₁ * A₀) (h₁₀ : A₁ * B₀ = B₀ * A₁) (h₁₁ : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) ^ 2 = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) :=
-- END SPEC
  sorry

end M142

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ring` needs a commutative `*`, so it does not apply. Expand both sides into words of four letters and put
    every word in a normal form: all `A`s before all `B`s, squares removed. Then the two sides are sums of the
    same words, and `abel` (sums and differences only) finishes.
H2. The hypotheses `h₀₀ : A₀ * B₀ = …`, `hA₀ : A₀ * A₀ = 1` do not match inside a right-nested word
    `x * (B₀ * (A₀ * y))`. Prove two helpers with a tail `x` (SKELETON step 1, R1), split `4` into
    `1 + 1 + 1 + 1` (R6), then do all the rewriting in one `simp only` (R7–R13) and close with `abel` (R14).
H3. `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]`, then
    `simp only [sq, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, sw h₀₀, sw h₀₁, sw h₁₀, sw h₁₁, sq1 hA₀,
    sq1 hA₁, hA₀, hA₁, hB₀, hB₁, mul_one]`, then `abel`. If `abel` fails, find the word not yet in normal form.
-/
