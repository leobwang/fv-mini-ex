/- M104 | Floating-point products | 15-20 min | relative error model, list induction, abs, gcongr, mathlib
GOAL
  Standard model: every rounded operation returns `x (1 + δ)` with `|δ| ≤ u`. Then a product of `n`
  numbers computed right-to-left has relative error at most `(1 + u)ⁿ - 1` (≈ n u): products are benign.

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · fprod_error
  1. Induction on the list:                                                 R1
  2. nil: witness θ = 0, then one goal per conjunct:                        R2
       |0| ≤ (1 + u) ^ [].length - 1                                        R3 (`simp`)
       fprod fl [] = [].prod * (1 + 0)                                      R4, R5 (`simp [fprod]`)
  3. cons: take the tail's error apart, then the last rounding's error:
       θ, hθ, hq  from ih                                                   R6
       δ, hδ, hfx from hfl applied to `x * fprod fl xs`                     R7, R6
     witness θ + δ + θ * δ, one goal per conjunct:                          R2
  4. The bound. Prove two facts first, then combine them:
       h1 : |θ + δ + θ * δ| ≤ |θ| + |δ| + |θ| * |δ|
            a two-step calc: split off θ * δ, then split θ + δ              R8, R9, R10 → R11 → R9
       h2 : |θ| * |δ| ≤ ((1 + u) ^ xs.length - 1) * u
            gcongr uses hθ, hδ; its side goal 0 ≤ (1 + u) ^ xs.length - 1   R12, R14 with R13 and hθ
     rewrite (x :: xs).length and the power, then add up hθ, hδ, h1, h2:   R15, R16, R17
  5. The equation: unfold fprod, substitute, expand the list product:       R4, rw [hfx], rw [hq], R18, ring
-/
-- BEGIN SPEC
theorem fprod_error (u : ℝ) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    ∃ θ, |θ| ≤ (1 + u) ^ xs.length - 1 ∧ fprod fl xs = xs.prod * (1 + θ) :=
-- END SPEC
  by
    induction xs with
    | nil => exact ⟨0, by simp, by simp [fprod]⟩
    | cons x xs ih =>
      obtain ⟨θ, hθ, hq⟩ := ih
      obtain ⟨δ, hδ, hfx⟩ := hfl (x * fprod fl xs)
      refine ⟨θ + δ + θ * δ, ?_, ?_⟩
      · have h1 : |θ + δ + θ * δ| ≤ |θ| + |δ| + |θ| * |δ| := by
          calc _ ≤ |θ + δ| + |θ * δ| := abs_add_le _ _
            _ ≤ _ := by rw [abs_mul]; gcongr; exact abs_add_le _ _
        have h2 : |θ| * |δ| ≤ ((1 + u) ^ xs.length - 1) * u := by
          gcongr
          exact le_trans (abs_nonneg _) hθ
        simp only [List.length_cons, pow_succ]
        nlinarith
      · rw [fprod, hfx, hq, List.prod_cons]
        ring

/- SKELETON · fprod_abs_error
  1. Take θ from the theorem above (applied to u fl hfl xs):                R7, R6
  2. Substitute fprod fl xs, then pull the absolute value apart:
       rw [h]; xs.prod * (1 + θ) - xs.prod = xs.prod * θ; |·| of a product;
       swap the factors so the left side reads |θ| * |xs.prod|              rw [h], R19, R10, R20
  3. Compare factor by factor (hθ is in the context):                       R12
-/
-- BEGIN SPEC
theorem fprod_abs_error (u : ℝ) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    |fprod fl xs - xs.prod| ≤ ((1 + u) ^ xs.length - 1) * |xs.prod| :=
-- END SPEC
  by
    obtain ⟨θ, hθ, h⟩ := fprod_error u fl hfl xs
    rw [h, show xs.prod * (1 + θ) - xs.prod = xs.prod * θ by ring, abs_mul, mul_comm]
    gcongr

end M104

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on `xs`. Nil: `θ = 0`. Cons: you get `θ` for the tail from `ih` and `δ` for the last rounding
    from `hfl (x * fprod fl xs)`; since `(1 + θ) * (1 + δ) = 1 + (θ + δ + θ * δ)`, the new error is
    `θ + δ + θ * δ`. The second theorem follows from the first.
H2. Bound `|θ + δ + θ * δ| ≤ |θ| + |δ| + |θ| * |δ|` (triangle inequality twice, `abs_mul`) and
    `|θ| * |δ| ≤ ((1 + u) ^ n - 1) * u` (`gcongr`), then compare with
    `(1 + u) ^ n * (1 + u) - 1 = ((1 + u) ^ n - 1) + u + ((1 + u) ^ n - 1) * u` by `nlinarith`.
    Second theorem: `|xs.prod * (1 + θ) - xs.prod| = |θ| * |xs.prod|`, then `gcongr`.
H3. Cons case: `obtain ⟨θ, hθ, hq⟩ := ih; obtain ⟨δ, hδ, hfx⟩ := hfl (x * fprod fl xs)`;
    `refine ⟨θ + δ + θ * δ, ?_, ?_⟩`. The middle term of `h1`'s calc is `|θ + δ| + |θ * δ|`. The `gcongr`
    for `h2` leaves `0 ≤ (1 + u) ^ xs.length - 1`: close it with `le_trans (abs_nonneg _) hθ`. Then
    `simp only [List.length_cons, pow_succ]; nlinarith`. Equation: `rw [fprod, hfx, hq, List.prod_cons]; ring`.
-/
