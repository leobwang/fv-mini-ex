/- M141 | CHSH inequality for local hidden variables | 15 min | CHSH, Bell inequality, abs, Finset sums, case bash, mathlib
GOAL
  A local-hidden-variable model: a hidden value `l : Λ` with probability `p l`; Alice's setting `x` and
  Bob's setting `y` give outcomes `A x l, B y l ∈ {±1}`. Prove `|E₀₀ + E₀₁ + E₁₀ − E₁₁| ≤ 2`, where
  `Eₓᵧ = ∑ l, p l * A x l * B y l` (all four correlations are written inside one sum).

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M141

/- SKELETON · chsh_lhv
  1. MILESTONE, prove first (step 2c uses it): the bound for one hidden value
       pt : ∀ l, |A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l| ≤ 2
     proof: intro l, then split the four ±1 facts hA 0 l, hA 1 l, hB 0 l, hB 1 l,
     chained with <;> (16 goals)                                           R1, R2
     in all 16 goals (<;>): rw [h1, h2, h3, h4], then finish the numbers    R4 (uses R3)
  2. Average over l with a four-step chain:                                 R5
     a. |∑ l, p l * X l| ≤ ∑ l, |p l * X l|      (X l: the bracket)          R6
     b.                  = ∑ l, p l * |X l|      termwise, with hp l         R7 → R8 → R9
     c.                  ≤ ∑ l, p l * 2          termwise, with pt l, hp l   R10 → R11
     d.                  = 2                     factor 2 out, use hsum      R12 → rw [hsum] → R13
-/
-- BEGIN SPEC
theorem chsh_lhv {Λ : Type} [Fintype Λ] (p : Λ → ℝ) (hp : ∀ l, 0 ≤ p l) (hsum : ∑ l, p l = 1)
    (A B : Fin 2 → Λ → ℝ) (hA : ∀ x l, A x l = 1 ∨ A x l = -1) (hB : ∀ y l, B y l = 1 ∨ B y l = -1) :
    |∑ l, p l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)| ≤ 2 :=
-- END SPEC
  by
    have pt : ∀ l, |A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l| ≤ 2 := by
      intro l
      rcases hA 0 l with h1 | h1 <;> rcases hA 1 l with h2 | h2 <;> rcases hB 0 l with h3 | h3 <;>
        rcases hB 1 l with h4 | h4 <;> rw [h1, h2, h3, h4] <;> norm_num [abs_le]
    calc _ ≤ ∑ l, |p l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, p l * |A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l| :=
          Finset.sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (hp l)]
      _ ≤ ∑ l, p l * 2 := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (pt l) (hp l)
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

end M141

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the bound for one hidden value first, `pt : ∀ l, |A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁| ≤ 2`
    (it equals `A₀(B₀ + B₁) + A₁(B₀ − B₁)`, and one of the brackets is 0). Then average over `l`:
    the weights `p l` are nonnegative and sum to 1.
H2. `pt`: `intro l`, four `rcases` on `hA 0 l`, `hA 1 l`, `hB 0 l`, `hB 1 l` joined by `<;>` (16 goals),
    then `<;> rw [h1, h2, h3, h4] <;> norm_num [abs_le]` (R1–R4).
    Averaging: a `calc` (R5): triangle inequality for sums (R6); `|p l * x| = p l * |x|` termwise
    (R7–R9); bound each term by `p l * 2` with `pt` (R10, R11); factor out 2 and use `hsum` (R12, R13).
H3. `calc _ ≤ ∑ l, |p l * _| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, p l * |…| := Finset.sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (hp l)]
      _ ≤ ∑ l, p l * 2 := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (pt l) (hp l)
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]`
-/
