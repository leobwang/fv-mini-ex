/- E066 | ε–δ binders and abs | 2-3 min | ∀ ε > 0, binder predicates, abs_sub_lt_iff, Set.Icc, mathlib
GOAL
  Read and prove statements in analysis shape: `∀ ε > 0, ∃ δ > 0, …`, `|x - a| < r` as an interval,
  and membership in `Set.Icc a b` (the closed interval [a, b]). `|x|` is the absolute value.
BANNED: grind, exists_between, exact?, apply?, try?

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E066

/- SKELETON · eps_half
  1. Open the binder `∀ ε > 0`: an `ε` and `hε : ε > 0`:                                  R1
  2. Name a witness `δ` strictly between `0` and `ε`; one goal per `?_`:                   R2
  3. `δ > 0` from `hε`:                                                                   R3
  4. `δ < ε` from `hε`:                                                                   R4
-/
-- BEGIN SPEC
theorem eps_half : ∀ ε > (0 : ℝ), ∃ δ > 0, δ < ε :=
-- END SPEC
  sorry

/- SKELETON · abs_sub_lt
  1. Turn `|x - 1| < 2` into two linear inequalities:                                     R5
  2. Split the `↔` into its two directions (`mp`, `mpr`):                                 R6
  3. In each direction: `intro h`, split the `∧` goal with `constructor`
     (TACTIC_STATES, "Structure"), close each half from `h.1` and `h.2`:                  R7
-/
-- BEGIN SPEC
theorem abs_sub_lt (x : ℝ) : |x - 1| < 2 ↔ -1 < x ∧ x < 3 :=
-- END SPEC
  sorry

/- SKELETON · Icc_sq
  1. `h : x ∈ Set.Icc 0 1` is the pair `0 ≤ x ∧ x ≤ 1`: `h.1`, `h.2` (no rewrite needed):  R8
  2. Feed both halves to the power lemma (as a term, or `apply` it and close two goals):  R9
-/
-- BEGIN SPEC
theorem Icc_sq (x : ℝ) (h : x ∈ Set.Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 :=
-- END SPEC
  sorry

/- SKELETON · linear_cont
  1. Open `∀ ε > 0`:                                                                       R1
  2. Witness `δ := ε / 3`; fill the `δ > 0` slot with `by …` and the `∀ x, |x| < δ → …`
     slot with `fun x hx => ?_`:                                                          R2, R3, R10
  3. Rewrite `|f x|` to `|3| * |x|`, then evaluate `|3|`:                                 R11 → R12 → R13
  4. Close `3 * |x| < ε` from `hx : |x| < ε / 3`:                                        R4
-/
-- BEGIN SPEC
theorem linear_cont (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε :=
-- END SPEC
  sorry

end E066

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every binder `∀ ε > 0` is two `intro`s (R1), every `∃ δ > 0` is a triple `⟨δ, _, _⟩` (R2), and
    `x ∈ Set.Icc a b` is already the pair `a ≤ x ∧ x ≤ b` (R8). Once the shapes are opened, what is
    left is linear arithmetic.
H2. `eps_half`: `δ = ε / 2`. `abs_sub_lt`: `rw [abs_sub_lt_iff]`, split the `↔`, and each of the four
    inequality goals is linear in `x`. `Icc_sq`: `h.1 : 0 ≤ x` and `h.2 : x ≤ 1` are the premises of
    `pow_le_one₀`. `linear_cont`: `δ = ε / 3`, and `|f x| = |3 * x| = |3| * |x| = 3 * |x|`.
H3. `refine ⟨ε / 2, by positivity, ?_⟩`, then `linarith`; `constructor <;> intro h <;> constructor <;>
    linarith [h.1, h.2]`; `pow_le_one₀ h.1 h.2`; in `linear_cont`,
    `refine ⟨ε / 3, by positivity, fun x hx => ?_⟩` and `rw [hf, abs_mul]` before `norm_num`.
-/
