/- E066 | ε–δ binders and abs | 2-3 min | ∀ ε > 0, binder predicates, abs_sub_lt_iff, Set.Icc, mathlib
GOAL
  Read and prove statements in analysis shape: `∀ ε > 0, ∃ δ > 0, …`, `|x - a| < r` as an interval,
  and membership in `Set.Icc a b` (the closed interval [a, b]). `|x|` is the absolute value.

REFERENCE
  `∀ ε > 0, P ε` means `∀ ε, ε > 0 → P ε`;  `∃ δ > 0, Q δ` means `∃ δ, δ > 0 ∧ Q δ`
  example : ∀ ε > (0 : ℝ), ∃ δ > 0, δ ≤ ε := by intro ε hε; exact ⟨ε, hε, le_refl ε⟩
  #check abs_sub_lt_iff   -- |a - b| < c ↔ a - b < c ∧ b - a < c
  #check abs_mul          -- |a * b| = |a| * |b|
  #check Set.mem_Icc      -- x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b
  #check pow_le_one₀      -- 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
  example (x : ℝ) (h : x ∈ Set.Icc (0 : ℝ) 2) : x ≤ 2 := h.2   -- membership is an ∧: use .1 / .2
  example (ε : ℝ) (h : 0 < ε) : 0 < ε / 3 := by positivity
BANNED: grind, exists_between, exact?, apply?, try?
-/
import Mathlib

namespace E066

-- BEGIN SPEC
theorem eps_half : ∀ ε > (0 : ℝ), ∃ δ > 0, δ < ε :=
-- END SPEC
  by
    intro ε hε
    exact ⟨ε / 2, by positivity, by linarith⟩

-- BEGIN SPEC
theorem abs_sub_lt (x : ℝ) : |x - 1| < 2 ↔ -1 < x ∧ x < 3 :=
-- END SPEC
  by
    rw [abs_sub_lt_iff]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

-- BEGIN SPEC
theorem Icc_sq (x : ℝ) (h : x ∈ Set.Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 :=
-- END SPEC
  pow_le_one₀ h.1 h.2   -- WHY: `h : x ∈ Set.Icc 0 1` is the pair `0 ≤ x ∧ x ≤ 1`

-- BEGIN SPEC
theorem linear_cont (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε :=
-- END SPEC
  by
    intro ε hε
    refine ⟨ε / 3, by positivity, fun x hx => ?_⟩
    rw [hf, abs_mul]
    norm_num
    linarith

end E066

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Open each `∀ ε > 0` with `intro ε hε`; give `∃ δ > 0, …` as `⟨δ, proof of δ > 0, proof of the rest⟩`.
H2. `eps_half`: δ = ε / 2. `abs_sub_lt`: rewrite with `abs_sub_lt_iff`, then every direction is linear.
    `Icc_sq`: `h.1 : 0 ≤ x` and `h.2 : x ≤ 1` are the premises of `pow_le_one₀`. `linear_cont`: δ = ε / 3,
    and `|f x| = |3 * x| = |3| * |x|`.
H3. `rw [abs_sub_lt_iff]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]`;
    `intro ε hε; refine ⟨ε / 3, by positivity, fun x hx => ?_⟩; rw [hf, abs_mul]; norm_num; linarith`.
-/
