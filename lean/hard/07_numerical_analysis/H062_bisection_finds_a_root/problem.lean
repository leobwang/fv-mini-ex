/- H062 | Bisection finds a root | 1-1.25 h | nested intervals, ciSup, monotone convergence, Filter.Tendsto, continuity, mathlib
GOAL
  Bisection on a continuous `f` with `f a ≤ 0 ≤ f b` converges: some root `r ∈ [a, b]` is within
  `(b - a) / 2ⁿ⁺¹` of the `n`-th midpoint, for every `n`. Take `r` = sup of the left ends `(bisect f a b n).1`
  and pass the signs to the limit (IVT gives *a* root, not this one). Milestones 1-2: paste your M106 proofs.

REFERENCE
  -- `⨆ n, lo n` = supremum of a sequence;  `Tendsto u atTop (𝓝 r)` means `u n → r` (`open Filter Topology`)
  #check le_ciSup                 -- BddAbove (Set.range f) → ∀ c, f c ≤ ⨆ i, f i
  #check ciSup_le                 -- (∀ x, f x ≤ c) → ⨆ i, f i ≤ c
  #check tendsto_atTop_ciSup      -- Monotone f → BddAbove (Set.range f) → Tendsto f atTop (𝓝 (⨆ i, f i))
  #check monotone_nat_of_le_succ  -- (∀ n, f n ≤ f (n + 1)) → Monotone f   (also `antitone_nat_of_succ_le`)
  #check le_of_tendsto'           -- Tendsto f l (𝓝 a) → (∀ c, f c ≤ b) → a ≤ b   (also `ge_of_tendsto'`)
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  example (f : ℝ → ℝ) (hf : Continuous f) (u : ℕ → ℝ) (r : ℝ) (h : Tendsto u atTop (𝓝 r)) :
      Tendsto (fun n => f (u n)) atTop (𝓝 (f r)) := (hf.tendsto r).comp h
  example (lo : ℕ → ℝ) (b : ℝ) (h : ∀ n, lo n ≤ b) : BddAbove (Set.range lo) := ⟨b, by rintro _ ⟨n, rfl⟩; exact h n⟩
  -- limits combine: `h.add g : u + v → a + b`, `h.const_mul c : c * u → c * a`
-/
import Mathlib

open Filter Topology

namespace H062

-- BEGIN SPEC
/-- one bisection step: keep the half `[lo, mid]` or `[mid, hi]` that still has a sign change -/
noncomputable def step (f : ℝ → ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  if f ((I.1 + I.2) / 2) ≤ 0 then ((I.1 + I.2) / 2, I.2) else (I.1, (I.1 + I.2) / 2)

/-- the interval `(lo, hi)` after `n` steps -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 => step f (bisect f a b n)
-- END SPEC

-- MILESTONE (optional: change or delete)  (proved in M106: paste your proof)
theorem bisect_invariant (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 ∧
      (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n := by
  sorry

-- MILESTONE (optional: change or delete)  (proved in M106: paste your proof)
theorem bisect_nested (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).1 ≤ (bisect f a b (n + 1)).1 ∧
      (bisect f a b (n + 1)).2 ≤ (bisect f a b n).2 ∧ (bisect f a b n).2 ≤ b := by
  sorry

-- MILESTONE (optional: change or delete)
-- every left endpoint lies below every right endpoint (compare both with index `max m n`)
theorem lo_le_hi (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) (m n : ℕ) :
    (bisect f a b m).1 ≤ (bisect f a b n).2 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem gap_tendsto (a b : ℝ) : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
  sorry

-- BEGIN SPEC
theorem bisection_finds_root (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b)
    (ha : f a ≤ 0) (hb : 0 ≤ f b) :
    ∃ r, f r = 0 ∧ a ≤ r ∧ r ≤ b ∧ ∀ n,
      |r - ((bisect f a b n).1 + (bisect f a b n).2) / 2| ≤ (b - a) / 2 ^ (n + 1) :=
-- END SPEC
  sorry

end H062

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `lo n`, `hi n` for the endpoints. `lo` increases, `hi` decreases, `hi n - lo n = (b - a) / 2ⁿ → 0`,
    and `lo m ≤ hi n` for all `m, n`. So `r := ⨆ n, lo n` exists and is squeezed: `lo n ≤ r ≤ hi n`.
H2. `lo n → r` (monotone convergence), and `hi n = lo n + (b - a) / 2ⁿ → r + 0`. By continuity
    `f (lo n) → f r` and `f (hi n) → f r`; the signs `f (lo n) ≤ 0 ≤ f (hi n)` pass to the limit, so
    `f r = 0`. The midpoint bound and `a ≤ r ≤ b` (index 0) follow from `lo n ≤ r ≤ hi n`.
H3. `set r := ⨆ n, (bisect f a b n).1`;  `le_ciSup hbdd n`, `ciSup_le fun m => lo_le_hi f a b hab ha hb m n`;
    `le_of_tendsto' ((hf.tendsto r).comp tlo) (fun n => (bisect_invariant f a b ha hb n).1)`; for the
    midpoint: `rw [abs_le, pow_succ, ← div_div, ← hw]; constructor <;> linarith`. For `gap_tendsto`:
    `simp_rw [div_eq_mul_inv, ← inv_pow]` then `(tendsto_pow_atTop_nhds_zero_of_lt_one _ _).const_mul (b - a)`.
-/
