/- H062 | Bisection finds a root | 1-1.25 h | nested intervals, ciSup, monotone convergence, Filter.Tendsto, continuity, mathlib
GOAL
  Bisection on a continuous `f` with `f a ≤ 0 ≤ f b` converges: some root `r ∈ [a, b]` is within
  `(b - a) / 2ⁿ⁺¹` of the `n`-th midpoint, for every `n`. Take `r` = sup of the left ends `(bisect f a b n).1`
  and pass the signs to the limit (IVT gives *a* root, not this one). Milestones 1-2: paste your M106 proofs.

GUIDE
  Entries R1–R36: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · bisect_invariant   (milestone 1; M106 proves it: paste your proof)
  Write lo n, hi n for (bisect f a b n).1, (bisect f a b n).2.
  1. Induct on n:                                                           R1
  2. zero: unfold `bisect` at 0, close with ha, hb:                         simp [bisect, ha, hb]
  3. succ: split ih into its three parts h1 h2 h3:                          R2
     unfold one step of `bisect`, then `step` (an `if`):                    R3
     one goal per branch, hm : f mid ≤ 0  or  hm : ¬f mid ≤ 0:             R4
     each branch: give the two signs (hm or a part of ih; the ¬ branch by R8),
       reduce the pair projections                                          R5
       width: 2 ^ (n + 1) → 2 ^ n * 2, then w / (p * 2) → w / p / 2,
       then the invariant's (b - a) / 2 ^ n → hi - lo                       R6, R7, rw [← h3]
       finish the identity                                                  R9
-/
-- MILESTONE (optional: change or delete)  (proved in M106: paste your proof)
theorem bisect_invariant (f : ℝ → ℝ) (a b : ℝ) (ha : f a ≤ 0) (hb : 0 ≤ f b) (n : ℕ) :
    f (bisect f a b n).1 ≤ 0 ∧ 0 ≤ f (bisect f a b n).2 ∧
      (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n := by
  sorry

/- SKELETON · bisect_nested   (milestone 2; M106 proves it: paste your proof)
  1. The statement mentions step n + 1, so first prove, for all n, by induction:
       hle : ∀ n, lo n ≤ hi n ∧ a ≤ lo n ∧ hi n ≤ b                        R1, R2, R3, R4, R5, R8
  2. Take its parts at n (R2) and split the goal into its four conjuncts: refine with the
     outer two filled by those parts and ?_ for the middle two (a bare `_` is an error here).
  3. The two middle goals mention step n + 1: unfold it, split the `if`, project, finish:
                                                                            R3, R4, R5, R8
-/
-- MILESTONE (optional: change or delete)  (proved in M106: paste your proof)
theorem bisect_nested (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).1 ≤ (bisect f a b (n + 1)).1 ∧
      (bisect f a b (n + 1)).2 ≤ (bisect f a b n).2 ∧ (bisect f a b n).2 ≤ b := by
  sorry

/- SKELETON · lo_le_hi   (milestone 3; uses milestones 1 and 2)
  1. hmono : Monotone fun n => lo n      (bisect_nested, 2nd part)           R10
  2. hanti : Antitone fun n => hi n      (bisect_nested, 3rd part)           R11
  3. hw : ∀ k, lo k ≤ hi k   (bisect_invariant, 3rd part: the width is ≥ 0)
       first 0 ≤ (b - a) / 2 ^ k: numerator by R8, denominator by R13      R12, R8, R13
       then lo k ≤ hi k from the width equation                             R8
  4. Chain through the index max m n:  lo m ≤ lo (max m n) ≤ hi (max m n) ≤ hi n
                                                                            R14 with R15, R16, hw
-/
-- MILESTONE (optional: change or delete)
-- every left endpoint lies below every right endpoint (compare both with index `max m n`)
theorem lo_le_hi (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) (m n : ℕ) :
    (bisect f a b m).1 ≤ (bisect f a b n).2 := by
  sorry

/- SKELETON · gap_tendsto   (milestone 4)
  1. Under the `fun`: (b - a) / 2 ^ n → (b - a) * (2 ^ n)⁻¹ → (b - a) * 2⁻¹ ^ n:   R17, R18
  2. 2⁻¹ ^ n → 0, the two side conditions by norm_num:                     R19
  3. Multiply the limit by (b - a); (b - a) * 0 = 0 closes it:              R20 → R21
-/
-- MILESTONE (optional: change or delete)
theorem gap_tendsto (a b : ℝ) : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
  sorry

/- SKELETON · bisection_finds_root
  Prove the four milestones first: bisect_invariant, bisect_nested (M106), then lo_le_hi, gap_tendsto.
  1. Name the sequences lo, hi := fun n => (bisect f a b n).1, .2 (optional: shorter
     hypotheses; the goal keeps (bisect f a b n).1, since `set` replaces only literal copies):  R22
  2. hbdd : BddAbove (Set.range lo), bound b:                                R23, R24
       the goal lo m ≤ b is closed by `exact lo_le_hi … m 0` (lo m and hi 0 = b agree by definition)
  3. r := ⨆ n, lo n:                                                         R22
  4. The squeeze:  hlo_r : ∀ n, lo n ≤ r                                     R25
                   hr_hi : ∀ n, r ≤ hi n    (lo_le_hi … m n for every m)     R26
  5. tlo : Tendsto lo atTop (𝓝 r)    (lo monotone by bisect_nested)          R10, R27
  6. thi : Tendsto hi atTop (𝓝 r):
       first hi = fun n => lo n + (b - a) / 2 ^ n    (bisect_invariant)      R28, (R29 on the goal), R8
       rewrite with it, add tlo and gap_tendsto, r + 0 = r:                  rw, R30 → R21
  7. h1 : f r ≤ 0   from tlo and bisect_invariant (1st part):                R31 → R32 → R33
     h2 : 0 ≤ f r   from thi and bisect_invariant (2nd part):                R31 → R32 → R34
  8. Give r, f r = 0 from h1 h2 (R35), and three goals:
       a ≤ r   from hlo_r 0, with lo 0 = a:                                  R21 (simpa [lo, bisect])
       r ≤ b   from hr_hi 0, with hi 0 = b:                                  R21 (simpa [hi, bisect])
       midpoint, for n: take hw (bisect_invariant, 3rd part), hlo_r n, hr_hi n;
         unfolding lo, hi in them is optional (linarith sees through them)  (R29)
         |…| ≤ … → two inequalities, 2 ^ (n + 1) → 2 ^ n * 2,
         w / (p * 2) → w / p / 2, (b - a) / 2 ^ n → hi n - lo n              R36, R6, R7, rw [← hw]
         split the ∧ and finish both sides                                  constructor, R8
-/
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
    and `lo m ≤ hi n` for all `m, n` (compare both with the index `max m n`). So `r := ⨆ n, lo n` is a
    true supremum (`lo` is bounded by `b`) and is squeezed: `lo n ≤ r ≤ hi n`.
H2. `lo n → r` (monotone convergence, R27), and `hi n = lo n + (b - a) / 2ⁿ → r + 0` (R28, R30). By
    continuity `f (lo n) → f r` and `f (hi n) → f r` (R31, R32); the signs `f (lo n) ≤ 0 ≤ f (hi n)` pass to
    the limit (R33, R34), so `f r = 0` (R35). `a ≤ r ≤ b` is the squeeze at index 0; the midpoint bound is
    the squeeze at index `n` with the width `(b - a) / 2ⁿ = 2 · (b - a) / 2ⁿ⁺¹`.
H3. `set r := ⨆ n, lo n`;  `le_ciSup hbdd n`;  `ciSup_le fun m => lo_le_hi f a b hab ha hb m n`;
    `le_of_tendsto' ((hf.tendsto r).comp tlo) (fun n => (bisect_invariant f a b ha hb n).1)`; for the
    midpoint: `rw [abs_le, pow_succ, ← div_div, ← hw]; constructor <;> linarith`. For `gap_tendsto`:
    `simp_rw [div_eq_mul_inv, ← inv_pow]` then `(tendsto_pow_atTop_nhds_zero_of_lt_one _ _).const_mul (b - a)`.
-/
