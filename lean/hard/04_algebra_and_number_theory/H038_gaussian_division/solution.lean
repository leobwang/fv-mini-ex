/- H038 | Division with remainder in ℤ[i] | 1-1.5 h | GaussianInt, Zsqrtd.norm, rounding, nlinarith, mathlib
GOAL
  The Gaussian integers `ℤ[i] = {s + t·i | s t : ℤ}` have division with remainder for the norm
  `N(s + t·i) = s² + t²`: if `b ≠ 0` then `a = b * q + r` with `N r < N b`. Build `q` by rounding.
  (`GaussianInt` is `ℤ√(-1)`, Mathlib's `Zsqrtd (-1)`: a structure with integer fields `.re`, `.im`.)

BANNED: GaussianInt.norm_mod_lt, GaussianInt.natAbs_norm_mod_lt, GaussianInt.mod_def, GaussianInt.div_def, GaussianInt.normSq_div_sub_div_lt_one, GaussianInt.norm_le_norm_mul_left, EuclideanDomain.div_add_mod, EuclideanDomain.mod_add_div, EuclideanDomain.mod_add_div', EuclideanDomain.div_add_mod', EuclideanDomain.remainder_lt, EuclideanDomain.mod_lt, exact?, apply?, try?, hint

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H038

/- SKELETON · round_int   (MILESTONE: prove it first; used twice in div_mod, step 2)
  1. Put the three facts about `u % n` and `u / n` in the context:                    R1, R2, R3
  2. Split on whether the remainder is at most half of `n`: `h : 2 * (u % n) ≤ n`:     R4
  3. case pos: witness `u / n` (`refine ⟨_, ?_⟩`); rewrite `u - n * (u / n)` to `u % n`,
     drop `|·|` with `h1`, close with `h`:                                            R6 (R5 inside) → R7
  4. case neg: witness `u / n + 1`; flip `h`; rewrite `u - n * (u / n + 1)` to `u % n - n`,
     drop `|·|` (the remainder minus `n` is negative), close:                         R8 → R6 → R9 → R5
-/
-- MILESTONE (optional: change or delete)
/-- Every integer `u` is within `n / 2` of a multiple of `n`. -/
theorem round_int (n u : ℤ) (hn : 0 < n) : ∃ s : ℤ, 2 * |u - n * s| ≤ n := by
  have h1 := Int.emod_nonneg u hn.ne'
  have h2 := Int.emod_lt_of_pos u hn
  have h3 := Int.emod_add_mul_ediv u n
  by_cases h : 2 * (u % n) ≤ n
  · refine ⟨u / n, ?_⟩
    rw [show u - n * (u / n) = u % n by linarith, abs_of_nonneg h1]
    exact h
  · refine ⟨u / n + 1, ?_⟩
    push Not at h
    rw [show u - n * (u / n + 1) = u % n - n by linarith, abs_of_neg (by linarith)]
    linarith

/- SKELETON · mul_conj_sub   (MILESTONE: used by norm_mul_norm, step 3)
  1. Replace the cast norm `↑b.norm` by `b * star b`:                                  R10
  2. Now a ring identity in `ℤ√(-1)`:                                                   R11
-/
-- MILESTONE (optional: change or delete)
theorem mul_conj_sub (a b q : GaussianInt) :
    (a - b * q) * star b = a * star b - (b.norm : GaussianInt) * q := by
  rw [Zsqrtd.norm_eq_mul_conj]
  ring

/- SKELETON · norm_mul_norm   (MILESTONE: prove after mul_conj_sub; it is `key` in div_mod, step 4)
  1. Write `b.norm` as `(star b).norm` so the left side is a product of two norms:      R12
  2. Merge it into one norm `((a - b * ⟨s, t⟩) * star b).norm`:                         R13
  3. Rewrite the argument with the milestone: `rw [mul_conj_sub]`
  4. Expand the norm into coordinates, compute `.re` and `.im`:                         R14 → R15
  5. What is left is an integer identity (`u * u` versus `u ^ 2`):                      R11
-/
-- MILESTONE (optional: change or delete)
theorem norm_mul_norm (a b : GaussianInt) (s t : ℤ) :
    (a - b * ⟨s, t⟩).norm * b.norm
      = ((a * star b).re - b.norm * s) ^ 2 + ((a * star b).im - b.norm * t) ^ 2 := by
  rw [← Zsqrtd.norm_conj b, ← Zsqrtd.norm_mul, mul_conj_sub, Zsqrtd.norm_def]
  simp
  ring

/- SKELETON · div_mod
  Prove the MILESTONES first: round_int (step 2), mul_conj_sub (inside norm_mul_norm), norm_mul_norm (step 4).
  1. `hN : 0 < b.norm` from `hb`:                                                       R16
  2. Round the coordinates of `a * star b` to multiples of `b.norm`: `round_int` twice
     (`round_int b.norm (a * star b).re hN`, then with `.im`), unpacked into `s, hs` and `t, ht`:
                                                                                        R17, R17
  3. Witnesses `q := ⟨s, t⟩`, `r := a - b * ⟨s, t⟩`; the equation `a = b * q + r`:       R18 (R11 inside)
  4. `key := norm_mul_norm a b s t`
  5. From `hs`: `hs2 : 4 * ((a * star b).re - b.norm * s) ^ 2 ≤ b.norm ^ 2`, and `ht2` from `ht`:
     square the bound on `|·|`:                                                         R19, R20 → R21
  6. Assume the norm bound fails, flip the `¬<`, combine `key hs2 ht2 hN`:              R22 → R8 → R21
-/
-- BEGIN SPEC
theorem div_mod (a b : GaussianInt) (hb : b ≠ 0) :
    ∃ q r : GaussianInt, a = b * q + r ∧ r.norm < b.norm :=
-- END SPEC
  by
    have hN : 0 < b.norm := GaussianInt.norm_pos.mpr hb
    obtain ⟨s, hs⟩ := round_int b.norm (a * star b).re hN
    obtain ⟨t, ht⟩ := round_int b.norm (a * star b).im hN
    refine ⟨⟨s, t⟩, a - b * ⟨s, t⟩, by ring, ?_⟩
    have key := norm_mul_norm a b s t
    -- WHY: from `2|x| ≤ N` we get `4x² ≤ N²`; nlinarith needs `|x|² = x²` and `|x| ≥ 0` spelled out.
    have hs2 : 4 * ((a * star b).re - b.norm * s) ^ 2 ≤ b.norm ^ 2 := by
      nlinarith [sq_abs ((a * star b).re - b.norm * s), abs_nonneg ((a * star b).re - b.norm * s)]
    have ht2 : 4 * ((a * star b).im - b.norm * t) ^ 2 ≤ b.norm ^ 2 := by
      nlinarith [sq_abs ((a * star b).im - b.norm * t), abs_nonneg ((a * star b).im - b.norm * t)]
    by_contra hge
    push Not at hge
    nlinarith

end H038

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Over ℂ you would take `q ≈ a / b = a·b̄ / N(b)`. Stay in ℤ: with `N = b.norm` and `w = a * star b`,
    round each coordinate of `w` to a multiple of `N` (`round_int`: `w.re ≈ N * s`, `w.im ≈ N * t`), and set
    `q = ⟨s, t⟩`, `r = a - b * q`. Do not use `/` or `%` of `GaussianInt`: their lemmas are banned.
H2. Order: `round_int` (R1–R9: take `s = u / n` if `2 * (u % n) ≤ n`, else `u / n + 1`), `mul_conj_sub`
    (R10, R11: `r * star b = w - N * q`), `norm_mul_norm` (R12–R15, R11: `N(r) * N = (w.re - N s)² + (w.im - N t)²`).
    In `div_mod` each square is at most `N² / 4`, so `N(r) * N ≤ N² / 2`, which contradicts `N ≤ N(r)` and `0 < N`.
H3. `norm_mul_norm`: `rw [← Zsqrtd.norm_conj b, ← Zsqrtd.norm_mul, mul_conj_sub, Zsqrtd.norm_def]; simp; ring`.
    `div_mod`: `refine ⟨⟨s, t⟩, a - b * ⟨s, t⟩, by ring, ?_⟩`, then
    `have hs2 : 4 * ((a * star b).re - b.norm * s) ^ 2 ≤ b.norm ^ 2 := by nlinarith [sq_abs (…), abs_nonneg (…)]`
    with `…` the same difference, likewise `ht2`, and finish `by_contra hge; push Not at hge; nlinarith`.
-/
