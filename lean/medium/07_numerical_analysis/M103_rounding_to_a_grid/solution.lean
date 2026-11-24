/- M103 | Rounding to a grid | 15-20 min | round, zpow, relative error, floating point, field_simp, mathlib
GOAL
  Rounding `x` to the nearest point of the grid `h ℤ = {…, -h, 0, h, 2h, …}` has absolute error `≤ h/2`.
  Floats with `p` fraction bits in the binade `[2^e, 2^(e+1))` lie on the grid of spacing `2^(e-p)`;
  rounding any `x ≥ 2^e` to that grid gives `x (1 + δ)` with `|δ| ≤ u = 2^(-p-1)` (the unit roundoff).

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M103

-- BEGIN SPEC
-- nearest point of the grid h ℤ (ties go up, like `round`)
noncomputable def roundTo (h x : ℝ) : ℝ := h * round (x / h)
-- END SPEC

/- SKELETON · roundTo_error
  1. The error is `h` times the error of rounding `x / h`. Prove it first:
       e : roundTo h x - x = -(h * (x / h - round (x / h)))
       proof: unfold the definition, clear `x / h` (it uses `hh`), then ring    R1 → R2 → ring
  2. rw [e], then take the absolute value apart:                              R3 → R4 → R5 (with hh)
       goal is now  h * |x / h - ↑(round (x / h))| ≤ h / 2
  3. Close with the rounding bound for `x / h` as a hint (a product of
     `0 < h` and `|…| ≤ 1/2` is needed, so not plain linarith):              R6 inside R7
-/
-- BEGIN SPEC
theorem roundTo_error (h x : ℝ) (hh : 0 < h) : |roundTo h x - x| ≤ h / 2 :=
-- END SPEC
  by
    have e : roundTo h x - x = -(h * (x / h - round (x / h))) := by
      unfold roundTo; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos hh]
    nlinarith [abs_sub_round (x / h)]

/- SKELETON · binade_relative_error
  1. `hx0 : 0 < x` FIRST (step 2's equation and step 4 divide by `x`):      R8 with R9 for `0 < 2 ^ e`
  2. Witness δ := (roundTo (2 ^ (e - p)) x - x) / x, the relative error:     R10
       the equation is the SECOND goal; prove it in place of its `?_` with a
       `by …` block (clear `/ x`, then ring), so only the bound remains:      R2, ring
  3. Part 1 at the grid spacing `2 ^ (e - p)`; its `0 < _` argument:          R11 with R9
       herr : |roundTo (2 ^ (e - ↑p)) x - x| ≤ 2 ^ (e - ↑p) / 2
  4. Clear the quotient:                                                      R12 → R5 (with hx0) → R13
       goal is now  |roundTo (2 ^ (e - ↑p)) x - x| ≤ 2 ^ (-↑p - 1) * x
  5. Prove the exponent fact (half a grid step = u · 2^e):
       key : (2 : ℝ) ^ (e - p) / 2 = 2 ^ (-(p : ℤ) - 1) * 2 ^ e
       proof: reshape `e - p` as `(-p - 1 + e) + 1`, split twice, drop `^ 1`, ring
                                                                              R14 → R15 (R16) → R15 → R17 → ring
  6. Chain  |…| ≤ 2^(e-p)/2 = 2^(-p-1) * 2^e ≤ 2^(-p-1) * x:                 R18 with herr, key, R19
-/
-- BEGIN SPEC
theorem binade_relative_error (p : ℕ) (e : ℤ) (x : ℝ) (hx : 2 ^ e ≤ x) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-(p : ℤ) - 1) ∧ roundTo (2 ^ (e - p)) x = x * (1 + δ) :=
-- END SPEC
  by
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    refine ⟨(roundTo (2 ^ (e - p)) x - x) / x, ?_, by field_simp; ring⟩
    have herr := roundTo_error (2 ^ (e - p)) x (by positivity)
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have key : (2 : ℝ) ^ (e - p) / 2 = 2 ^ (-(p : ℤ) - 1) * 2 ^ e := by
      rw [show e - (p : ℤ) = (-(p : ℤ) - 1 + e) + 1 by ring, zpow_add₀ two_ne_zero,
        zpow_add₀ two_ne_zero, zpow_one]
      ring
    calc _ ≤ (2 : ℝ) ^ (e - p) / 2 := herr
      _ = 2 ^ (-(p : ℤ) - 1) * 2 ^ e := key
      _ ≤ 2 ^ (-(p : ℤ) - 1) * x := by gcongr

end M103

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `roundTo h x - x = -(h * (x/h - round (x/h)))`: the error is `h` times the error of rounding `x/h`,
    which `abs_sub_round` bounds by `1/2`. For the binade, the witness is the relative error itself,
    `δ := (roundTo h x - x) / x` with `h = 2 ^ (e - p)`, and Part 1 bounds its numerator.
H2. Part 1: prove the identity with `unfold roundTo; field_simp; ring`, rewrite with it, strip the
    absolute values with `abs_neg`, `abs_mul`, `abs_of_pos hh`, and finish with `nlinarith` given the
    rounding bound as a hint. Part 2: get `0 < x` first; after `refine ⟨δ, ?_, ?_⟩` the equation is
    `field_simp; ring`; for the bound, `|δ| = |err| / x ≤ (h / 2) / x` and `h / 2 = 2^(-p-1) * 2^e ≤ 2^(-p-1) * x`.
H3. Part 1 ends with `nlinarith [abs_sub_round (x / h)]`. Part 2: `have hx0 : 0 < x := lt_of_lt_of_le
    (by positivity) hx`; `rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]`; the key fact
    `(2:ℝ) ^ (e - p) / 2 = 2 ^ (-(p:ℤ) - 1) * 2 ^ e` comes from
    `rw [show e - (p : ℤ) = (-(p : ℤ) - 1 + e) + 1 by ring, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one]; ring`;
    close with `calc _ ≤ (2 : ℝ) ^ (e - p) / 2 := herr` / `_ = … := key` / `_ ≤ … := by gcongr`.
-/
