/- H038 | Division with remainder in ℤ[i] | 1-1.5 h | GaussianInt, Zsqrtd.norm, rounding, nlinarith, mathlib
GOAL
  The Gaussian integers `ℤ[i] = {s + t·i | s t : ℤ}` have division with remainder for the norm
  `N(s + t·i) = s² + t²`: if `b ≠ 0` then `a = b * q + r` with `N r < N b`. Build `q` by rounding.
  (`GaussianInt` is `ℤ√(-1)`, Mathlib's `Zsqrtd (-1)`: a structure with integer fields `.re`, `.im`.)

REFERENCE
  example : GaussianInt := ⟨3, 4⟩   -- 3 + 4i (anonymous constructor ⟨re, im⟩)
  #check Zsqrtd.norm_def            -- n.norm = n.re * n.re - d * n.im * n.im   (here d = -1)
  #check Zsqrtd.norm_mul            -- (n * m).norm = n.norm * m.norm
  #check Zsqrtd.norm_conj           -- (star x).norm = x.norm   (`star x` is the conjugate re - im·i)
  #check Zsqrtd.norm_eq_mul_conj    -- ((n.norm : ℤ) : ℤ√d) = n * star n
  #check GaussianInt.norm_pos       -- 0 < x.norm ↔ x ≠ 0
  #check Int.emod_add_mul_ediv      -- a % b + b * (a / b) = a
  #check Int.emod_nonneg            -- b ≠ 0 → 0 ≤ a % b    (and `Int.emod_lt_of_pos : 0 < b → a % b < b`)
  #check sq_abs                     -- |a| ^ 2 = a ^ 2
  -- `ring` works in `GaussianInt`; `simp` knows `Zsqrtd.re_mul`, `Zsqrtd.re_star`, `Zsqrtd.re_sub`, ...
BANNED: GaussianInt.norm_mod_lt, GaussianInt.natAbs_norm_mod_lt, GaussianInt.mod_def, GaussianInt.div_def, GaussianInt.normSq_div_sub_div_lt_one, GaussianInt.norm_le_norm_mul_left, EuclideanDomain.div_add_mod, EuclideanDomain.mod_add_div, EuclideanDomain.mod_add_div', EuclideanDomain.div_add_mod', EuclideanDomain.remainder_lt, EuclideanDomain.mod_lt, exact?, apply?, try?, hint
NOTE: `GaussianInt` already has `/` and `%`, but their lemmas are banned: construct `q` yourself.
-/
import Mathlib

namespace H038

-- MILESTONE (optional: change or delete)
/-- Every integer `u` is within `n / 2` of a multiple of `n`. -/
theorem round_int (n u : ℤ) (hn : 0 < n) : ∃ s : ℤ, 2 * |u - n * s| ≤ n := by
  sorry

-- MILESTONE (optional: change or delete)
theorem mul_conj_sub (a b q : GaussianInt) :
    (a - b * q) * star b = a * star b - (b.norm : GaussianInt) * q := by
  sorry

-- MILESTONE (optional: change or delete)
theorem norm_mul_norm (a b : GaussianInt) (s t : ℤ) :
    (a - b * ⟨s, t⟩).norm * b.norm
      = ((a * star b).re - b.norm * s) ^ 2 + ((a * star b).im - b.norm * t) ^ 2 := by
  sorry

-- BEGIN SPEC
theorem div_mod (a b : GaussianInt) (hb : b ≠ 0) :
    ∃ q r : GaussianInt, a = b * q + r ∧ r.norm < b.norm :=
-- END SPEC
  sorry

end H038

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Over ℂ you would take `q ≈ a / b = a·b̄ / N(b)`. Stay in ℤ: round each coordinate of `w = a * star b` to the nearest multiple of `N = b.norm`, i.e. `w.re ≈ N * s`, `w.im ≈ N * t`, and set `q = ⟨s, t⟩`, `r = a - b * q`.
H2. Then `r * star b = w - N * q`, so `N(r) * N = (w.re - N s)² + (w.im - N t)²`, and each square is at most `N² / 4`. Rounding: take `s = u / n` if `2 * (u % n) ≤ n`, else `u / n + 1`.
H3. `norm_mul_norm`: `rw [← Zsqrtd.norm_conj b, ← Zsqrtd.norm_mul, mul_conj_sub, Zsqrtd.norm_def]; simp; ring` (and `mul_conj_sub` is `rw [Zsqrtd.norm_eq_mul_conj]; ring`). Finish with `4 * sq ≤ N ^ 2` from `sq_abs` + `nlinarith`, then `by_contra` and `nlinarith`.
-/
