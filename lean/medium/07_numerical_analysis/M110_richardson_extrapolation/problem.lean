/- M110 | Richardson extrapolation | 15-20 min | error expansion, abs, powers, set, gcongr, mathlib
GOAL
  `D t` approximates an exact value `A` with step `t`, with known leading error `c tᵖ` and a remainder
  bounded by `K t^q`. Show that the combination `(2ᵖ D(h/2) - D(h)) / (2ᵖ - 1)` cancels the `c tᵖ`
  term: its error is `O(h^q)`, with the explicit constant below (`c` does not appear in it).

REFERENCE
  #check one_lt_pow₀   -- 1 < a → n ≠ 0 → 1 < a ^ n
  #check div_pow       -- (a / b) ^ n = a ^ n / b ^ n
  #check abs_sub       -- |a - b| ≤ |a| + |b|
  #check abs_div       -- |a / b| = |a| / |b|        (also `abs_mul`, `abs_of_pos : 0 < a → |a| = a`)
  #check div_le_iff₀   -- 0 < c → (b / c ≤ a ↔ b ≤ a * c)
  example (D : ℝ → ℝ) (A h : ℝ) : D h - A = D h - A := by set u := D h - A with hu; rfl  -- name a subterm (`hu : u = D h - A`)
  `gcongr` proves `f a ≤ f b` from `a ≤ b` for monotone shapes (sums, products by nonnegatives, …).
  `field_simp` then `ring` proves identities with denominators once their nonvanishing is in context.
-/
import Mathlib

namespace M110

-- BEGIN SPEC
theorem richardson (p q : ℕ) (A c K h : ℝ) (D : ℝ → ℝ) (hp : 1 ≤ p) (hh : 0 < h)
    (hD : ∀ t, 0 < t → |D t - (A + c * t ^ p)| ≤ K * t ^ q) :
    |(2 ^ p * D (h / 2) - D h) / (2 ^ p - 1) - A| ≤ (2 ^ p / 2 ^ q + 1) / (2 ^ p - 1) * K * h ^ q :=
-- END SPEC
  sorry

end M110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Name the two remainders `u := D (h/2) - (A + c (h/2)ᵖ)` and `w := D h - (A + c hᵖ)`; `hD` bounds each.
H2. Key identity: the extrapolated error equals `(2ᵖ u - w) / (2ᵖ - 1)`, because `2ᵖ (h/2)ᵖ = hᵖ` kills
    the `c` terms. Then `|2ᵖ u - w| ≤ 2ᵖ |u| + |w|` and plug in the two bounds.
H3. After `set u := … with hu` and `set w := … with hw`: `have key : (2 ^ p * D (h / 2) - D h) / (2 ^ p - 1) - A =
    (2 ^ p * u - w) / (2 ^ p - 1) := by rw [hu, hw, div_pow]; field_simp; ring`, then `rw [key, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]`
    with `hpos : 0 < 2 ^ p - 1` from `one_lt_pow₀`.
-/
