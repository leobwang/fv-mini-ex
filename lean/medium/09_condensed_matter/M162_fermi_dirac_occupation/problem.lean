/- M162 | Fermi–Dirac occupation | 15 min | Fermi function, bounds, Antitone, Tendsto, field_simp, mathlib
GOAL
  The Fermi function `f(ε) = 1 / (exp (β (ε - μ)) + 1)` (level energy `ε`, inverse temperature `β`,
  chemical potential `μ`) lies strictly between 0 and 1, obeys particle–hole symmetry
  `f(μ + x) + f(μ - x) = 1`, decreases in `ε` when `β ≥ 0`, and tends to 1 below `μ` as `β → ∞` (T → 0).

REFERENCE
  #check Real.exp_pos   -- 0 < exp x
  #check Real.exp_neg   -- exp (-x) = (exp x)⁻¹
  #check div_lt_one     -- 0 < b → (a / b < 1 ↔ a < b)
  example (x y : ℝ) (h : x ≤ y) : 1 / (Real.exp y + 1) ≤ 1 / (Real.exp x + 1) := by gcongr
  #check Filter.Tendsto.atTop_mul_neg  -- C < 0 → f → ∞ → g → C → f * g → -∞ (atBot)
  #check Real.tendsto_exp_atBot        -- exp x → 0 as x → -∞
  #check Filter.Tendsto.add_const      -- f → a ⊢ f + b → a + b
  #check Filter.Tendsto.div            -- f → a → g → b → b ≠ 0 → f / g → a / b
  `Antitone f` means `∀ a b, a ≤ b → f b ≤ f a`; `Tendsto f atTop (𝓝 L)` is "f β → L as β → ∞".
  `field_simp` clears denominators it can prove nonzero (give it `exp _ + 1 ≠ 0`-style facts).
-/
import Mathlib

open Real Filter Topology

namespace M162

-- BEGIN SPEC
/-- Fermi–Dirac occupation of a level of energy `ε` at inverse temperature `β` and chemical
potential `μ`. -/
noncomputable def fermi (β μ ε : ℝ) : ℝ := 1 / (Real.exp (β * (ε - μ)) + 1)
-- END SPEC

-- BEGIN SPEC
theorem fermi_bounds (β μ ε : ℝ) : 0 < fermi β μ ε ∧ fermi β μ ε < 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem particle_hole (β μ x : ℝ) : fermi β μ (μ + x) + fermi β μ (μ - x) = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fermi_antitone (β μ : ℝ) (hβ : 0 ≤ β) : Antitone (fermi β μ) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fermi_zero_T (μ ε : ℝ) (h : ε < μ) : Tendsto (fun β => fermi β μ ε) atTop (𝓝 1) :=
-- END SPEC
  sorry

end M162

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start each part with `unfold fermi`. Positivity of `exp` drives the bounds; `exp (-y) = 1 / exp y`
    drives the symmetry.
H2. Symmetry: rewrite `exp (β * (μ - x - μ))` as `(exp (β * (μ + x - μ)))⁻¹`, then clear
    denominators. Limit: the exponent `β * (ε - μ)` goes to `-∞`, so `exp` of it goes to 0 and
    `1 / (exp _ + 1) → 1 / (0 + 1)`.
H3. Limit: `have h1 : Tendsto (fun β : ℝ => β * (ε - μ)) atTop atBot`, then build the limit of
    `exp ∘ _`, of `_ + 1` and of `1 / _` with `Real.tendsto_exp_atBot.comp h1`, `.add_const 1` and
    `tendsto_const_nhds.div _ (by norm_num)`. Antitone: compare the two exponents first.
-/
