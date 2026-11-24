/- M162 | Fermi–Dirac occupation | 15 min | Fermi function, bounds, Antitone, Tendsto, field_simp, mathlib
GOAL
  The Fermi function `f(ε) = 1 / (exp (β (ε - μ)) + 1)` (level energy `ε`, inverse temperature `β`,
  chemical potential `μ`) lies strictly between 0 and 1, obeys particle–hole symmetry
  `f(μ + x) + f(μ - x) = 1`, decreases in `ε` when `β ≥ 0`, and tends to 1 below `μ` as `β → ∞` (T → 0).

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Real Filter Topology

namespace M162

-- BEGIN SPEC
/-- Fermi–Dirac occupation of a level of energy `ε` at inverse temperature `β` and chemical
potential `μ`. -/
noncomputable def fermi (β μ ε : ℝ) : ℝ := 1 / (Real.exp (β * (ε - μ)) + 1)
-- END SPEC

/- SKELETON · fermi_bounds
  1. Unfold the definition:                                          R1
  2. Record that the exponential is positive, with the exponent
     exactly as it appears in the goal:
       this : 0 < rexp (β * (ε - μ))                                 R2
  3. Split the `∧`:                                                  refine ⟨?_, ?_⟩
  4. Left goal `0 < 1 / (rexp _ + 1)`:                               R3
  5. Right goal `1 / (rexp _ + 1) < 1` → `1 < rexp _ + 1`
     (side goal `0 < rexp _ + 1` by R3), then finish from `this`:    R4, R5
-/
-- BEGIN SPEC
theorem fermi_bounds (β μ ε : ℝ) : 0 < fermi β μ ε ∧ fermi β μ ε < 1 :=
-- END SPEC
  sorry

/- SKELETON · particle_hole
  1. Unfold the definition:                                          R1
  2. Prove first, with `have`:
       h : rexp (β * (μ - x - μ)) = (rexp (β * (μ + x - μ)))⁻¹
     proof: inverse → exp of a negation, then ring arithmetic
     inside `rexp`:                                                  R6 (right to left) → R7
  3. Substitute it:                                                  rw [h]
  4. Clear the denominators, then finish the polynomial identity:    R8 → R9
-/
-- BEGIN SPEC
theorem particle_hole (β μ x : ℝ) : fermi β μ (μ + x) + fermi β μ (μ - x) = 1 :=
-- END SPEC
  sorry

/- SKELETON · fermi_antitone
  1. Open `Antitone` (keep `hβ` in the context):                     R10
  2. Unfold the definition:                                          R1
  3. Compare the two same-shape sides; the step through `β * _`
     needs `0 ≤ β`, which `gcongr` takes from `hβ`:                   R11 (R12)
-/
-- BEGIN SPEC
theorem fermi_antitone (β μ : ℝ) (hβ : 0 ≤ β) : Antitone (fermi β μ) :=
-- END SPEC
  sorry

/- SKELETON · fermi_zero_T
  Build the limit as `have` facts, inside out, then close with step 5.
  1. h1 : Tendsto (fun β : ℝ => β * (ε - μ)) atTop atBot
       R15 applied to R13 (β → ∞) and R14 (ε - μ is constant);
       its `ε - μ < 0` argument from `h`:                            R13, R14 → R15, R5
  2. h2 : `rexp (β * (ε - μ)) + 1 → 0 + 1`:                          R16 → R17 (with h1) → R18
  3. h3 : `1 / (rexp _ + 1) → 1 / (0 + 1)`; the constant 1 is R14
     written with `(x := (1 : ℝ))`, `0 + 1 ≠ 0` by `norm_num`:       R14 → R19
  4. Clean `∘`, `0 + 1`, `1 / 1` in h3:                              R20, R21 (at h3)
  5. h3 is the goal once `fermi` unfolds:                            R22
-/
-- BEGIN SPEC
theorem fermi_zero_T (μ ε : ℝ) (h : ε < μ) : Tendsto (fun β => fermi β μ ε) atTop (𝓝 1) :=
-- END SPEC
  sorry

end M162

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start each part with `unfold fermi` (in `fermi_antitone`, after `intro a b hab`). `0 < rexp y` (R2)
    drives the bounds, `rexp (-y) = (rexp y)⁻¹` (R6) drives the symmetry, `gcongr` (R11) does the
    monotonicity, and the limit is built from `Tendsto` lemmas (R13–R19).
H2. Bounds: `refine ⟨?_, ?_⟩`, then `positivity`, and `rw [div_lt_one (by positivity)]` + `linarith`.
    Symmetry: rewrite `rexp (β * (μ - x - μ))` as `(rexp (β * (μ + x - μ)))⁻¹`, then `field_simp; ring`.
    Limit: the exponent `β * (ε - μ)` goes to `-∞`, so `rexp` of it goes to 0 and
    `1 / (rexp _ + 1) → 1 / (0 + 1)`.
H3. Symmetry's fact: `rw [← Real.exp_neg]; ring_nf`. Limit:
    `have h1 : Tendsto (fun β : ℝ => β * (ε - μ)) atTop atBot := tendsto_id.atTop_mul_neg (by linarith) tendsto_const_nhds`,
    then `have h2 := (Real.tendsto_exp_atBot.comp h1).add_const 1`,
    `have h3 := (tendsto_const_nhds (x := (1 : ℝ))).div h2 (by norm_num)`,
    `simp only [Function.comp_def, zero_add, div_one] at h3`.
-/
