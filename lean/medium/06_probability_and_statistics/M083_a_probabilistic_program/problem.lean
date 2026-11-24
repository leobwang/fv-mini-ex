/- M083 | A probabilistic program | 10-15 min | PMF, monad, do-notation, tsum_bool, ENNReal arithmetic, mathlib
GOAL
  `twoFlips` flips two fair coins with the `PMF` monad and returns `a || b` (at least one `true`).
  Prove that it returns `true` with probability `3 / 4`.

REFERENCE
  `PMF α` is a probability mass function on `α`; `p a : ℝ≥0∞` is the probability of outcome `a`.
  `do let a ← p; …` is `p.bind fun a => …`, and `return x` is `PMF.pure x`.
  #check PMF.bind_apply                -- (p.bind f) b = ∑' a, p a * (f a) b
  #check PMF.pure_apply                -- (PMF.pure a) a' = if a' = a then 1 else 0
  #check tsum_bool                     -- ∑' i : Bool, f i = f false + f true
  #check PMF.uniformOfFintype_apply    -- (PMF.uniformOfFintype α) a = (↑(Fintype.card α))⁻¹
  #check ENNReal.inv_two_add_inv_two   -- 2⁻¹ + 2⁻¹ = 1
  #check ENNReal.toReal_eq_toReal_iff' -- a ≠ ∞ → b ≠ ∞ → (a.toReal = b.toReal ↔ a = b)
  #check ENNReal.toReal_add            -- a ≠ ∞ → b ≠ ∞ → (a + b).toReal = a.toReal + b.toReal
  `finiteness` proves side goals `x ≠ ∞`; `show <explicit binds> true = 3 / 4` unfolds the `do` block.
NOTE: `norm_num` cannot evaluate `2⁻¹ * 2⁻¹ + 2⁻¹ = 3 / 4` in `ℝ≥0∞`; move the equation to `ℝ` first.
-/
import Mathlib

namespace M083

-- BEGIN SPEC
noncomputable def coin : PMF Bool := PMF.uniformOfFintype Bool

noncomputable def twoFlips : PMF Bool := do
  let a ← coin
  let b ← coin
  return (a || b)

theorem twoFlips_true : twoFlips true = 3 / 4 :=
-- END SPEC
  sorry

end M083

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Make the binds explicit with `show (coin.bind fun a => coin.bind fun b => PMF.pure (a || b)) true = 3 / 4`.
H2. Expand each `bind` into a sum over `Bool`, evaluate `coin` and `pure`, and let `simp` clean the
    `if`s. You are left with a numeral identity in `ℝ≥0∞`.
H3. `simp only [PMF.bind_apply, tsum_bool, PMF.pure_apply, coin, PMF.uniformOfFintype_apply, Fintype.card_bool]`
    then `simp` leaves `2⁻¹ * 2⁻¹ + 2⁻¹ * (2⁻¹ + 2⁻¹) = 3 / 4` in `ℝ≥0∞`; move it to `ℝ` with
    `ENNReal.toReal_eq_toReal_iff'` and finish there.
-/
