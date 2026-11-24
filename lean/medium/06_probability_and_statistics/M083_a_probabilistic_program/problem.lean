/- M083 | A probabilistic program | 10-15 min | PMF, monad, do-notation, tsum_bool, ENNReal arithmetic, mathlib
GOAL
  `twoFlips` flips two fair coins with the `PMF` monad and returns `a || b` (at least one `true`).
  Prove that it returns `true` with probability `3 / 4`.

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M083

/- SKELETON · twoFlips_true
  1. Unfold `twoFlips` and its `do` block into explicit binds
     (outer `let a ← coin` = outer `bind`):                                  R1
  2. Expand every `bind`, `∑'` over `Bool`, `pure` and coin in ONE
     `simp only [...]` (add the name `coin` to the list):                    R2, R3, R4, coin, R5, R6
  3. Evaluate the `if`s and the casts `↑2`; `simp` leaves, in `ℝ≥0∞`,
       ⊢ 2⁻¹ * 2⁻¹ + 2⁻¹ * (2⁻¹ + 2⁻¹) = 3 / 4                               R7, R8
  4. Collapse the inner `2⁻¹ + 2⁻¹`:                                          R9 → R10
  5. `norm_num` cannot finish in `ℝ≥0∞`: move the equation to `ℝ`,
     closing both side goals on the spot:                                    R11 (R12, R12)
  6. Split `toReal` over the outer `+`, side goals again:                    R13 (R12, R12)
  7. Push `toReal` through `*`, `⁻¹`, `/` and the numerals:                   R14–R17
  8. Finish the numeral identity in `ℝ`:                                      R18
-/
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
H1. Nothing computes until `twoFlips` is unfolded. Make the binds explicit with
    `show (coin.bind fun a => coin.bind fun b => PMF.pure (a || b)) true = 3 / 4` (R1).
H2. Expand with `PMF.bind_apply`, `tsum_bool`, `PMF.pure_apply`, `coin`, `PMF.uniformOfFintype_apply`,
    `Fintype.card_bool` in one `simp only` (R2–R6), then `simp` (R7, R8). That leaves
    `2⁻¹ * 2⁻¹ + 2⁻¹ * (2⁻¹ + 2⁻¹) = 3 / 4` in `ℝ≥0∞`, which `norm_num` cannot evaluate: move it to `ℝ`.
H3. After `rw [ENNReal.inv_two_add_inv_two, mul_one]` (R9, R10), the key line is
    `rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]` (R11, R12); then
    `ENNReal.toReal_add` (R13) and `simp [ENNReal.toReal_div]` (R14–R17) leave a real identity for `norm_num`.
-/
