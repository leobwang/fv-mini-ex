/- E037 | positivity | 1-2 min | positivity, mathlib
GOAL
  Prove goals of the form `0 < e` or `0 ≤ e` by the syntactic structure of `e`.

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

/- SKELETON · sq_add_one_pos
  1. Read the tree of `x ^ 2 + 1`: an even power (`≥ 0` for every `x`) plus a
     positive numeral, so the sum is `> 0`. Close in one step:              R1
-/
-- BEGIN SPEC
theorem sq_add_one_pos (x : ℝ) : 0 < x ^ 2 + 1 :=
-- END SPEC
  by positivity

/- SKELETON · prod_pos
  1. `a` and `b` are real variables: their signs come only from `ha`, `hb`.
     `b + 1` is `≥ 0` plus `> 0`; the product of two `> 0` factors is `> 0`.
     Close in one step (keep `ha`, `hb` in the context):                     R2
-/
-- BEGIN SPEC
theorem prod_pos (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a * (b + 1) :=
-- END SPEC
  by positivity

/- SKELETON · exp_abs_pos
  1. `Real.exp x > 0` for every `x` (R3) and `|x| ≥ 0` (R4): a `> 0` term plus
     a `≥ 0` term. No hypothesis is needed. Close in one step:              R3, R4
-/
-- BEGIN SPEC
theorem exp_abs_pos (x : ℝ) : 0 < Real.exp x + |x| :=
-- END SPEC
  by positivity

/- SKELETON · nat_pow_pos
  1. In `ℕ`, `2 ^ n > 0` (positive base, any exponent) and `n ≥ 0` for free.
     Close in one step:                                                     R5
-/
-- BEGIN SPEC
theorem nat_pow_pos (n : ℕ) : 0 < 2 ^ n + n :=
-- END SPEC
  by positivity

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal is `0 < e` with `e` built from pieces whose sign is known: squares, numerals,
    `Real.exp`, `|·|`, powers of a positive base, and variables bounded by hypotheses.
H2. One tactic reads the tree of `e` bottom up and proves the sign of each node from its children
    (R1–R5): `≥ 0` plus `> 0` is `> 0`, `> 0` times `> 0` is `> 0`. Real variables need a hypothesis
    in the context; `ℕ` variables are `≥ 0` for free.
H3. Each proof is `positivity`.
-/
