/- E070 | Products and Fin sums | 2-3 min | Finset.prod, prod_range_succ, prod_const, Fin.sum_univ_succ, Fin.sum_univ_three, mathlib
GOAL
  Products `∏ i ∈ range n, f i` (= f 0 * … * f (n-1)) work like E042's sums. For `g : Fin n → M`,
  `∑ i, g i` sums over every `i : Fin n` (the finset `Finset.univ`).
BANNED: exact?, aesop

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E070

/- SKELETON · prod_four
  1. A closed product of naturals over a numeral range: Lean computes both sides:        R1
-/
-- BEGIN SPEC
open Finset

theorem prod_four : ∏ i ∈ range 4, (i + 1) = 24 :=
-- END SPEC
  by decide

/- SKELETON · prod_peel
  1. Peel the last factor `n + 1` off the left side (it lands on the right):              R2
  2. Swap the two factors of that product; `rw` then closes the goal by `rfl`:            R3
-/
-- BEGIN SPEC
theorem prod_peel (n : ℕ) : ∏ i ∈ range (n + 1), (i + 1) = (n + 1) * ∏ i ∈ range n, (i + 1) :=
-- END SPEC
  by rw [prod_range_succ, mul_comm]

/- SKELETON · prod_const_two
  1. Product of a constant → power with exponent `#(range n)`:                            R4
  2. Count the elements of `range n`; `rw` then closes the goal by `rfl`:                 R5
-/
-- BEGIN SPEC
theorem prod_const_two (n : ℕ) : ∏ _i ∈ range n, (2 : ℕ) = 2 ^ n :=
-- END SPEC
  by rw [prod_const, card_range]

/- SKELETON · sum_fin_three
  1. The statement is exactly the library lemma for `Fin 3`, applied to `g`:              R6
     (as a term, or with `rw`, which then closes the goal by `rfl`)
-/
-- BEGIN SPEC
theorem sum_fin_three (g : Fin 3 → ℝ) : ∑ i, g i = g 0 + g 1 + g 2 :=
-- END SPEC
  Fin.sum_univ_three g

/- SKELETON · sum_fin_succ
  1. Peel the `0` term off the sum over `Fin (n + 1)`:                                    R7
     left side becomes `g ↑0 + ∑ i, g ↑i.succ`
  2. Rewrite the indices, `↑0` → `0` and `↑i.succ` → `↑i + 1` (under the `∑`, so with
     `simp`, not `rw`); `simp` then closes the goal:                                      R9, R8
-/
-- BEGIN SPEC
theorem sum_fin_succ (g : ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin (n + 1), g i = g 0 + ∑ i : Fin n, g ((i : ℕ) + 1) :=
-- END SPEC
  by
    rw [Fin.sum_univ_succ]
    simp

end E070

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Products peel like E042's sums (`prod_range_succ` is `sum_range_succ` with `*`); a product of a constant
    is a power; sums over a whole `Fin n` have their own `Fin.sum_univ_*` lemmas. Concrete products in `ℕ`
    are computed.
H2. `prod_four`: compute. `prod_peel`: peel the last factor, then swap the two factors. `prod_const_two`:
    constant product → `2 ^ #(range n)`, then count. `sum_fin_three`: the `Fin 3` lemma. `sum_fin_succ`:
    peel the `0` term with `Fin.sum_univ_succ`; what is left differs only by `↑0` vs `0` and `↑i.succ` vs
    `↑i + 1`, which `simp` fixes (`Fin.val_succ`).
H3. `decide`; `rw [prod_range_succ, mul_comm]`; `rw [prod_const, card_range]`; `Fin.sum_univ_three g`;
    `rw [Fin.sum_univ_succ]` and then `simp`.
-/
