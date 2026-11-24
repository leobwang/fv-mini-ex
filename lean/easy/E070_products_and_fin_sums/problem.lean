/- E070 | Products and Fin sums | 2-3 min | Finset.prod, prod_range_succ, prod_const, Fin.sum_univ_succ, Fin.sum_univ_three, mathlib
GOAL
  Products `∏ i ∈ range n, f i` (= f 0 * … * f (n-1)) work like E042's sums. For `g : Fin n → M`,
  `∑ i, g i` sums over every `i : Fin n` (the finset `Finset.univ`).

REFERENCE
  open Finset in example : ∏ i ∈ range 3, (i + 2) = 24 := by decide   -- small closed products compute
  #check Finset.prod_range_succ  -- ∏ x ∈ range (n + 1), f x = (∏ x ∈ range n, f x) * f n
  #check Finset.prod_const       -- ∏ _x ∈ s, b = b ^ #s      (`#s` is the number of elements of s)
  #check Finset.card_range       -- #(range n) = n
  #check Fin.sum_univ_three      -- ∑ i, f i = f 0 + f 1 + f 2         (f : Fin 3 → M)
  #check Fin.sum_univ_succ       -- ∑ i, f i = f 0 + ∑ i : Fin n, f i.succ   (f : Fin (n + 1) → M)
  #check Fin.val_succ            -- ↑j.succ = ↑j + 1
  `∏` is typed `\prod`. `(i : ℕ)`, displayed `↑i`, is the value of `i : Fin n` as a natural number.
BANNED: exact?, aesop
NOTE: in `sum_fin_succ`, `g ((i : ℕ) + 1)` adds in ℕ after the cast, not with wrap-around `Fin` addition.
-/
import Mathlib

namespace E070

-- BEGIN SPEC
open Finset

theorem prod_four : ∏ i ∈ range 4, (i + 1) = 24 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prod_peel (n : ℕ) : ∏ i ∈ range (n + 1), (i + 1) = (n + 1) * ∏ i ∈ range n, (i + 1) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prod_const_two (n : ℕ) : ∏ _i ∈ range n, (2 : ℕ) = 2 ^ n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_fin_three (g : Fin 3 → ℝ) : ∑ i, g i = g 0 + g 1 + g 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_fin_succ (g : ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin (n + 1), g i = g 0 + ∑ i : Fin n, g ((i : ℕ) + 1) :=
-- END SPEC
  sorry

end E070

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Products peel exactly like sums (`prod_range_succ` is `sum_range_succ` with `*`); sums over a
    whole `Fin n` have their own `Fin.sum_univ_*` lemmas.
H2. `prod_peel`: peel, then swap the factors. `prod_const_two`: a product of a constant is a power whose
    exponent is `#(range n)`. `sum_fin_succ`: peel the `0` term with `Fin.sum_univ_succ`; what is left
    differs only by `↑i.succ` vs `↑i + 1`.
H3. `decide`; `rw [prod_range_succ, mul_comm]`; `rw [prod_const, card_range]`; `Fin.sum_univ_three g`;
    `rw [Fin.sum_univ_succ]` and then `simp` (it knows `Fin.val_succ`).
-/
