/- E107 | Contractions and fixed points | 2-3 min | LipschitzWith, ContractingWith, IsFixedPt, NNReal, mathlib
GOAL
  Show that `g x = x / 2 + 1` is Lipschitz with constant `1/2`, hence a contraction, and that `2` is a
  fixed point of `g`. This is the vocabulary of fixed-point iteration `x_{n+1} = g x_n`.

REFERENCE
  `ℝ≥0` (`NNReal`) is the type of reals `≥ 0`; Lipschitz constants live there. `↑K : ℝ` is the cast.
  `LipschitzWith K f`: `edist (f x) (f y) ≤ K * edist x y` for all `x y` (extended distance).
  #check LipschitzWith.of_dist_le_mul   -- (∀ x y, dist (f x) (f y) ≤ ↑K * dist x y) → LipschitzWith K f
  `ContractingWith K f` is by definition `K < 1 ∧ LipschitzWith K f`, so build it as `⟨hK, hf⟩`.
  `Function.IsFixedPt f x` is by definition `f x = x` (unfold with `Function.IsFixedPt` in `simp`/`norm_num`).
  #check Real.dist_eq    -- dist x y = |x - y|
  #check NNReal.coe_div  -- ↑(r₁ / r₂) = ↑r₁ / ↑r₂   (with NNReal.coe_one, NNReal.coe_ofNat)
  #check abs_div         -- |a / b| = |a| / |b|
-/
import Mathlib

namespace E107

-- BEGIN SPEC
theorem half_lipschitz : LipschitzWith (1 / 2) (fun x : ℝ => x / 2 + 1) :=
-- END SPEC
  by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    rw [show x / 2 + 1 - (y / 2 + 1) = (x - y) / 2 by ring, abs_div, abs_two]
    linarith

-- BEGIN SPEC
theorem half_contracting : ContractingWith (1 / 2) (fun x : ℝ => x / 2 + 1) :=
-- END SPEC
  ⟨by norm_num, half_lipschitz⟩

-- BEGIN SPEC
theorem two_is_fixed : Function.IsFixedPt (fun x : ℝ => x / 2 + 1) 2 :=
-- END SPEC
  by norm_num [Function.IsFixedPt]

end E107

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Reduce `LipschitzWith` to a statement about `dist` on `ℝ`, i.e. absolute values.
H2. `refine LipschitzWith.of_dist_le_mul fun x y => ?_`, then cast the constant to `ℝ` with
    `simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]`.
H3. `rw [show x / 2 + 1 - (y / 2 + 1) = (x - y) / 2 by ring, abs_div, abs_two]; linarith`.
    The contraction is the pair `⟨(proof of 1/2 < 1), half_lipschitz⟩`.
-/
