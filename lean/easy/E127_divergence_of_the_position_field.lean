/- E127 | Divergence of the position field | 2-3 min | Space, Space.div, ∂[i], Finset.sum_const, physlib
GOAL
  In `d`-dimensional space the position field `x ↦ x` has divergence `∇ · x = d` at every point.

REFERENCE
  `Space d` is a structure over `Fin d → ℝ`: `x.val i` is the `i`-th coordinate of the point `x`.
  `basis.repr y : EuclideanSpace ℝ (Fin d)` is the coordinate vector of `y`, so `y ↦ basis.repr y` is "x ↦ x".
  example (d : ℕ) (f : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d) :
      (∇ ⬝ f) x = ∑ i, ∂[i] (fun y => f y i) x := rfl     -- `∂[i]` = partial derivative in direction `i`
  #check Space.basis_repr_apply  -- (basis.repr p) i = p.val i
  #check Space.deriv_component   -- ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0
  #check Finset.sum_const        -- ∑ _x ∈ s, b = s.card • b
  example (d : ℕ) : (Finset.univ : Finset (Fin d)).card = d := by rw [Finset.card_univ, Fintype.card_fin]
  example (n : ℕ) : n • (1 : ℝ) = n := by rw [nsmul_eq_mul, mul_one]
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space

namespace E127

-- BEGIN SPEC
theorem div_position {d : ℕ} (x : Space d) :
    (∇ ⬝ (fun y : Space d => basis.repr y)) x = d :=
-- END SPEC
  sorry

end E127

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `∇ ⬝` (it is `Space.div`) to a sum of partial derivatives, one per direction.
H2. Each summand is `∂[i]` of the `i`-th coordinate function: rewrite the coordinate with
    `basis_repr_apply`, then `deriv_component` gives `if i = i then 1 else 0`. A sum of `d` ones is `d`.
H3. `rw [Space.div]; simp only [Space.basis_repr_apply, Space.deriv_component, if_true]`, then
    `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]` (or `simp`).
-/
