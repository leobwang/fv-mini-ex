/- E127 | Divergence of the position field | 2-3 min | Space, Space.div, ∂[i], Finset.sum_const, physlib
GOAL
  In `d`-dimensional space the position field `x ↦ x` has divergence `∇ · x = d` at every point.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Div

open Space

namespace E127

/- SKELETON · div_position
  1. Unfold the divergence into a sum of partial derivatives:              R1
  2. In one `simp only [...]` (the terms sit under `∑` and `fun`, so not `rw`):
       coordinate vector entry → coordinate                                R2
       ∂[i] of the i-th coordinate → `if i = i then 1 else 0` → `if True` R3
       drop the decided `if`; the goal is `∑ x, 1 = ↑d`                     R4
  3. Count the ones: sum of a constant → `card • 1` → `d • 1` → `↑d * 1` → `↑d`
                                                                           R5 → R6 → R7 → R8 → R9
-/
-- BEGIN SPEC
theorem div_position {d : ℕ} (x : Space d) :
    (∇ ⬝ (fun y : Space d => basis.repr y)) x = d :=
-- END SPEC
  by
    rw [Space.div]
    simp only [Space.basis_repr_apply, Space.deriv_component, if_true]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end E127

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `∇ ⬝` is `Space.div`: unfold it to a sum over `i : Fin d` of `∂[i]` of the `i`-th component, then
    every summand is `∂x_i/∂x_i = 1` and the sum of `d` ones is `↑d`.
H2. `rw [Space.div]`; then one `simp only` with `Space.basis_repr_apply` (component → `y.val i`),
    `Space.deriv_component` (Kronecker delta) and `if_true`; then count with `Finset.sum_const`,
    `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`, `mul_one` (or just `simp`).
H3. After `rw [Space.div]`, `simp only [Space.basis_repr_apply, Space.deriv_component, if_true]` leaves
    `∑ x, 1 = ↑d`; finish with one `rw [...]` of the five counting lemmas of H2, in that order.
-/
