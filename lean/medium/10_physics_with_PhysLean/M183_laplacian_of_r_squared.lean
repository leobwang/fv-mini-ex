/- M183 | Laplacian of r² | 15 min | Δ, ∂[i], laplacian_eq_sum_snd_deriv, funext, fderiv_const_mul, physlib
GOAL
  In `d`-dimensional space, the Laplacian of `r² = ‖y‖²` is the constant `2d`: `Δ ‖y‖² = ∑ᵢ ∂ᵢ∂ᵢ ‖y‖² = 2d`.

REFERENCE
  `Space d` is `d`-dimensional space; `y.val i` (also written `y i`) is the `i`-th coordinate of `y`.
  `∂[i] f x` (`Space.deriv i f x`) is ∂f/∂yᵢ at `x`; `Δ f` is `Space.laplacian f` (`= ∇ ⬝ ∇ f`, where `∇ ⬝ F` is the divergence `Space.div F`).
  #check Space.laplacian_eq_sum_snd_deriv  -- Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x
  #check Space.deriv_norm_sq    -- ∂[i] (fun x => ‖x‖ ^ 2) x = 2 * x.val i
  #check Space.deriv_component  -- ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0
  #check Space.deriv_eq         -- ∂[μ] f x = fderiv ℝ f x (basis μ)   (unfold to a Fréchet derivative)
  #check fderiv_const_mul       -- DifferentiableAt 𝕜 a x → fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x
  example {d : ℕ} (i : Fin d) (x : Space d) : DifferentiableAt ℝ (fun y : Space d => y i) x := by fun_prop
  `funext y` proves an equation between functions pointwise; the `d` on the right is the cast `(d : ℝ)`.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Laplacian

open Space

namespace M183

-- BEGIN SPEC
theorem laplacian_norm_sq {d : ℕ} (x : Space d) : Δ (fun y : Space d => ‖y‖ ^ 2) x = 2 * d :=
-- END SPEC
  sorry

end M183

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rewrite `Δ` as a sum of second partial derivatives. The first derivative `∂[i] ‖·‖²` is known as a
    function (`2 * y i`); then each second derivative is the constant `2`.
H2. Prove two helper facts with `have`: `∂[i] (fun y => ‖y‖ ^ 2) = fun y => 2 * y i` (by `funext`) and
    `∂[i] (fun y => 2 * y i) x = 2` (via `Space.deriv_eq` and `fderiv_const_mul`), then `simp` the sum.
H3. `rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]; simp [← Space.deriv_eq]` proves the second fact;
    the main goal ends as `↑d * 2 = 2 * ↑d` (`ring`).
-/
