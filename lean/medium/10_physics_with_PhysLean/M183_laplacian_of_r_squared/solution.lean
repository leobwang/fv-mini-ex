/- M183 | Laplacian of r² | 15 min | Δ, ∂[i], laplacian_eq_sum_snd_deriv, funext, fderiv_const_mul, physlib
GOAL
  In `d`-dimensional space, the Laplacian of `r² = ‖y‖²` is the constant `2d`: `Δ ‖y‖² = ∑ᵢ ∂ᵢ∂ᵢ ‖y‖² = 2d`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.SpaceAndTime.Space.Derivatives.Laplacian

open Space

namespace M183

/- SKELETON · laplacian_norm_sq
  1. Fact 1, the first derivative as a FUNCTION (state it with `have`, before touching the goal):
       h1 : ∀ i : Fin d, ∂[i] (fun y : Space d => ‖y‖ ^ 2) = fun y => 2 * y i
       proof: intro i, then pointwise, then the norm-square lemma              R1 → R2
  2. Fact 2, the second derivative as a NUMBER at the theorem's point `x`:
       h2 : ∀ i : Fin d, ∂[i] (fun y : Space d => 2 * y i) x = 2
       proof: intro i; ∂ → fderiv, constant factor out (side goal by R5)      R3 → R4 + R5
              then evaluate: one `simp` told the direction of R7 (W3)          R6 → R7 → R8
              (or by hand, as in W2: R6, R7, R8 leave `2 * 1 = 2`, closed by R13)
  3. Main goal: `Δ` → a sum of second partial derivatives at `x`:              R9
  4. `simp` with h1 and h2 (inside the sum), then sum the constant `2`:         R10 → R11 → R12
  5. Close `↑d * 2 = 2 * ↑d`:                                                  R13
-/
-- BEGIN SPEC
theorem laplacian_norm_sq {d : ℕ} (x : Space d) : Δ (fun y : Space d => ‖y‖ ^ 2) x = 2 * d :=
-- END SPEC
  by
    have h1 : ∀ i : Fin d, ∂[i] (fun y : Space d => ‖y‖ ^ 2) = fun y => 2 * y i := by
      intro i
      funext y
      exact deriv_norm_sq y i
    have h2 : ∀ i : Fin d, ∂[i] (fun y : Space d => 2 * y i) x = 2 := by
      intro i
      rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]
      simp [← Space.deriv_eq]
    rw [laplacian_eq_sum_snd_deriv]
    simp [h1, h2]
    ring

end M183

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Δ f x` is the sum over `i : Fin d` of the second partials `∂[i] (∂[i] f) x` (R9). The first partial
    of `‖y‖²` is the function `y ↦ 2 * y i`; its partial along `i` is the constant `2`; `d` copies of `2`
    sum to `2 * d`.
H2. Prove two `have`s first: `h1 : ∀ i : Fin d, ∂[i] (fun y : Space d => ‖y‖ ^ 2) = fun y => 2 * y i`
    (an equation of functions: `funext`, then `Space.deriv_norm_sq`) and
    `h2 : ∀ i : Fin d, ∂[i] (fun y : Space d => 2 * y i) x = 2` (`Space.deriv_eq`, `fderiv_const_mul`, then
    fold back to `∂` and use `∂[i] yᵢ = 1`). Then `rw [laplacian_eq_sum_snd_deriv]` and let `simp` use
    `h1`, `h2` inside the sum (`rw` cannot rewrite under `∑ i`).
H3. `h1`: `intro i; funext y; exact deriv_norm_sq y i`. `h2`: `intro i;
    rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]; simp [← Space.deriv_eq]`. Main:
    `rw [laplacian_eq_sum_snd_deriv]; simp [h1, h2]` leaves `↑d * 2 = 2 * ↑d`, closed by `ring`.
-/
