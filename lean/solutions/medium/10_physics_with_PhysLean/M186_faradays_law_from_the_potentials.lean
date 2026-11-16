/- M186 | Faraday's law from the potentials | 10-15 min | ElectromagneticPotential, curl, rw with side goals, fun_prop, physlib
GOAL
  For a smooth electromagnetic potential `V` (scalar potential `φ`, vector potential `A`), the fields
  `E = -∇φ - ∂ₜA` and `B = ∇ × A` satisfy Faraday's law `∇ × E = -∂ₜ B` at every time `t` and point `x`.

REFERENCE
  `V : ElectromagneticPotential` (a 4-potential on spacetime); `c : SpeedOfLight` (a positive real constant).
  `V.electricField c t : Space → EuclideanSpace ℝ (Fin 3)`; `∇ ⨯ F` is `curl F`; `∂ₜ g t` = d/dt of `g : Time → _`.
  #check ThreeDimension.electricField_eq_3D -- V.electricField c = fun t x => -∇ (V.scalarPotential c t) x - ∂ₜ (fun t => V.vectorPotential c t x) t
  #check ThreeDimension.magneticField_eq_3D -- V.magneticField c = fun t x => curl (V.vectorPotential c t) x
  #check Space.time_deriv_curl_commute -- ContDiff ℝ 2 ↿fₜ → ∂ₜ (fun t => curl (fₜ t) x) t = curl (fun x => ∂ₜ (fun t => fₜ t x) t) x
  #check Space.curl_of_grad_eq_zero    -- ContDiff ℝ 2 f → curl (∇ f) = 0
  #check Space.fun_curl_neg   -- Differentiable ℝ f → curl (fun x => -f x) = fun x => -curl f x
  #check Space.fun_curl_sub   -- Differentiable ℝ f1 → Differentiable ℝ f2 → curl (fun x => f1 x - f2 x) = fun x => curl f1 x - curl f2 x
  `↿fₜ` is `fₜ` uncurried: `fun (t, x) => fₜ t x`. `ContDiff ℝ ∞ V` says `V` is smooth.
  `rw [h]` with `h : P → a = b` rewrites and adds `P` as a goal after the main one; `fun_prop` proves such
  `Differentiable`/`ContDiff` goals (physlib registers the smoothness of `φ`, `A` given `hV`).
BANNED: faradayLaw
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace M186

-- BEGIN SPEC
theorem faraday (c : SpeedOfLight) (V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V)
    (t : Time) (x : Space) :
    (∇ ⨯ V.electricField c t) x = - ∂ₜ (fun t => V.magneticField c t x) t :=
-- END SPEC
  by
    rw [ThreeDimension.electricField_eq_3D, ThreeDimension.magneticField_eq_3D, fun_curl_sub,
      fun_curl_neg, curl_of_grad_eq_zero, time_deriv_curl_commute]
    · simp
    all_goals fun_prop

end M186

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write both fields in terms of the potentials first. Then two facts do all the physics: the curl of a
    gradient vanishes (M182), and the time derivative commutes with the curl.
H2. Rewrite in this order: `E` and `B` into potentials; split `curl (-∇φ - ∂ₜA)` with `fun_curl_sub` and
    `fun_curl_neg`; kill `curl (∇ φ)`; move `∂ₜ` inside the curl on the right. What remains is
    `-0 - X = -X`, plus smoothness side goals.
H3. The rewrite order: `electricField_eq_3D, magneticField_eq_3D, fun_curl_sub, fun_curl_neg,
    curl_of_grad_eq_zero, time_deriv_curl_commute`. The main goal left is algebra; every side goal is smoothness.
-/
