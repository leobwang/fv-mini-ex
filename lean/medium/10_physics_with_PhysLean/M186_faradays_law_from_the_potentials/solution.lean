/- M186 | Faraday's law from the potentials | 10-15 min | ElectromagneticPotential, curl, rw with side goals, fun_prop, physlib
GOAL
  For a smooth electromagnetic potential `V` (scalar potential `φ`, vector potential `A`), the fields
  `E = -∇φ - ∂ₜA` and `B = ∇ × A` satisfy Faraday's law `∇ × E = -∂ₜ B` at every time `t` and point `x`.
BANNED: faradayLaw

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace M186

/- SKELETON · faraday
  1. Fields → potentials: E on the left, B on the right.                     R1, R2
  2. Left side, in this order (each `rw` puts its smoothness side goals
     right after the main goal):
       curl (-∇φ - ∂ₜA) → curl (-∇φ) - curl (∂ₜA)                           R3
       curl (-∇φ)       → -curl (∇φ)                                         R4
       curl (∇φ)        → 0                                                  R5
  3. Right side: ∂ₜ (curl A) → curl (∂ₜA)                                     R6
     Steps 1–3 fit in one `rw [...]` with the six lemmas in this order.
  4. Main goal is now `-0 - X = -X` with X = curl (∂ₜA) at x (inside
     beta-redexes): focus it with `·` and close it.                          R7
  5. Five side goals remain, all `Differentiable`/`ContDiff` facts about φ, ∇φ,
     ∂ₜA, ↿A; close them all with `all_goals`. It finds R9–R12 and uses hV.  R8
-/
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
H1. Write both fields in terms of the potentials first (R1, R2). Then two facts do all the physics: the
    curl of a gradient vanishes (R5, M182), and the time derivative commutes with the curl (R6). The rest is
    linearity of the curl (R3, R4) and smoothness side goals.
H2. One `rw [...]` chain: fields into potentials; split `curl (-∇φ - ∂ₜA)` with `fun_curl_sub`, then
    `fun_curl_neg`; kill `curl (∇ φ)`; move `∂ₜ` inside the curl on the right. The main goal comes first and
    reads `-0 - X = -X`; after it come five smoothness side goals.
H3. The rewrite order: `electricField_eq_3D, magneticField_eq_3D, fun_curl_sub, fun_curl_neg,
    curl_of_grad_eq_zero, time_deriv_curl_commute`. The main goal left is algebra (R7); every side goal
    is smoothness (R8), so close the main goal first.
-/
