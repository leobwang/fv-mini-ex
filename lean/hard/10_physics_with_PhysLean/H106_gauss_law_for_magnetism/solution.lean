/- H106 | Gauss's law for magnetism from the vector potential | 30-60 min | Space.div, Space.curl, Fin 3 sums, fderiv of a difference, Schwarz, physlib
GOAL
  physlib defines the magnetic field of an electromagnetic potential as `B = ∇ × A` (`A` = vector potential).
  Prove Gauss's law for magnetism `∇ · B = 0` for a smooth potential, via `∇ · (∇ × F) = 0` for C² fields `F`.

REFERENCE
  `Space` = 3D space; `∂[i] f x` = ∂f/∂xᵢ at `x`; `F x i` = component `i` of `F x : EuclideanSpace ℝ (Fin 3)`.
  `V : ElectromagneticPotential`, `c : SpeedOfLight` (> 0); `ContDiff ℝ ∞` = smooth, `ContDiff ℝ 2` = C²; `fun_prop` gets C² of `V.vectorPotential c t` from `hV`.
  example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) : (∇ ⬝ F) x = ∑ i, ∂[i] (fun y => F y i) x := rfl
  example (F : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :   -- curl: component i uses i+1, i+2 (mod 3)
    (∇ ⨯ F) x 0 = ∂[1] (fun y => F y 2) x - ∂[2] (fun y => F y 1) x := rfl
  #check ThreeDimension.magneticField_eq_3D  -- magneticField c V = fun t x => (∇ ⨯ vectorPotential c V t) x
  #check Space.deriv_commute   -- ContDiff ℝ 2 f → ∂[u] (∂[v] f) = ∂[v] (∂[u] f)   (Schwarz)
  #check Space.deriv_eq        -- ∂[μ] f x = fderiv ℝ f x (Space.basis μ)
  #check Space.deriv_eq_fderiv_fun  -- ∂[μ] f = fun x => fderiv ℝ f x (basis μ)  (then `fun_prop` sees it)
  #check fderiv_fun_sub        -- DifferentiableAt f x → DifferentiableAt g x → fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x
  #check contDiff_euclidean    -- ContDiff ℝ n F ↔ ∀ i, ContDiff ℝ n (fun x => F x i)
  `simp only [Space.div, Space.curl, Fin.sum_univ_three]` unfolds both; `Fin.reduceAdd` computes `1 + 2 = 0`.
BANNED: Space.div_of_curl_eq_zero, Electromagnetism.ElectromagneticPotential.magneticField_div_eq_zero, Space.deriv_coord_2nd_sub, Space.deriv_coord_2nd_add, Space.curl_of_curl, Electromagnetism.ThreeDimension.gaussLawMagnetic
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace H106

-- MILESTONE (optional: change or delete)
/-- `∂[u]` distributes over a difference of first partial derivatives of a C² field. -/
theorem deriv_sub_deriv (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f)
    (u v w : Fin 3) :
    ∂[u] (fun x => ∂[v] (fun x => f x w) x - ∂[w] (fun x => f x v) x) =
      ∂[u] (∂[v] (fun x => f x w)) - ∂[u] (∂[w] (fun x => f x v)) := by
  have h1 : Differentiable ℝ (∂[v] (fun x => f x w)) := by
    have : ContDiff ℝ 2 (fun x => f x w) := contDiff_euclidean.mp hf w
    rw [deriv_eq_fderiv_fun]
    fun_prop
  have h2 : Differentiable ℝ (∂[w] (fun x => f x v)) := by
    have : ContDiff ℝ 2 (fun x => f x v) := contDiff_euclidean.mp hf v
    rw [deriv_eq_fderiv_fun]
    fun_prop
  ext x
  rw [Pi.sub_apply, Space.deriv_eq, Space.deriv_eq, Space.deriv_eq, fderiv_fun_sub (h1 x) (h2 x)]
  rfl

-- MILESTONE (optional: change or delete)
/-- The divergence of a curl vanishes. -/
theorem div_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f)
    (x : Space) : (∇ ⬝ (∇ ⨯ f)) x = 0 := by
  have hc : ∀ i : Fin 3, ContDiff ℝ 2 (fun x => f x i) := fun i => contDiff_euclidean.mp hf i
  simp only [Space.div, Space.curl, Fin.sum_univ_three, Fin.isValue, Fin.reduceAdd, zero_add]
  rw [deriv_sub_deriv f hf, deriv_sub_deriv f hf, deriv_sub_deriv f hf]
  simp only [Pi.sub_apply]
  -- WHY: Schwarz turns each `∂[u] (∂[v] f_w)` into `∂[v] (∂[u] f_w)`, pairing the six terms off.
  rw [deriv_commute _ (hc 0), deriv_commute _ (hc 1), deriv_commute _ (hc 2)]
  ring

-- BEGIN SPEC
theorem gauss_magnetic (c : SpeedOfLight) (V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V)
    (t : Time) (x : Space) : (∇ ⬝ V.magneticField c t) x = 0 :=
-- END SPEC
  by
    rw [ThreeDimension.magneticField_eq_3D]
    exact div_curl_eq_zero _ (by fun_prop) x

end H106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The main theorem is the milestone `div_curl_eq_zero` applied to the vector potential at time `t`; its
    smoothness follows from `hV` by `fun_prop`. The real work is `∇ · (∇ × f) = 0`.
H2. Unfold `div` and `curl` and expand the `Fin 3` sum: you get three terms `∂[i] (fun x => ∂[i+1] f_{i+2} x -
    ∂[i+2] f_{i+1} x)`. Split each with the first milestone, then Schwarz pairs the six second derivatives off.
    For the first milestone, the two first derivatives are differentiable because each component is C².
H3. Milestone 1: pointwise, turn every `∂` into `fderiv` with `Space.deriv_eq`; the key step is then
    `fderiv_fun_sub (h1 x) (h2 x)`, with `h1 : Differentiable ℝ (∂[v] (fun x => f x w))` from
    `deriv_eq_fderiv_fun` + `fun_prop` (given `ContDiff ℝ 2 (fun x => f x w)`).
    Milestone 2: `hc i : ContDiff ℝ 2 (fun x => f x i) := contDiff_euclidean.mp hf i`; after splitting with
    milestone 1, three Schwarz rewrites (`deriv_commute`), then `ring`.
-/
