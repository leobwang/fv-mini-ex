/- H106 | Gauss's law for magnetism from the vector potential | 30-60 min | Space.div, Space.curl, Fin 3 sums, fderiv of a difference, Schwarz, physlib
GOAL
  physlib defines the magnetic field of an electromagnetic potential as `B = ∇ × A` (`A` = vector potential).
  Prove Gauss's law for magnetism `∇ · B = 0` for a smooth potential, via `∇ · (∇ × F) = 0` for C² fields `F`.

BANNED: Space.div_of_curl_eq_zero, Electromagnetism.ElectromagneticPotential.magneticField_div_eq_zero, Space.deriv_coord_2nd_sub, Space.deriv_coord_2nd_add, Space.curl_of_curl, Electromagnetism.ThreeDimension.gaussLawMagnetic

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Electromagnetism.ThreeDimension.Basic

open Electromagnetism ElectromagneticPotential Space Time ContDiff

namespace H106

/- SKELETON · deriv_sub_deriv   (milestone; prove it FIRST; div_curl_eq_zero uses it three times)
  1. Both first derivatives are differentiable; `have` each one, after putting the
     component's C² fact into the context (fun_prop could also use `hf`):              R1 → R2 → R3
       h1 : Differentiable ℝ (∂[v] (fun x => f x w))
       h2 : Differentiable ℝ (∂[w] (fun x => f x v))
  2. Equation of functions → equation at a point `x`:                                  R4
  3. Apply the difference on the right, then every `∂ … x` → `fderiv` (three terms):   R5, R6 ×3
  4. Split the derivative of the difference at `x`, using `h1 x`, `h2 x`:              R8 with R7
  5. Both sides now agree by definition:                                              R9
-/
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

/- SKELETON · div_curl_eq_zero   (milestone; uses deriv_sub_deriv; gauss_magnetic uses it)
  0. Prove deriv_sub_deriv first (used in step 3).
  1. C² of every component, as one fact `hc : ∀ i : Fin 3, ContDiff ℝ 2 (fun x => f x i)`:   R1
  2. Unfold `∇ ⬝` and `∇ ⨯`, expand the `Fin 3` sum, compute the indices (one simp only):   R10, R11, R12, R13
     three terms `∂[i] (fun x => ∂[i+1] f_{i+2} x - ∂[i+2] f_{i+1} x) x` are left
  3. Split each with the milestone, then apply the differences at `x`:     rw [deriv_sub_deriv f hf] ×3, R5
  4. Schwarz once per component (`hc 0`, `hc 1`, `hc 2`) so the six terms pair off:      R14 ×3
  5. Cancel:                                                                         R15
-/
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

/- SKELETON · gauss_magnetic
  0. Prove the milestones deriv_sub_deriv and div_curl_eq_zero first (step 2 uses the second).
  1. Write the magnetic field as the curl of the vector potential:                     R16
  2. The goal is now `∇ ⬝ (∇ ⨯ A t)` at `x` (with an unreduced `(fun t x => …) t`, which `exact`
     accepts): apply div_curl_eq_zero to `A t`; its C² argument is                      R17
-/
-- BEGIN SPEC
theorem gauss_magnetic (c : SpeedOfLight) (V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V)
    (t : Time) (x : Space) : (∇ ⬝ V.magneticField c t) x = 0 :=
-- END SPEC
  by
    rw [ThreeDimension.magneticField_eq_3D]
    exact div_curl_eq_zero _ (by fun_prop) x

end H106

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The main theorem is `div_curl_eq_zero` applied to the vector potential at time `t`, once the magnetic
    field is rewritten as a curl (R16); the smoothness it needs follows from `hV` by `fun_prop` (R17). The
    real work is `∇ · (∇ × f) = 0`: six second partial derivatives that cancel in pairs by Schwarz.
H2. Milestone 1: show both first derivatives are differentiable (R1 → R2 → R3), go pointwise with `ext x`,
    turn every `∂` into `fderiv` (R5, R6), split the derivative of the difference (R7, R8), close by `rfl`.
    Milestone 2: unfold `div` and `curl` and expand the `Fin 3` sum (R10–R13); rewrite each of the three
    terms with milestone 1, `simp only [Pi.sub_apply]`, then one Schwarz swap per component (R14) and `ring`.
H3. Milestone 1: `have : ContDiff ℝ 2 (fun x => f x w) := contDiff_euclidean.mp hf w`, then
    `rw [Space.deriv_eq_fderiv_fun]; fun_prop` gives `h1`; after `ext x`, `Pi.sub_apply` and three
    `Space.deriv_eq`, the key rewrite is `fderiv_fun_sub (h1 x) (h2 x)`.
    Milestone 2: `simp only [Space.div, Space.curl, Fin.sum_univ_three, Fin.isValue, Fin.reduceAdd, zero_add]`,
    then `rw [Space.deriv_commute _ (hc 0), Space.deriv_commute _ (hc 1), Space.deriv_commute _ (hc 2)]`.
-/
