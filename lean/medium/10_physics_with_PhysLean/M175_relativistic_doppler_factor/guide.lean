/- Guide for M175 (Relativistic Doppler factor).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` (or `k`) in an entry is only there to finish the example; it shows what the goal
became. `G : Prop` is a goal the entry does not touch.
Part W: worked combinations on objects that are NOT the exercise's (the other light-cone coordinate
`t - xᵢ`; a Euclidean identity for a plain real `c` with `c ^ 2 = 1 / (1 + u ^ 2)`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.LorentzGroup.Boosts.Apply

open Lorentz Vector LorentzGroup

namespace M175Guide

/-! # Part R · Reference entries -/

/-! ## Splitting the goal -/

/-! ### R1. `constructor` · goal list: `A ∧ B` → two goals `A`, `B` -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  exact ha
  exact hb

/-! ## Coordinates of a boosted vector
`boost i β hβ : LorentzGroup d` is the boost with speed `β` along space axis `i`; it needs
`hβ : |β| < 1`. `Λ • p` applies a Lorentz transformation `Λ` to the 4-vector `p`. -/

/-! ### R2. `Lorentz.Vector.boost_time_eq` · goal: time coordinate of `boost i β hβ • p`
`(boost i β hβ • p) (Sum.inl 0) = γ β * (p (Sum.inl 0) - β * p (Sum.inr i))`, i.e. `t' = γ (t - β xᵢ)`. -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (γ β * (p (Sum.inl 0) - β * p (Sum.inr i)))) : P ((boost i β hβ • p) (Sum.inl 0)) := by
  rw [Lorentz.Vector.boost_time_eq]
  exact h

/-! ### R3. `Lorentz.Vector.boost_inr_self_eq` · goal: coordinate `i` (the boost axis) of `boost i β hβ • p`
`(boost i β hβ • p) (Sum.inr i) = γ β * (p (Sum.inr i) - β * p (Sum.inl 0))`, i.e. `xᵢ' = γ (xᵢ - β t)`. -/
example {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (γ β * (p (Sum.inr i) - β * p (Sum.inl 0)))) : P ((boost i β hβ • p) (Sum.inr i)) := by
  rw [Lorentz.Vector.boost_inr_self_eq]
  exact h

/-! ### R4. `ring` · closes a commutative-ring identity
It treats `γ β` and the coordinates `p (Sum.inl 0)`, `p (Sum.inr i)` as unknowns (atoms). -/
example (β a b : ℝ) : γ β * a + γ β * b - (a + b) * γ β = 0 := by
  ring

/-! ## The Lorentz factor `γ β = 1 / √(1 - β ^ 2)` -/

/-! ### R5. `LorentzGroup.γ_det_not_zero` · `|β| < 1 → 1 - β ^ 2 ≠ 0` · context gains the fact -/
example (β : ℝ) (hβ : |β| < 1) (G : Prop) (k : 1 - β ^ 2 ≠ 0 → G) : G := by
  have hd := LorentzGroup.γ_det_not_zero β hβ
  exact k hd

/-! ### R6. `calc a = b := ?_; _ = c := ?_` · goal list: `a = c` → `a = b`, `b = c`
In a real proof each `?_` is replaced by `by tac`; the middle term `b` is yours to choose. -/
example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := ?_
    _ = c := ?_
  exact h1
  exact h2

/-! ### R7. `LorentzGroup.γ_sq` · `|β| < 1 → γ β ^ 2 = 1 / (1 - β ^ 2)` · goal: `γ β ^ 2` → a fraction
`rw` needs `γ β ^ 2` literally: `γ β * γ β` does not match. -/
example (β : ℝ) (hβ : |β| < 1) (P : ℝ → Prop) (h : P (1 / (1 - β ^ 2))) : P (γ β ^ 2) := by
  rw [LorentzGroup.γ_sq β hβ]
  exact h

/-! ### R8. `field_simp` · goal: clears denominators that a hypothesis `hx : x ≠ 0` says are nonzero
It closes `a / x * x = a`; on `a / x = b` it leaves `a = x * b`. -/
example (a x : ℝ) (hx : x ≠ 0) : a / x * x = a := by
  field_simp

example (a b x : ℝ) (hx : x ≠ 0) (h : a = x * b) : a / x = b := by
  field_simp
  exact h

/-! Without a way to prove `x ≠ 0`, `field_simp` cannot cancel: `a / x * x = a` stays as `a * x / x = a`. -/
example (a x : ℝ) (h : a * x / x = a) : a / x * x = a := by
  field_simp
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The other light-cone coordinate `t - xᵢ` is scaled by `γ β * (1 + β)`: R2, R3, R4 -/
example {d : ℕ} (p : Lorentz.Vector d) (i : Fin d) (β : ℝ) (hβ : |β| < 1) :
    (boost i β hβ • p) (Sum.inl 0) - (boost i β hβ • p) (Sum.inr i)
      = γ β * (1 + β) * (p (Sum.inl 0) - p (Sum.inr i)) := by
  rw [Lorentz.Vector.boost_time_eq]
  rw [Lorentz.Vector.boost_inr_self_eq]
  ring

/-! ### W2. Regroup until `c ^ 2` appears, substitute, clear the denominator: R6, R4, R7-style `rw`, R8
With `c = cos θ` and `u = tan θ` this is `sin² θ + cos² θ = 1`. -/
example (c u : ℝ) (hc : c ^ 2 = 1 / (1 + u ^ 2)) (hu : 1 + u ^ 2 ≠ 0) :
    (c * u) ^ 2 + c ^ 2 = 1 := by
  calc (c * u) ^ 2 + c ^ 2 = c ^ 2 * (1 + u ^ 2) := ?_
    _ = 1 := ?_
  ring
  rw [hc]
  field_simp

end M175Guide
