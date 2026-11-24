/- Guide for E053 (Structures with extends).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the structures `Rect` and `Box` below, NOT the exercise's `Point` and `Point3`.
Part W: worked combinations on `Rect` and `Box`.
Assumed: Lean basics (E001–E033), in particular structures, fields and projections (E017).
-/

namespace E053Guide

/-- A rectangle: width and height. -/
structure Rect where
  w : Int
  h : Int

/-- A box is a rectangle plus a depth. `extends Rect` gives `Box` the fields `w`, `h` (inherited)
and `d` (new), the parent projection `Box.toRect : Box → Rect`, and the constructor
`Box.mk (toRect : Rect) (d : Int) : Box`: the parent part comes first, as ONE argument. -/
structure Box extends Rect where
  d : Int

/-- Uses inherited fields directly: `b.w` means `b.toRect.w`. -/
def Box.vol (b : Box) : Int := b.w * b.h * b.d

/-- A box whose depth equals its width (functional update, R1). -/
def Box.cube (r : Rect) : Box := { r with d := r.w }

/-- A box of depth `0` (anonymous constructor, R2). -/
def Box.flat (r : Rect) : Box := ⟨r, 0⟩

/-! # Part R · Reference entries -/

/-! ## Building a child value from a parent value -/

/-! ### R1. `{ r with d := v }` (functional update) · closes a `⊢ Box` hole
`r` may have the PARENT type `Rect`: its fields are copied and the new field `d` is given.
The infoview prints the result as `{ toRect := r, d := v }`. -/
example (r : Rect) (v : Int) : Box := by
  exact { r with d := v }

/-! ### R2. `refine ⟨r, ?_⟩` (anonymous constructor) · goal `⊢ Box` → the new field's type
`⟨_, _⟩` fills `Box.mk`'s arguments in order: the parent `r : Rect` first, then `d`.
In term mode: `⟨r, v⟩`. -/
example (r : Rect) (v : Int) : Box := by
  refine ⟨r, ?_⟩
  exact v

/-! ## Reducing projections of a constructed value -/

/-! ### R3. `unfold D` · goal: the defined name `D` → its body -/
example (r : Rect) (P : Rect → Prop) (h : P ({ toRect := r, d := r.w } : Box).toRect) :
    P (Box.cube r).toRect := by
  unfold Box.cube
  exact h

/-! ### R4. `dsimp only` · goal: a field of a constructor value → the value stored there
`{ toRect := r, d := v }.toRect` → `r` and `{ toRect := r, d := v }.d` → `v`. -/
example (r : Rect) (v : Int) (P : Rect → Prop) (h : P r) :
    P ({ toRect := r, d := v } : Box).toRect := by
  dsimp only
  exact h

/-! ### R5. `dsimp only` on an INHERITED field · goal: `{ toRect := r, d := v }.w` → `r.w`
`b.w` for `b : Box` is really `b.toRect.w`; Lean prints both as `b.w`. -/
example (r : Rect) (v : Int) (P : Int → Prop) (h : P r.w) :
    P ({ toRect := r, d := v } : Box).w := by
  dsimp only
  exact h

/-! ### R6. `rfl` · closes `a = b` when both sides agree after unfolding definitions and
reducing projections: it does R3, R4 and R5 by itself. -/
example (r : Rect) : (Box.cube r).d = r.w := by
  rfl

/-! ## Arithmetic clean-up -/

/-! ### R7. `Int.mul_zero` · `∀ (a : Int), a * 0 = 0` · goal: `a * 0` → `0` -/
example (a : Int) (P : Int → Prop) (h : P 0) : P (a * 0) := by
  rw [Int.mul_zero]
  exact h

/-! ### R8. `Int.add_zero` · `∀ (a : Int), a + 0 = a` · goal: `a + 0` → `a` -/
example (a : Int) (P : Int → Prop) (h : P a) : P (a + 0) := by
  rw [Int.add_zero]
  exact h

/-! ### R9. `simp [D₁, D₂]` · goal: unfolds `D₁, D₂`, reduces projections, applies R7, R8 and the
other default simp lemmas; closes the goal if both sides then agree -/
example (r : Rect) (P : Int → Prop) (h : P (r.w * r.h * r.w)) : P (Box.cube r).vol := by
  simp [Box.vol, Box.cube]
  exact h

/-! # Part W · Worked combinations (on `Rect` and `Box`, not the exercise's structures) -/

/-! ### W1. Three ways to write a `Box` (R1, R2, and flat field syntax through `extends`) -/
example : Box := { w := 1, h := 2, d := 3 }
example (r : Rect) : Box := { r with d := 0 }
example (r : Rect) : Box := ⟨r, 0⟩

/-! ### W2. The volume of a flat box by hand: R3 (two names), R4/R5, then R7 -/
example (r : Rect) : (Box.flat r).vol = 0 := by
  unfold Box.vol Box.flat
  dsimp only
  rw [Int.mul_zero]

/-! ### W3. The same in one step (R9) -/
example (r : Rect) : (Box.flat r).vol = 0 := by
  simp [Box.vol, Box.flat]

end E053Guide
