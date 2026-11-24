/- Guide for E087 (Unique existence).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`α β : Type` are arbitrary types, `p : α → Prop` is an arbitrary property and `P : α → Prop` stands
for "the rest of the goal". A hypothesis in an entry whose name starts with `h` is only there to
finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033), in particular `rfl` (E001), `intro` and `exact` (E003), `fun` and
anonymous constructors `⟨_, _⟩` (E004, E005, E007), `obtain` (E005, E007), `rw` (E009), `omega` (E011)
and `refine` with `?_` (E031). `linarith` (E035) is explained in R7.
-/
import Mathlib

namespace E087Guide

/-! # Part R · Reference entries -/

/-! ## What `∃!` means -/

/-! ### R1. `unfold ExistsUnique` · goal: `∃! x, p x` → its definition
Mathlib defines `ExistsUnique p` (notation `∃! x, p x`) as `∃ x, p x ∧ ∀ y, p y → y = x`:
some `x` works, and every `y` that works equals `x`. Only for reading; the later steps do not need it. -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) (hu : ∀ y, p y → y = w) : ∃! x, p x := by
  unfold ExistsUnique
  exact ⟨w, hw, hu⟩

/-! ## Proving `∃! x, p x` -/

/-! ### R2. `refine ⟨w, ?_, ?_⟩` · goal list: `∃! x, p x` → "w works" and "only w works"
The anonymous constructor flattens `⟨w, ⟨_, _⟩⟩` to `⟨w, _, _⟩`. Lean leaves the property as the
unreduced function application `(fun x => p x) w`, which means `p w` (R3). -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) (hu : ∀ y, p y → y = w) : ∃! x, p x := by
  refine ⟨w, ?_, ?_⟩
  exact hw
  exact hu

/-! ### R3. `beta_reduce` · goal: `(fun x => p x) w` → `p w`
Mathlib tactic: substitutes the argument into the `fun` (beta reduction). Only for reading:
`exact`, `rfl`, `omega` and `linarith` see through `(fun x => …) w` by themselves. -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) : (fun x => p x) w := by
  beta_reduce
  exact hw

/-! ### R4. `refine ⟨w, rfl, ?_⟩` · goal: `∃! x, …` → only the uniqueness part
When "w works" holds by computation (`rfl`), fill it in directly; one goal is left. -/
example {α β : Type} (f : α → β) (c : α) (hu : ∀ y, f y = f c → y = c) : ∃! x, f x = f c := by
  refine ⟨c, rfl, ?_⟩
  exact hu

/-! ### R5. `intro y hy` · goal `∀ (y : α), (fun x => p x) y → y = w` → `y = w`
The context gains `y : α` and `hy : p y` (`intro` beta-reduces the hypothesis for you). -/
example {α : Type} (p : α → Prop) (w : α) (hu : ∀ y, p y → y = w) :
    ∀ y, (fun x => p x) y → y = w := by
  intro y hy
  exact hu y hy

/-! ### R6. `omega` · closes a linear goal over `ℕ` or `ℤ`, using the hypotheses -/
example (a b y : ℕ) (hy : y + a = b + a) : y = b := by
  omega

/-! ### R7. `linarith` · closes a linear (in)equality over `ℝ` (or `ℚ`), using the hypotheses
`omega` does not work over `ℝ`. `linarith` also proves hypothesis-free numeral facts like
`(2 : ℝ) * 4 = 8`, where `rfl` fails on real numbers. -/
example (a b y : ℝ) (hy : 2 * y + a = b) : y = (b - a) / 2 := by
  linarith

/-! ### R8. `⟨w, hw, fun y hy => …⟩` · a term that closes `∃! x, p x` in one go
The three parts: the witness, the proof that it works, the uniqueness function. Each part may be
`by tac`, e.g. `fun y hy => by linarith`. Unlike `intro` (R5), the `fun` leaves `hy` unreduced:
inside `by` it prints as `hy : (fun x => p x) y`, which still means `p y`. -/
example {α : Type} (p : α → Prop) (w : α) (hw : p w) (hu : ∀ y, p y → y = w) : ∃! x, p x := by
  exact ⟨w, hw, fun y hy => hu y hy⟩

/-! ## Using `h : ∃! x, p x` -/

/-! ### R9. `obtain ⟨x, hx, hu⟩ := h` · context: `h` → `x`, `hx : p x`, `hu : ∀ y, p y → y = x`
`h` is removed. `hu` is printed with the unreduced `(fun x => p x) y`, which means `p y`. -/
example {α : Type} (p : α → Prop) (h : ∃! x, p x) (G : Prop)
    (hG : ∀ x, p x → (∀ y, p y → y = x) → G) : G := by
  obtain ⟨x, hx, hu⟩ := h
  exact hG x hx hu

/-! ### R10. `rw [hu a ha]` · goal: every `a` → `x`
`hu a ha : a = x` (apply the `∀` to `a`, then the implication to `ha : p a`). `rw` rewrites with it,
and closes the goal if it becomes `x = x`. -/
example {α : Type} (p P : α → Prop) (x a : α) (hu : ∀ y, p y → y = x) (ha : p a) (h : P x) :
    P a := by
  rw [hu a ha]
  exact h

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Over `ℕ`: R4, R5, R6 -/
example : ∃! n : ℕ, 2 * n = 8 := by
  refine ⟨4, rfl, ?_⟩
  intro y hy
  omega

/-! ### W2. Over `ℝ`, as one term: R8 with R7 in both proof slots -/
example : ∃! x : ℝ, 3 * x - 2 = 4 :=
  ⟨2, by linarith, fun y hy => by linarith⟩

/-! ### W3. Using uniqueness: R9, then R10 twice; the last `rw` closes `x + 1 = x + 1` -/
example (q : ℤ → Prop) (h : ∃! z, q z) (c d : ℤ) (hc : q c) (hd : q d) : c + 1 = d + 1 := by
  obtain ⟨x, hx, hu⟩ := h
  rw [hu c hc, hu d hd]

end E087Guide
