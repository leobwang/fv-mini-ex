/- Guide for M007 (Subtypes).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on the toy subtype `Pos` below, which is NOT the exercise's.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M007Guide

/-! ## Toy objects used by the entries (not the exercise's) -/

/-- `Pos`: the positive naturals, as a subtype. A value is a pair `⟨n, h⟩` of a number `n` and a
proof `h : 0 < n`. `abbrev` (not `def`) lets Lean see through the name, so `Pos` is literally
`{n : Nat // 0 < n}` everywhere. -/
abbrev Pos := {n : Nat // 0 < n}

/-- Build a `Pos` from a `Pos`: the new number, then a proof about it. -/
def double (p : Pos) : Pos := ⟨2 * p.val, by have := p.property; omega⟩

/-- Read a `Pos` back as a plain number. -/
def pred (p : Pos) : Nat := p.val - 1

/-- Build a `Pos` from a plain number; the proof needs no hypothesis. -/
def succPos (n : Nat) : Pos := ⟨n + 1, by omega⟩

/-! # Part R · Reference entries -/

/-! ## Building and taking apart a subtype value -/

/-! ### R1. `⟨v, h⟩`, in tactic form `refine ⟨v, ?_⟩` · goal `{ a // P a }` → goal `P v`
A value of `{a : α // P a}` is a value `v : α` together with a proof of `P v`. In a `def` body write
`⟨v, by tac⟩`: the `by` block sees exactly the goal `P v` shown after `refine`. -/
example {α : Type} (P : α → Prop) (v : α) (hv : P v) : {a : α // P a} := by
  refine ⟨v, ?_⟩
  exact hv

/-! ### R2. `have h := x.property` · context gains `h : P x.val`; goal unchanged
`x.val` (also `x.1`) is the number inside `x`; `x.property` (also `x.2`) is the proof about it.
`have h := e` names the fact so every later tactic sees it. -/
example {α : Type} (P : α → Prop) (x : {a : α // P a}) (G : Prop) (g : P x.val → G) : G := by
  have h := x.property
  exact g h

/-! ### R3. `omega` · closes linear arithmetic over `Nat` and `Int`, using the context
It knows `+`, truncated `-`, `*` by a numeral, and `/` and `%` by a numeral, with `=`, `≤`, `<`, `≠`.
It reads hypotheses such as `h : n % 3 = 0` from the context. -/
example (n : Nat) (h : n % 3 = 0) : 3 * (n / 3) = n := by
  omega

/-- R3 on a subtype: in this Lean version `omega` also adds `p.property` by itself for every
atom `p.val` of a subtype it meets. Other tactics (`simp`, `exact`, `decide`) do not; R2 does. -/
example (p : Pos) : p.val ≠ 0 := by
  omega

/-! ## Computing with `.val` -/

/-! ### R4. `rfl` · closes `.val` of a constructor, through definitions
`⟨v, hv⟩.val` reduces to `v` by computation (the projection of a pair), so `rfl` closes it, also
when `⟨v, hv⟩` is hidden behind a `def` such as `double`. -/
example {α : Type} (P : α → Prop) (v : α) (hv : P v) : (⟨v, hv⟩ : {a : α // P a}).val = v := by
  rfl

example (p : Pos) : (double p).val = 2 * p.val := by
  rfl

/-! ### R5. `simp only [f]` · goal: the name `f` → its body, and `⟨v, hv⟩.val` → `v`
`simp only [f]` unfolds `f`; `simp` always reduces a projection of a constructor, so the `.val` of
the anonymous constructor disappears (third example: `simp only` with no names). -/
example (p : Pos) (P : Nat → Prop) (h : P (2 * p.val)) : P (double p).val := by
  simp only [double]
  exact h

example (p : Pos) (P : Nat → Prop) (h : P (p.val - 1)) : P (pred p) := by
  simp only [pred]
  exact h

example {α : Type} (P : α → Prop) (v : α) (hv : P v) (R : α → Prop) (h : R v) :
    R (⟨v, hv⟩ : {a : α // P a}).val := by
  simp only
  exact h

/-! ## Equality of subtype values -/

/-! ### R6. `apply Subtype.ext` · goal `x = y` → goal `x.val = y.val`
`Subtype.ext : a1.val = a2.val → a1 = a2`. The proofs inside need not be compared: any two proofs
of the same `Prop` are equal (proof irrelevance). -/
example {α : Type} (P : α → Prop) (x y : {a : α // P a}) (h : x.val = y.val) : x = y := by
  apply Subtype.ext
  exact h

/-! # Part W · Worked combinations (on `Pos`, not the exercise's subtype) -/

/-! ### W1. Unfold a number-valued and a `Pos`-valued definition, then arithmetic: R5 → R3 -/
example (p : Pos) : pred (double p) + 1 = 2 * p.val := by
  simp only [pred, double]
  omega

/-! ### W2. An equation between `Pos` values: R6 → R2 → R5 → R3 -/
example (p : Pos) : succPos (pred p) = p := by
  apply Subtype.ext
  have h := p.property
  simp only [succPos, pred]
  omega

end M007Guide
