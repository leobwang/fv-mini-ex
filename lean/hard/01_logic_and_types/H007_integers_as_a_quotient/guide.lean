/- Guide for H007 (Integers as a quotient of Nat × Nat).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on an object that is NOT the exercise's: the naturals modulo parity
(`Nat / ≡ mod 2`, two classes), built with the same tools.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace H007Guide

/-! # Part R · Reference entries -/

/-! ## An equivalence relation -/

/-! ### R1. `refine ⟨?_, ?_, ?_⟩` on `Equivalence r` · goal → three goals: refl, symm, trans
`Equivalence r` is a structure with three fields; the anonymous constructor fills them in order. -/
example {α : Type} (r : α → α → Prop) (hr : ∀ x, r x x) (hs : ∀ {x y}, r x y → r y x)
    (ht : ∀ {x y z}, r x y → r y z → r x z) : Equivalence r := by
  refine ⟨?_, ?_, ?_⟩
  · exact hr
  · exact hs
  · exact ht

/-! ### R2. `intro x y h` on `∀ {x y}, r x y → Q` · context gains `x y` and `h : r x y`
Curly braces `{x y}` (implicit binders) are introduced by `intro` like ordinary ones. -/
example {α : Type} (r : α → α → Prop) (Q : Prop) (hq : ∀ x y, r x y → Q) :
    ∀ {x y : α}, r x y → Q := by
  intro x y h
  exact hq x y h

/-! ### R3. `unfold D at *` · goal and every hypothesis: the name `D` → its body -/
def Par (m n : Nat) : Prop := m % 2 = n % 2

example (m n : Nat) (h : Par m n) (hq : m % 2 = n % 2 → n % 2 = m % 2) : Par n m := by
  unfold Par at *
  exact hq h

/-! ### R4. `omega` · closes linear arithmetic over `Nat`/`Int`, using the hypotheses in context
Linear: `+`, `-`, numerals, `* k` and `% k` for a numeral `k`. A product of two variables is an
unknown to it (use R8). It does not unfold definitions: `unfold` or `show` first (R3, R13). -/
example (a b c d : Nat) (h1 : a + b = c) (h2 : c + d = a + 5) : b + d = 5 := by
  omega

/-! ### R5. `h.symm` (`Eq.symm`) · closes `b = a` from `h : a = b`
It also works when `h : D x y` for a definition `D` whose body is an equation. -/
example (m n : Nat) (h : Par m n) : Par n m := by
  exact h.symm

/-! ## Elements of a quotient -/

/-! ### R6. `induction x using Quotient.inductionOn with | h a => …` · context: `x : Quotient s` → `a : α`
`Quotient s` is the type of classes of `α` under the setoid `s`; `Quotient.mk s a` is the class of
`a`. Every class is `Quotient.mk s a` for some `a`, so it suffices to prove `P` on those. -/
example {α : Type} {s : Setoid α} (P : Quotient s → Prop) (h : ∀ a, P (Quotient.mk s a))
    (x : Quotient s) : P x := by
  induction x using Quotient.inductionOn with
    | h a => ?_
  exact h a

/-! ### R7. `exact ⟨a, b, rfl⟩` · closes `∃ a b, G a b` by naming both witnesses and a proof
A pair `p` is definitionally `(p.1, p.2)` (`p.fst`, `p.snd` in the infoview), so `rfl` proves it. -/
example {α β : Type} (p : α × β) : ∃ a b, p = (a, b) := by
  exact ⟨p.1, p.2, rfl⟩

/-! ### R8. `grind` · closes goals that need products of variables (ring normalisation + linear
arithmetic + the hypotheses), where `omega` gives up -/
example (a b a' b' c : Nat) (h : a + b' = a' + b) : a * c + b' * c = a' * c + b * c := by
  grind

/-! ## Functions out of a quotient -/

/-! ### R9. `Quotient.lift₂ f ?_` · goal: a two-argument function on classes → the proof that
`f` respects `≈` in both arguments. Argument order: `a₁ b₁ a₂ b₂`, then `a₁ ≈ a₂`, `b₁ ≈ b₂`. -/
example {α β γ : Type} {s₁ : Setoid α} {s₂ : Setoid β} (f : α → β → γ)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂) :
    Quotient s₁ → Quotient s₂ → γ := by
  refine Quotient.lift₂ f ?_
  exact h

/-! ### R10. `intro ⟨a, b⟩` · context: a pair `p : α × β` → its two components -/
example {α β : Type} (P : α × β → Prop) (h : ∀ a b, P (a, b)) : ∀ p : α × β, P p := by
  intro ⟨a, b⟩
  exact h a b

/-! ### R11. `intro (h : T)` · context gains `h`, stated as `T`; `T` must be definitionally the
binder's type. Here `m ≈ n` (for the setoid below) is by definition `m % 2 = n % 2`. -/
instance parSetoid : Setoid Nat := ⟨Par, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

example (Q : Prop) (hq : ∀ m n : Nat, m % 2 = n % 2 → Q) : ∀ m n : Nat, m ≈ n → Q := by
  intro m n (h : m % 2 = n % 2)
  exact hq m n h

/-! ### R12. `apply Quotient.sound` · `Quotient.sound : a ≈ b → Quotient.mk s a = Quotient.mk s b`
· goal: equal classes → related representatives -/
example {α : Type} {s : Setoid α} (a b : α) (h : a ≈ b) : Quotient.mk s a = Quotient.mk s b := by
  apply Quotient.sound
  exact h

/-! ### R13. `show T` · goal restated as a definitionally equal `T` (unfolds `≈`, `(a, b).fst`, …) -/
example (m n : Nat) (h : m % 2 = n % 2) : m ≈ n := by
  show m % 2 = n % 2
  exact h

example {α β : Type} (a : α) (b : β) (P : α → β → Prop) (h : P a b) : P (a, b).fst (a, b).snd := by
  show P a b
  exact h

/-! ### R14. `Quotient.lift f ?_` · goal: a function on classes → the proof that `f` respects `≈` -/
example {α β : Type} {s : Setoid α} (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) :
    Quotient s → β := by
  refine Quotient.lift f ?_
  exact h

/-! ### R15. `omega` over `Int` with casts · `↑a` is a `Nat` cast to `Int`; `omega` handles `↑`,
including the subtraction that a `Nat` could not do -/
example (a b : Nat) (h : a + 2 = b) : (b : Int) - a = 2 := by
  omega

/-! ## Computing and comparing -/

/-! ### R16. `rfl` · closes `Quotient.lift f h (Quotient.mk s a) = f a` (computation rule, by
definition; the same holds for `Quotient.lift₂` on two classes) -/
example {α β : Type} {s : Setoid α} (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) (a : α) :
    Quotient.lift f h (Quotient.mk s a) = f a := by
  rfl

/-! ### R17. `constructor` on `A ↔ B` · goal → two goals `A → B` and `B → A`
Term form: `⟨proof of A → B, proof of B → A⟩`. -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  · exact hab
  · exact hba

/-! ### R18. `Quotient.exact` · `Quotient.mk s a = Quotient.mk s b → a ≈ b` · context gains `a ≈ b` -/
example {α : Type} {s : Setoid α} (a b : α) (h : Quotient.mk s a = Quotient.mk s b) : a ≈ b := by
  have h' := Quotient.exact h
  exact h'

/-! ### R19. `obtain ⟨a, b, rfl⟩ := e` · `e : ∃ a b, x = f a b` · context: `x` is replaced by `f a b`
everywhere and disappears; the pattern `rfl` substitutes the equation. -/
example {α β : Type} (f : α → α → β) (x : β) (e : ∃ a b, x = f a b) (P : β → Prop)
    (h : ∀ a b, P (f a b)) : P x := by
  obtain ⟨a, b, rfl⟩ := e
  exact h a b

/-! ### R20. `rw [e]` with `e : ∀ x y, Q x y ↔ S x y` · goal: the proposition `Q a b` → `S a b` -/
example {α : Type} (Q S : α → α → Prop) (e : ∀ x y, Q x y ↔ S x y) (a b : α) (h : S a b) :
    Q a b := by
  rw [e]
  exact h

/-! ### R21. `rw [e] at h` · context: rewrites hypothesis `h` instead of the goal -/
example {α : Type} (f : α → α) (a b : α) (e : f a = b) (P : α → Prop) (h : P (f a)) : P b := by
  rw [e] at h
  exact h

/-! ### R22. `Int.toNat` with `omega` · `n.toNat : Nat` is `n` if `0 ≤ n`, else `0`; `omega` knows it -/
example (n : Int) (h : 0 ≤ n) : (n.toNat : Int) = n := by
  omega

/-! ### R23. `grind` over `Int` with casts · moves `↑` through `+` and `*` itself, then ring
arithmetic closes the goal -/
example (a b c : Nat) : ((a * b + c : Nat) : Int) - c = (a : Int) * b := by
  grind

/-! # Part W · Worked combinations (parity classes, not the exercise's objects) -/

/-! ### W1. A function on classes: `Quotient.lift₂` + R10 + R11 + R12 + R13 + R4 -/
def Bit : Type := Quotient parSetoid

def Bit.mk (n : Nat) : Bit := Quotient.mk parSetoid n

def Bit.add : Bit → Bit → Bit :=
  Quotient.lift₂ (fun m n => Bit.mk (m + n)) (by
    intro m n m' n' (h1 : m % 2 = m' % 2) (h2 : n % 2 = n' % 2)
    apply Quotient.sound
    show (m + n) % 2 = (m' + n') % 2
    omega)

/-! ### W2. The computation rule makes the defining equation `rfl` (R16) -/
example (m n : Nat) : (Bit.mk m).add (Bit.mk n) = Bit.mk (m + n) := rfl

/-! ### W3. An equation between classes: R6, then R12, R13, R4 -/
example (x : Bit) : x.add x = Bit.mk 0 := by
  induction x using Quotient.inductionOn with
    | h m => ?_
  apply Quotient.sound
  show (m + m) % 2 = 0 % 2
  omega

/-! ### W4. Two classes equal → representatives related: R18, then R11-style restatement -/
example (m n : Nat) (h : Bit.mk m = Bit.mk n) : m % 2 = n % 2 := by
  have h' : m ≈ n := Quotient.exact h
  exact h'

end H007Guide
