/- Guide for E029 (Constructor injectivity).
Part R: one reference entry per tactic, term or fact the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`G` is an arbitrary goal (a `Prop`) when the step does not look at the goal; a hypothesis `k` in an
entry is only there to finish the example; it shows what the context became.
All entries use the guide's type `T` below, NOT the exercise's `Shape`.
Part W: worked combinations on `Option`, pairs and `T`.
Assumed: Lean basics up to E028, in particular `intro`/`exact`/`apply` (E003), anonymous
constructors `⟨_, _⟩` (E004), `∧` (E005), `¬` and `False` (E008), `simp at h` (E010), lists and
`::` (E015), and `inductive` types with constructors (E018).
-/

namespace E029Guide

/-- A type with three constructors: no argument, one argument, two arguments. -/
inductive T (α : Type) where
  | leaf
  | one (a : α)
  | two (a b : α)

/-! # Part R · Reference entries -/

/-! ## Equal constructors ⇒ equal arguments -/

/-! ### R1. `injection h` · context gains `a_eq✝ : a = b` (unnamed); closes the goal if it is that equation
`h : T.one a = T.one b` says two values built by the SAME constructor are equal. Constructors are
injective, so their arguments are equal: `injection h` adds `a = b`. With no names given, the new
hypothesis is inaccessible (`a_eq✝`: you cannot type its name). `injection` then tries `assumption`
itself: if the goal is exactly one of the new equations, the goal closes on the spot.
`assumption` closes a goal that some hypothesis states exactly, inaccessible ones included. -/
example {α : Type} (a b : α) (G : Prop) (k : a = b → G) (h : T.one a = T.one b) : G := by
  injection h
  apply k
  assumption

/-! ### R2. `injection h with h1 h2` · context gains `h1 : a = c`, `h2 : b = d` (named)
One equation per constructor argument, named left to right by the `with` list. -/
example {α : Type} (a b c d : α) (G : Prop) (k : a = c → b = d → G)
    (h : T.two a b = T.two c d) : G := by
  injection h with h1 h2
  exact k h1 h2

/-! ### R3. `exact ⟨h1, h2⟩` · closes `A ∧ B` from `h1 : A`, `h2 : B` (anonymous constructor, E004) -/
example (A B : Prop) (h1 : A) (h2 : B) : A ∧ B := by
  exact ⟨h1, h2⟩

/-! ## Different constructors are never equal -/

/-! ### R4. `intro h` on `x ≠ y` · goal → `False`, context gains `h : x = y`
`x ≠ y` is notation for `¬(x = y)`, and `¬p` is `p → False`; so `≠` is an implication and `intro`
applies to it. -/
example {α : Type} (a b : α) (k : T.leaf = T.two a b → False) : T.leaf ≠ T.two a b := by
  intro h
  exact k h

/-! ### R5. `nomatch h` · closes ANY goal when `h : C₁ … = C₂ …` with different constructors `C₁`, `C₂`
`nomatch h` is a `match` on `h` with zero arms: Lean checks that no case is possible, because an
equation between different constructors has no proof. (`injection h` closes such a goal too.) -/
example {α : Type} (a b : α) (G : Prop) (h : T.leaf = T.two a b) : G := by
  nomatch h

/-! ### R6. `nofun` · closes `C₁ … ≠ C₂ …` (a term: write `:= nofun`)
`nofun` is `fun h => nomatch h`: a function with no arms, accepted because no argument
`h : C₁ … = C₂ …` can exist. It works on any goal `x ≠ y` or `x = y → False` between different
constructors. -/
example {α : Type} (a : α) : T.leaf ≠ T.one a := by
  exact nofun

/-! ## Lists -/

/-! ### R7. `::` is a constructor · `injection` and `nofun` work on lists
`a :: l` is notation for `List.cons a l`; `[]` is `List.nil`, and `[a]` is `a :: []`. So
`h : a :: l = b :: m` is an equation between two `List.cons` values. -/
example {α : Type} (a b : α) (l m : List α) (G : Prop) (k : a = b → l = m → G)
    (h : a :: l = b :: m) : G := by
  injection h with e1 e2
  exact k e1 e2

/-! ## Another route: `simp` knows injectivity -/

/-! ### R8. `simp at h` · context: `h : T.two a b = T.two c d` becomes `h : a = c ∧ b = d`
For every constructor Lean generates `T.two.injEq : (T.two a b = T.two a' b') = (a = a' ∧ b = b')`,
a `simp` lemma; `simp` also turns an equation between different constructors into `False`. -/
example {α : Type} (a b c d : α) (G : Prop) (k : a = c ∧ b = d → G)
    (h : T.two a b = T.two c d) : G := by
  simp at h
  exact k h

/-! # Part W · Worked combinations (on `Option`, pairs and `T`, not the exercise's `Shape`) -/

/-! ### W1. `injection` alone closes the goal when the goal is the argument equation (R1) -/
example (a b : Nat) (h : some a = some b) : a = b := by
  injection h

/-! ### W2. A pair `(a, b)` is `Prod.mk a b`: R2 then R3 -/
example (a b c d : Nat) (h : (a, b) = (c, d)) : b = d ∧ a = c := by
  injection h with h1 h2
  exact ⟨h2, h1⟩

/-! ### W3. Refuting a clash: R4 + R5 in tactic mode, or R6 as a term -/
example (n : Nat) : none ≠ some n := by
  intro h
  nomatch h

example (x : Nat) (xs : List Nat) : [] ≠ x :: xs := nofun

/-! ### W4. Injection twice: `T.one (T.one a)`, constructors nested -/
example (a b : Nat) (h : T.one (T.one a) = T.one (T.one b)) : a = b := by
  injection h with h1
  injection h1

end E029Guide
