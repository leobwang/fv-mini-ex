/- Guide for M013 (Type-safe sprintf).
Part R: one reference entry per tactic, term construct or library lemma the exercise needs, stated
with typed placeholders. Put the cursor before and after the step to see the proof state change in
the infoview. `P` stands for "the rest of your goal": the step changes only the part shown inside
`P (…)`. A hypothesis `h` (or `h0`, `h1`, `k`) in an entry is only there to finish the example; it
shows what the goal became.
The entries use the toy family below, indexed by a number `n` instead of a format list, NOT the
exercise's `Fmt`: `Arity n` is the type of a function that takes `n` strings and returns a string,
`Tup n` is a tuple of `n` strings.
Part W: worked combinations on `Arity` and `Tup`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M013Guide

/-! # The toy family used by the entries -/

/-- `Arity n = String → … → String → String` with `n` arguments: a type computed by recursion. -/
def Arity : Nat → Type
  | 0 => String
  | n + 1 => String → Arity n

/-- `Tup n = String × (String × … × Unit)`: `n` strings in nested pairs, ending in `()`. -/
def Tup : Nat → Type
  | 0 => Unit
  | n + 1 => String × Tup n

/-- Feed a tuple to a curried function: `call 2 f (a, b, ()) = f a b`. -/
def call : (n : Nat) → Arity n → Tup n → String
  | 0, r, () => r
  | n + 1, f, (s, t) => call n (f s) t

/-- Concatenate the strings of a tuple. -/
def concat : (n : Nat) → Tup n → String
  | 0, () => ""
  | n + 1, (s, t) => s ++ concat n t

/-! # Part R · Reference entries -/

/-! ## Writing a function whose type is computed -/

/-! ### R1. `fun | p₁, q₁ => e₁ | p₂, q₂ => e₂` · goal list: one goal per arm, each with its own type
A `fun` with `|` arms matches on several arguments at once. In each arm the result type is the
declared one with the patterns plugged in: `Arity 0` in the first arm, `Arity (n + 1)` in the second.
`refine` with `?_` holes shows those types as goals; in a definition you write the arm bodies. -/
example (h0 : String → Arity 0) (h1 : (n : Nat) → String → Arity (n + 1)) :
    (n : Nat) → String → Arity n := by
  refine fun
    | 0, acc => ?_
    | n + 1, acc => ?_
  exact h0 acc
  exact h1 n acc

/-! ### R2. `show T'` · goal: `T` replaced by a type `T'` that it reduces to
`Arity (n + 1)` reduces by the second equation of `Arity` to `String → Arity n`. Lean accepts any
term whose type agrees after such reductions (definitional equality); `show` only makes it visible. -/
example (n : Nat) (k : String → Arity n) : Arity (n + 1) := by
  show String → Arity n
  exact k

/-! ### R3. `exact acc` with `acc : String` · closes `⊢ Arity 0`, because `Arity 0` reduces to `String` -/
example (acc : String) : Arity 0 := by
  exact acc

/-! ### R4. `intro s` (as a term: `fun s => …`) · goal `Arity (n + 1)` → context gains `s : String`, goal `Arity n`
`intro` reduces the goal until it sees the `→`. In a definition the same arm is written `fun s => e`
with `e : Arity n`. -/
example (n : Nat) (k : String → Arity n) : Arity (n + 1) := by
  intro s
  exact k s

/-! ### R5. `toString (n : Nat) : String` and `s₁ ++ s₂` · `rfl` closes a goal that evaluates
`toString` turns a number into its decimal digits; `++` appends strings. On literals both compute. -/
example : "x=" ++ toString (42 : Nat) = "x=42" := by
  rfl

/-! ## Proving it: generalise, induct, split the arguments -/

/-! ### R6. `have key : ∀ m acc, Q m acc := …` · context gains the general statement
A statement about the start value `""` of an accumulator is usually not provable by induction;
prove it for every `acc` first, then instantiate. -/
example (Q : Nat → String → Prop) (n : Nat) (hgen : ∀ acc m, Q m acc) : Q n "" := by
  have key : ∀ (m : Nat) (acc : String), Q m acc := fun m acc => hgen acc m
  exact key n ""

/-! ### R7. `intro xs` then `induction xs with | nil => … | cons x xs ih => …` · goal list and context
Introduce only the list. The rest of the `∀` stays in the goal, so the induction hypothesis `ih` is
still `∀ acc, …` and can be used at another accumulator. -/
example {α : Type} (Q : List α → String → Prop) (hn : ∀ acc, Q [] acc)
    (hc : ∀ x xs, (∀ acc, Q xs acc) → ∀ acc, Q (x :: xs) acc) :
    ∀ (xs : List α) (acc : String), Q xs acc := by
  intro xs
  induction xs with
    | nil => ?_
    | cons x xs ih => ?_
  exact hn
  exact hc x xs ih

/-! ### R8. `cases t` on `t : Tup 0` · context loses `t`; the goal gets `PUnit.unit` (the value `()`)
`Tup 0` reduces to `Unit`, whose only value is `()`, printed `PUnit.unit`. After this, defining
equations that match on `()` can fire. -/
example (P : Tup 0 → Prop) (h : P ()) (t : Tup 0) : P t := by
  cases t
  exact h

/-! ### R9. `cases o with | none => … | some a => …` · goal list: one goal per constructor, no IH
A case split on the head constructor. For a type with three constructors you write three arms. -/
example {α : Type} (P : Option α → Prop) (h0 : P none) (h1 : ∀ a, P (some a)) (o : Option α) :
    P o := by
  cases o with
    | none => ?_
    | some a => ?_
  exact h0
  exact h1 a

/-! ### R10. `obtain ⟨s, u⟩ := t` on `t : Tup (n + 1)` · context: `t` → its two components
`Tup (n + 1)` reduces to `String × Tup n`, so `t` is a pair; the goal now mentions `(s, u)`. -/
example (n : Nat) (P : Tup (n + 1) → Prop) (h : ∀ s u, P (s, u)) (t : Tup (n + 1)) : P t := by
  obtain ⟨s, u⟩ := t
  exact h s u

/-! ### R11. `simp only [call]` · goal: a defining equation fires once the arguments are constructors
`call (n + 1) f (s, t) = call n (f s) t` is an equation of `call`; it needs the pair `(s, t)`
literally, which is why R8 / R10 come first. -/
example (n : Nat) (f : Arity (n + 1)) (s : String) (t : Tup n) (P : String → Prop)
    (h : P (call n (f s) t)) : P (call (n + 1) f (s, t)) := by
  simp only [call]
  exact h

/-! ### R12. `simp only [ih]` with `ih : ∀ acc m, F acc m = acc ++ G m` · goal: rewrite at any `acc`
`simp` (and `rw`) instantiate the `∀` of an equation to match the goal: here `acc := a ++ "x"`. -/
example (F : String → Nat → String) (G : Nat → String) (a : String) (k : Nat)
    (ih : ∀ acc m, F acc m = acc ++ G m) (P : String → Prop) (h : P (a ++ "x" ++ G k)) :
    P (F (a ++ "x") k) := by
  simp only [ih]
  exact h

/-! ### R13. `String.append_assoc` · `s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃)` · goal: regroup `++` -/
example (a b c : String) (P : String → Prop) (h : P (a ++ (b ++ c))) : P (a ++ b ++ c) := by
  rw [String.append_assoc]
  exact h

/-! ### R14. `String.append_empty`, `String.empty_append` · `s ++ "" = s`, `"" ++ s = s` · goal
Both are `simp` lemmas: plain `simp` uses them without being told. -/
example (a : String) (P : String → Prop) (h : P a) : P (a ++ "") := by
  rw [String.append_empty]
  exact h

example (a : String) (P : String → Prop) (h : P a) : P ("" ++ a) := by
  rw [String.empty_append]
  exact h

/-! ### R15. `Nat.toString_eq_repr` · `toString n = n.repr` · goal: what `simp` turns `toString n` into
Also a `simp` lemma. `n.repr` (`Nat.repr n`) is the same string; it appears on both sides, so it is harmless. -/
example (n : Nat) (P : String → Prop) (h : P (Nat.repr n)) : P (toString n) := by
  rw [Nat.toString_eq_repr]
  exact h

/-! # Part W · Worked combinations (on `Arity` and `Tup`, not the exercise's `Fmt`) -/

/-! ### W1. A function of type `Arity n`: R1 arms, R3 in the base arm, R4 + R5 in the step arm
`catAux n acc` takes `n` more strings and returns `acc` followed by them. The step arm calls
`catAux` on the smaller `n`: structural recursion, accepted without a termination proof. -/
def catAux : (n : Nat) → String → Arity n := fun
  | 0, acc => acc
  | n + 1, acc => fun s => catAux n (acc ++ s)

example : call 2 (catAux 2 "<") ("a", "b", ()) = "<ab" := by
  rfl

/-! ### W2. The accumulator lemma, then the `""` case: R6, R7 (on `Nat`), R8, R10, R11 → R12 → R13, R14 -/
example (n : Nat) (t : Tup n) : call n (catAux n "") t = concat n t := by
  have key : ∀ (n : Nat) (acc : String) (t : Tup n), call n (catAux n acc) t = acc ++ concat n t := by
    intro n
    induction n with
    | zero =>
      intro acc t
      cases t
      simp [catAux, call, concat]
    | succ n ih =>
      intro acc t
      obtain ⟨s, u⟩ := t
      simp [catAux, call, concat, ih, String.append_assoc]
  simp [key]

end M013Guide
