/- Guide for M009 (A monoid class with laws).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use their own class `Absorb` (a commutative operation `op` with an absorbing element
`zero`: `op zero a = zero`), instantiated on `Nat` with `min` and `0`, and their own list function
`total` (the sum of a list). Neither is the exercise's `MyMonoid` / `mconcat`.
Part W: worked combinations on `Absorb` and `total`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M009Guide

/-- A class whose last two fields are proofs: every instance must supply them. -/
class Absorb (α : Type) where
  op : α → α → α
  zero : α
  op_comm : ∀ a b : α, op a b = op b a
  zero_op : ∀ a : α, op zero a = zero

/-- The sum of a list, by structural recursion on the list. -/
def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

/-! # Part R · Reference entries -/

/-! ## Building an instance: data fields, then one proof per law -/

/-! ### R1. `refine { op := f, zero := z, op_comm := ?_, zero_op := ?_ }` · goal list: an instance → one goal per proof field
Giving the data fields fixes what `op` and `zero` are; each law left as `?_` becomes a goal with `f`
and `z` substituted for `op` and `zero`. This is the obligation you meet inside `op_comm := by …`. -/
example {α : Type} (f : α → α → α) (z : α) (hc : ∀ a b, f a b = f b a) (hz : ∀ a, f z a = z) :
    Absorb α := by
  refine { op := f, zero := z, op_comm := ?_, zero_op := ?_ }
  exact hc
  exact hz

/-! ### R2. `intro a b` · goal `∀ a b, Q a b` → context gains `a b`, goal `Q a b` -/
example (Q : Nat → Nat → Prop) (h : ∀ a b, Q a b) : ∀ a b : Nat, Q a b := by
  intro a b
  exact h a b

/-! ### R3. `omega` · closes linear arithmetic over `Nat`/`Int`, `min` and `max` included -/
example (a b : Nat) : max a b = max b a := by
  omega

example (a b : Nat) : min a (max a b) = a := by
  omega

/-! ### R4. `instance name : C T where field := value …` · declares the instance (R1–R3 together)
After this, `Absorb.op a b` with `a b : Nat` means `min a b`: Lean finds the instance by the type.
The same instance in brace syntax: `{ op := min, zero := 0, op_comm := by …, zero_op := by … }`. -/
instance instMinAbsorb : Absorb Nat where
  op := min
  zero := 0
  op_comm := by intro a b; omega
  zero_op := by intro a; omega

/-! ## Using a concrete instance -/

/-! ### R5. `rfl` · closes `C.op a b = g a b` when the instance for that type sets `op := g`
`Absorb.op a b` unfolds (instance → its field) to `min a b`; both sides are then the same term. -/
example (a b : Nat) : Absorb.op a b = min a b := by
  rfl

/-! ### R6. `rfl` / `decide` · closes an equation of closed terms by evaluation, through the instance -/
example : Absorb.op (Absorb.op 5 3) 8 = 3 := by
  rfl

example : List.foldr min 9 [4, 2, 7] = 2 := by
  decide

/-! ## Induction on lists -/

/-! ### R7. `induction xs with | nil => … | cons x xs ih => …` · goal list: two goals; `cons` adds `x xs ih`
`?_` leaves a case open so both goals appear; in a proof, write tactics there instead. -/
example {α : Type} (P : List α → Prop) (h0 : P []) (hs : ∀ x xs, P xs → P (x :: xs))
    (xs : List α) : P xs := by
  induction xs with
    | nil => ?_
    | cons x xs ih => ?_
  exact h0
  exact hs x xs ih

/-! ### R8. `List.nil_append` · `[] ++ as = as` · goal -/
example {α : Type} (ys : List α) (P : List α → Prop) (h : P ys) : P ([] ++ ys) := by
  rw [List.nil_append]
  exact h

/-! ### R9. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`x :: xs ++ ys` is `(x :: xs) ++ ys`: `++` binds weaker than `::`. -/
example {α : Type} (x : α) (xs ys : List α) (P : List α → Prop) (h : P (x :: (xs ++ ys))) :
    P (x :: xs ++ ys) := by
  rw [List.cons_append]
  exact h

/-! ### R10. `simp only [f]` · goal: `f []` and `f (x :: xs)` → the right sides of `f`'s equations -/
example (x : Nat) (xs : List Nat) (P : Nat → Prop) (h : P 0 ∧ P (x + total xs)) :
    P (total []) ∧ P (total (x :: xs)) := by
  simp only [total]
  exact h

/-! ### R11. `rw [ih]` · goal: the induction hypothesis `ih : f xs = b` used as a rewrite rule -/
example {α β : Type} (f : List α → β) (b : β) (xs : List α) (ih : f xs = b) (P : β → Prop)
    (h : P b) : P (f xs) := by
  rw [ih]
  exact h

/-! ## Generic proofs over `[Absorb α]` -/

/-! ### R12. `rw [C.law]` · goal: a class law used as a rewrite rule, in any instance
`Absorb.zero_op : ∀ {α : Type} [self : Absorb α] (a : α), Absorb.op Absorb.zero a = Absorb.zero`.
Arguments may be given explicitly to pick one occurrence: `rw [Absorb.op_comm a b]`. -/
example {α : Type} [Absorb α] (a : α) (P : α → Prop) (h : P Absorb.zero) :
    P (Absorb.op Absorb.zero a) := by
  rw [Absorb.zero_op]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A generic fact from two laws: R12 with explicit arguments, then R12 -/
example {α : Type} [Absorb α] (a : α) : Absorb.op a Absorb.zero = Absorb.zero := by
  rw [Absorb.op_comm a Absorb.zero]
  rw [Absorb.zero_op]

/-! ### W2. `total` turns `++` into `+`: R7, then R8, R10 / R9, R10, R11, and `omega` (R3) -/
example (xs ys : List Nat) : total (xs ++ ys) = total xs + total ys := by
  induction xs with
    | nil =>
      rw [List.nil_append]
      simp only [total]
      omega
    | cons x xs ih =>
      rw [List.cons_append]
      simp only [total]
      rw [ih]
      omega

end M009Guide
