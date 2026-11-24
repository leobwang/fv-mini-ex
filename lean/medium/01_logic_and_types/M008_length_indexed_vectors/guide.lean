/- Guide for M008 (Length-indexed vectors).
Part R: one reference entry per tactic, construct or library lemma the exercise needs, stated with
typed placeholders. Put the cursor before and after the step to see the proof state change in the
infoview. `P` stands for "the rest of your goal": the step changes only the part shown inside
`P (…)`. A hypothesis `h` in an entry is only there to finish the example; it shows what the goal
became.
Part W: worked combinations on the toy type `Bits` below, which is NOT the exercise's `Vec`.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M008Guide

/-! ## Toy objects used by the entries (not the exercise's) -/

/-- `Bits n`: a string of exactly `n` booleans. The length `n` is an *index*: it is part of the
type and differs per constructor (`e` has length `0`, `b bit rest` has length `n + 1`). -/
inductive Bits : Nat → Type
  | e : Bits 0
  | b {n : Nat} (bit : Bool) (rest : Bits n) : Bits (n + 1)

/-- Forget the length: the booleans as a list. -/
def Bits.toList {n : Nat} : Bits n → List Bool
  | .e => []
  | .b bit rest => bit :: rest.toList

/-- Drop the first bit. Total: a `Bits (n + 1)` cannot be `e` (R1). -/
def Bits.tail {n : Nat} (v : Bits (n + 1)) : Bits n :=
  match v with
  | .b _ rest => rest

/-- Negate every bit. Structural recursion: the call `rest.flip` is on the smaller `rest` (R4). -/
def Bits.flip {n : Nat} (v : Bits n) : Bits n :=
  match v with
  | .e => .e
  | .b bit rest => .b (!bit) rest.flip

/-! # Part R · Reference entries -/

/-! ## Defining functions by dependent pattern matching -/

/-! ### R1. `match v with | .b bit rest => …` on `v : Bits (n + 1)` · goal list: one branch
Only `b` can build a `Bits (n + 1)` (`e` has index `0`, and `0 ≠ n + 1`), so one alternative is a
complete match. The branch's context gains the constructor's arguments. In a `def` you write the
same `match` as the body; `refine match … => ?_` shows its branch as a goal. -/
example {n : Nat} (v : Bits (n + 1)) : Bits n := by
  refine match v with | .b bit rest => ?_
  exact rest

/-! ### R2. `match v with | .e => … | .b bit rest => …` on `v : Bits n` · goal list: two branches,
the index refined in each. The result type `Bits n` mentions the index, so each branch must build a
`Bits 0` (for `e`) or a `Bits (n✝ + 1)` (for `b`, where `rest : Bits n✝`). `n✝` is the inaccessible
name of the constructor's implicit `{n : Nat}`. -/
example {n : Nat} (v : Bits n) : Bits n := by
  refine match v with
    | .e => ?_
    | .b bit rest => ?_
  exact .e
  exact .b (!bit) rest

/-! ### R3. `.e`, `.b x r` (constructor dot notation) · closes the goal
`.b x r` means `Bits.b x r`: Lean reads the namespace `Bits` off the expected type. The implicit
index `{n}` of `b` is inferred from `r`. -/
example {n : Nat} (x : Bool) (r : Bits n) : Bits (n + 1) := by
  exact .b x r

/-! ### R4. The recursive call `rest.flip` · closes the goal
`rest.flip` is `Bits.flip rest` (dot notation on a value). Inside the definition of `Bits.flip`
the call is allowed because `rest` is a sub-term of `v` (structural recursion); it has type
`Bits n✝`, and `.b` lifts it back to `Bits (n✝ + 1)`. -/
example {n : Nat} (bit : Bool) (rest : Bits n) : Bits (n + 1) := by
  exact .b (!bit) rest.flip

/-! ### R5. Index arithmetic by computation: `show` · goal: replaced by a definitionally equal one
`Nat.add` recurses on its SECOND argument: `m + 0` computes to `m` and `m + (n + 1)` to
`(m + n) + 1`. So a value of type `P (m + n + 1)` already has type `P (m + (n + 1))`. The first
argument does not compute: `(n + 1) + m` is not `(n + m) + 1` by computation (only by a lemma). -/
example (m n : Nat) (P : Nat → Type) (x : P (m + n + 1)) : P (m + (n + 1)) := by
  show P (m + n + 1)
  exact x

example (m : Nat) (P : Nat → Type) (x : P m) : P (m + 0) := by
  show P m
  exact x

/-! ## Proving facts about such functions -/

/-! ### R6. `rfl` · closes an equation that holds by computation
A `def` by `match` applied to a constructor reduces, so `(Bits.b x r).tail` is `r` by
computation. The same closes `nil`-style cases: `Bits.e.toList` is `[]` and `[] ++ l` is `l`. -/
example {n : Nat} (x : Bool) (r : Bits n) : (Bits.b x r).tail = r := by
  rfl

example {n : Nat} (w : Bits n) : Bits.e.toList ++ w.toList = w.toList := by
  rfl

/-! ### R7. `induction v` on `v : Bits n` · goal list: one goal per constructor, index refined
`P : (n : Nat) → Bits n → Prop` is "the statement", which may mention the index. Case `e` gets
index `0`; case `b` gets index `n✝ + 1` and the induction hypothesis `rest_ih✝` for `rest✝`.
Write `induction v with | e => … | b bit rest ih => …` to name them. Below, `‹_›` means "the
hypothesis whose type fits here": the only way to cite the unnamed `rest_ih✝`. -/
example (P : (n : Nat) → Bits n → Prop) (h0 : P 0 .e)
    (hs : ∀ n x r, P n r → P (n + 1) (.b x r)) {n : Nat} (v : Bits n) : P n v := by
  induction v
  exact h0
  exact hs _ _ _ ‹_›

/-- R7 with names: the same proof, the alternatives written out. -/
example (P : (n : Nat) → Bits n → Prop) (h0 : P 0 .e)
    (hs : ∀ n x r, P n r → P (n + 1) (.b x r)) {n : Nat} (v : Bits n) : P n v := by
  induction v with
    | e => exact h0
    | b bit rest ih => exact hs _ bit rest ih

/-! ### R8. `simp only [Bits.toList]` · goal: one step of a definition on a constructor
`simp [D]` with a `def D` given by pattern matching rewrites `D (constructor …)` by the matching
equation. Here `(Bits.b x r).toList` becomes `x :: r.toList`. -/
example {n : Nat} (x : Bool) (r : Bits n) (P : List Bool → Prop) (h : P (x :: r.toList)) :
    P (Bits.b x r).toList := by
  simp only [Bits.toList]
  exact h

/-! ### R9. `List.length_cons` · `(a :: l).length = l.length + 1` · goal (`simp` uses it by itself) -/
example {α : Type} (a : α) (l : List α) (P : Nat → Prop) (h : P (l.length + 1)) :
    P (a :: l).length := by
  rw [List.length_cons]
  exact h

/-! ### R10. `List.map_cons` · `(a :: l).map f = f a :: l.map f` · goal (`simp` uses it by itself)
Lean prints `l.map f` as `List.map f l`. -/
example {α β : Type} (f : α → β) (a : α) (l : List α) (P : List β → Prop)
    (h : P (f a :: l.map f)) : P ((a :: l).map f) := by
  rw [List.map_cons]
  exact h

/-! ### R11. `List.cons_append` · `(a :: as) ++ bs = a :: (as ++ bs)` · goal (`simp` uses it by itself) -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P ((a :: as) ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R12. `simp [ih]` · rewrites with a hypothesis `ih : l = l'` left to right, then closes
the goal if both sides become equal (`a :: l' = a :: l'`). -/
example {α : Type} (a : α) (l l' : List α) (ih : l = l') : a :: l = a :: l' := by
  simp [ih]

/-! # Part W · Worked combinations (on `Bits`, not the exercise's `Vec`) -/

/-! ### W1. Index arithmetic in a definition (R2-style match, R5): pad with `k` leading `false`s.
The result type is `Bits (n + k)` with `k` SECOND, so both branches type-check by computation:
`n + 0` is `n`, and `n + (k + 1)` is `(n + k) + 1`, the type of `.b false (v.pad k)`. -/
def Bits.pad {n : Nat} : (k : Nat) → Bits n → Bits (n + k)
  | 0, v => v
  | k + 1, v => .b false (v.pad k)

/-! ### W2. Induction on an indexed family, then `simp` with the definitions and the IH (R7, R8, R12) -/
example {n : Nat} (v : Bits n) : v.flip.flip = v := by
  induction v with
    | e => rfl
    | b bit rest ih => simp [Bits.flip, ih]

/-! ### W3. The same pattern for a list fact; `simp` applies R11 by itself -/
example {n : Nat} (k : Nat) (v : Bits n) :
    (v.pad k).toList = List.replicate k false ++ v.toList := by
  induction k with
    | zero => rfl
    | succ k ih => simp [Bits.pad, Bits.toList, ih, List.replicate_succ]

end M008Guide
