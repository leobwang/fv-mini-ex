/- Guide for M014 (A hand-built state monad and tree relabelling).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The guide builds its own monads, which are NOT the exercise's: `Box α` (a value in a one-field
structure) and the reader monad `Rd α := Nat → α` (a computation that reads a fixed number `e`).
Part W: worked combinations on those and on a tree `Bin` of unlabelled tips.
Assumed: Lean basics (E001–E033). Core Lean only: no imports.
-/

namespace M014Guide

/-- A value wrapped in a one-field structure: the simplest monad. -/
structure Box (α : Type) where
  val : α

instance boxMonad : Monad Box where
  pure a := ⟨a⟩
  bind m f := f m.val

/-! # Part R · Reference entries -/

/-! ## Building a `LawfulMonad` instance -/

/-! ### R1. `refine LawfulMonad.mk' m ?_ ?_ ?_` · goal list: `LawfulMonad m` → the three monad laws
`LawfulMonad.mk' m id_map pure_bind bind_assoc : LawfulMonad m`. The other five fields of
`LawfulMonad` are `autoParam`s: `mk'` proves them itself (by `intros; rfl`) once the monad's `map`,
`seq`, … are the defaults that `Monad` derives from `pure` and `bind`. -/
example : LawfulMonad Box := by
  refine LawfulMonad.mk' Box ?_ ?_ ?_
  · exact fun _ => rfl
  · exact fun _ _ => rfl
  · exact fun _ _ _ => rfl

/-! ### R2. `intro α β x f` · context gains the binders; goal: the body of the `∀`
`intro` takes the implicit binders `{α β : Type}` too, in order: name them all. -/
example : ∀ {α β : Type} (x : α) (f : α → Box β), pure x >>= f = f x := by
  intro α β x f
  rfl

/-! ### R3. `rfl` · closes an equation whose two sides compute to the same term
`pure x >>= f` unfolds through the instance to `f (⟨x⟩ : Box α).val`, which reduces to `f x`. -/
example {α β : Type} (x : α) (f : α → Box β) : pure x >>= f = f x := by
  rfl

/-! ### R4. `exact fun _ _ => rfl` · closes a `∀` law in one term (R2 then R3)
`fun` skips implicit binders (`{α β}` are filled in by Lean): write one `_` per explicit binder,
here `x` and `f`. With the wrong count you get `Type mismatch … rfl`. -/
example : ∀ {α β : Type} (x : α) (f : α → Box β), pure x >>= f = f x := by
  exact fun _ _ => rfl

/-! ## Induction with a moving counter -/

/-- A binary tree with unlabelled tips (not the exercise's `Tree`). -/
inductive Bin where
  | tip
  | fork (l r : Bin)

/-! ### R5. `induction t generalizing s with | tip => ?_ | fork l r ihl ihr => ?_` · goal list
`generalizing s` puts `s` back under a `∀` first, so both induction hypotheses hold for *every*
start value: `ihl : ∀ (s : Nat), P l s`. Without it, `ihl` speaks only about the one `s` you had. -/
example (P : Bin → Nat → Prop) (htip : ∀ s, P .tip s)
    (hfork : ∀ l r, (∀ s, P l s) → (∀ s, P r s) → ∀ s, P (.fork l r) s) (t : Bin) (s : Nat) :
    P t s := by
  induction t generalizing s with
    | tip => ?_
    | fork l r ihl ihr => ?_
  · exact htip s
  · exact hfork l r ihl ihr s

/-! ### R6. `obtain ⟨h1, h2⟩ := ih a` · context gains both halves of `ih` at the point `a`
`ih a` instantiates the `∀`; the pattern `⟨h1, h2⟩` splits the `∧`. Any term works for `a`,
also a compound one such as `(g x).snd`. -/
example {α : Type} (A B : α → Prop) (a : α) (ih : ∀ x, A x ∧ B x) (P : Prop)
    (h : A a → B a → P) : P := by
  obtain ⟨h1, h2⟩ := ih a
  exact h h1 h2

/-! ## Unfolding a `do` block over a hand-made monad -/

/-- The reader monad: a computation that reads one number `e` (an "environment"). -/
def Rd (α : Type) : Type := Nat → α

instance rdMonad : Monad Rd where
  pure a := fun _ => a
  bind m f := fun e => f (m e) e

def ask : Rd Nat := fun e => e

/-- Sum the environment once per tip. -/
def sumTips : Bin → Rd Nat
  | .tip => ask
  | .fork l r => do
    let a ← sumTips l
    let b ← sumTips r
    return a + b

/-! ### R7. `simp only [g, bind, pure]` · goal: a `do` block applied to a state → plain terms
A `do` block is sugar for `bind m (fun a => …)` ending in `pure`. `g` unfolds the definition at a
constructor, `bind` and `pure` unfold the instance's fields, and `simp only` then β-reduces
`(fun e => …) e`. It also reduces a projection of a pair, `(a, b).snd` → `b` (second example).
Add `at *` to do the same in every hypothesis. -/
example (l r : Bin) (e : Nat) (P : Nat → Prop) (h : P (sumTips l e + sumTips r e)) :
    P (sumTips (.fork l r) e) := by
  simp only [sumTips, bind, pure]
  exact h

example (a b : Nat) (P : Nat → Prop) (h : P b) : P ((fun s => (a, s)) b).snd := by
  simp only []
  exact h

/-! ## Arithmetic and `List.range'` -/

def Bin.leaves : Bin → Nat
  | .tip => 1
  | .fork l r => l.leaves + r.leaves

/-! ### R8. `rw [g]` (or `simp only [g]`) on a pattern-matching `def` · goal: `g (constructor …)` → its case
`g` has one equation per pattern; `rw [g]` uses the one whose pattern matches. -/
example (l r : Bin) (P : Nat → Prop) (h : P (l.leaves + r.leaves)) : P (Bin.fork l r).leaves := by
  rw [Bin.leaves]
  exact h

/-! ### R9. `omega` · closes linear arithmetic over `Nat` and `Int` (`+`, `-`, `*` by numerals, `≤`, `=`)
It treats any other term, such as `l.leaves`, as an unknown number. -/
example (s a b : Nat) : s + a + b = s + (a + b) := by
  omega

/-! ### R10. `List.range'_append_1` · goal: two adjacent ranges → one range
`List.range' s m = [s, s+1, …, s+m-1]` (`m` numbers from `s`).
`List.range'_append_1 : List.range' s m ++ List.range' (s + m) n = List.range' s (m + n)`.
The second start must be literally `s + m`. `simp` uses this lemma by itself. -/
example (s m n : Nat) (P : List Nat → Prop) (h : P (List.range' s (m + n))) :
    P (List.range' s m ++ List.range' (s + m) n) := by
  rw [List.range'_append_1]
  exact h

/-! ### R11. `List.range'_one` · goal: `List.range' s 1 = [s]`; `simp` uses it by itself -/
example (s : Nat) (P : List Nat → Prop) (h : P [s]) : P (List.range' s 1) := by
  rw [List.range'_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A `LawfulMonad` instance as one term: R1 with R4 for each law -/
instance boxLawful : LawfulMonad Box :=
  LawfulMonad.mk' Box (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

/-! ### W2. A counter threaded through a tree: R5, R8, `rw [ih]`, R9
`count t s` is the counter after visiting `t` from `s`; the right subtree starts where the left
one stopped, so `ihr` is used at `count l s`. -/
def count : Bin → Nat → Nat
  | .tip, s => s + 1
  | .fork l r, s => count r (count l s)

example (t : Bin) (s : Nat) : count t s = s + t.leaves := by
  induction t generalizing s with
    | tip => rfl
    | fork l r ihl ihr =>
      rw [count, ihr, ihl, Bin.leaves]
      omega

/-! ### W3. R10 needs the second start to be `s + m` literally: rewrite it there first -/
example (s a b c : Nat) (hc : c = s + a) :
    List.range' s a ++ List.range' c b = List.range' s (a + b) := by
  rw [hc]
  rw [List.range'_append_1]

end M014Guide
