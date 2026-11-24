/- Guide for M017 (Quicksort terminates).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a sieve, a split at 5).
Assumed: Lean basics (E001–E033). No imports: everything here is in core Lean.
-/

namespace M017Guide

/-! # Part R · Reference entries -/

/-! ## Termination: `termination_by` and `decreasing_by` -/

-- A helper and its length bound, used by R1 and the worked examples.
def rest (x : Nat) (xs : List Nat) : List Nat := xs.filter (fun y => y % x ≠ 0)

theorem rest_le (x : Nat) (xs : List Nat) : (rest x xs).length ≤ xs.length :=
  List.length_filter_le _ _

/-! ### R1. `termination_by m` + `decreasing_by` · goal list: one goal per recursive call
`sieve (rest x xs)` is not structural recursion (the argument is not a sub-term of `x :: xs`).
`termination_by l.length` says "the length goes down"; `decreasing_by` must then prove
`(rest x xs).length < (x :: xs).length`. W1 replays that goal as an `example` you can step through. -/
def sieve (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs => x :: sieve (rest x xs)
termination_by l.length
decreasing_by
  have := rest_le x xs
  simp only [List.length_cons]
  omega

/-! ### R2. `have := e` · context gains `this : T` (the type of `e`); goal unchanged -/
example (T G : Prop) (t : T) (g : T → G) : G := by
  have := t
  exact g this

/-! ### R3. `List.length_filter_le` · `(l.filter p).length ≤ l.length` · context, via `have :=` -/
example {α : Type} (p : α → Bool) (l : List α) (G : Prop)
    (g : (l.filter p).length ≤ l.length → G) : G := by
  have := List.length_filter_le p l
  exact g this

/-! ### R4. `List.length_cons` · `(a :: l).length = l.length + 1` · goal -/
example {α : Type} (a : α) (l : List α) (P : Nat → Prop) (h : P (l.length + 1)) :
    P (a :: l).length := by
  simp only [List.length_cons]
  exact h

/-! ### R5. `omega` · closes linear arithmetic over `Nat`/`Int`, using the hypotheses in context
Terms it does not understand (such as `(l.filter p).length`) are treated as opaque numbers. -/
example (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  omega

/-! ## Induction that follows the function: `fun_induction` -/

def zig : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: xs => x + zig (y :: xs) + zig xs

/-! ### R6. `fun_induction zig l` · goal list: one goal per equation of `zig`, each with its IHs
The new names print with `✝` (inaccessible). Name them with
`fun_induction zig l with | case1 => … | case2 x => … | case3 x y xs ih1 ih2 => …`;
here `case`/`rename_i` do the same one step at a time. -/
example (l : List Nat) (Q : List Nat → Nat → Prop) (h : ∀ l, Q l (zig l)) : Q l (zig l) := by
  fun_induction zig l
  case case1 => exact h []
  case case2 x => exact h [x]
  rename_i x y xs ih1 ih2
  exact h (x :: y :: xs)

/-! ## Membership -/

/-! ### R7. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · goal -/
example {α : Type} (a : α) (s t : List α) (P : Prop → Prop) (h : P (a ∈ s ∨ a ∈ t)) :
    P (a ∈ s ++ t) := by
  rw [List.mem_append]
  exact h

/-! ### R8. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · goal -/
example {α : Type} (a b : α) (l : List α) (P : Prop → Prop) (h : P (a = b ∨ a ∈ l)) :
    P (a ∈ b :: l) := by
  rw [List.mem_cons]
  exact h

/-! ### R9. `rw [h]` with `h : A ↔ B` · goal: `A` → `B` (an `↔` rewrites like an `=`) -/
example (A B : Prop) (P : Prop → Prop) (h : A ↔ B) (hb : P B) : P A := by
  rw [h]
  exact hb

/-! ### R10. `unfold d` · goal: the name `d` → its body (`simp only [d]` does the same) -/
def small (xs : List Nat) : List Nat := xs.filter (· < 3)

example (xs : List Nat) (P : List Nat → Prop) (h : P (xs.filter (· < 3))) : P (small xs) := by
  unfold small
  exact h

/-! ### R11. `List.mem_filter` · `a ∈ l.filter p ↔ a ∈ l ∧ p a = true` · goal -/
example {α : Type} (p : α → Bool) (a : α) (l : List α) (P : Prop → Prop)
    (h : P (a ∈ l ∧ p a = true)) : P (a ∈ l.filter p) := by
  rw [List.mem_filter]
  exact h

/-! ### R12. `decide_eq_true_eq` · `(decide A = true) = A` · goal: a `Bool` test back to a `Prop` -/
example (A : Prop) [Decidable A] (P : Prop → Prop) (h : P A) : P (decide A = true) := by
  simp only [decide_eq_true_eq]
  exact h

/-! ### R13. `grind` · closes goals that follow by propositional logic, equalities and arithmetic
It case-splits on `B ∨ ¬B` by itself (classical logic). -/
example (A B C : Prop) : (A ∧ B) ∨ C ∨ (A ∧ ¬B) ↔ C ∨ A := by
  grind

/-! ## Lengths -/

/-! ### R14. `List.length_append` · `(s ++ t).length = s.length + t.length` · goal -/
example {α : Type} (s t : List α) (P : Nat → Prop) (h : P (s.length + t.length)) :
    P (s ++ t).length := by
  rw [List.length_append]
  exact h

/-! ### R15. `List.filter_append_perm` · `(l.filter p ++ l.filter (fun x => !p x)).Perm l` · context
`l₁.Perm l₂` (`List.Perm`, also written `l₁ ~ l₂`): `l₁` is a reordering of `l₂`. `!b` is `Bool` not. -/
example {α : Type} (p : α → Bool) (l : List α) (G : Prop)
    (g : (l.filter p ++ l.filter (fun x => !p x)).Perm l → G) : G := by
  have := List.filter_append_perm p l
  exact g this

/-! ### R16. `List.Perm.length_eq` · `l₁.Perm l₂ → l₁.length = l₂.length` · context
Dot notation: for `hp : l₁.Perm l₂`, `hp.length_eq` means `List.Perm.length_eq hp`. -/
example {α : Type} (l₁ l₂ : List α) (hp : l₁.Perm l₂) (G : Prop)
    (g : l₁.length = l₂.length → G) : G := by
  have := hp.length_eq
  exact g this

/-! ### R17. `rw [lemma] at h` · context: rewrites hypothesis `h`; goal unchanged -/
example {α : Type} (s t : List α) (n : Nat) (h : (s ++ t).length = n) :
    s.length + t.length = n := by
  rw [List.length_append] at h
  exact h

/-! ### R18. `decide_not` · `decide ¬A = !decide A` · goal; use `simp only`, it rewrites under `fun x =>` -/
example (p : Nat → Prop) [DecidablePred p] (l : List Nat) (P : List Nat → Prop)
    (h : P (l.filter (fun x => !decide (p x)))) : P (l.filter (fun x => decide ¬p x)) := by
  simp only [decide_not]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The `decreasing_by` goal of `sieve` (R1) as an example: R2 → R4 → R5 -/
example (x : Nat) (xs : List Nat) : (rest x xs).length < (x :: xs).length := by
  have := rest_le x xs
  simp only [List.length_cons]
  omega

/-! ### W2. `fun_induction` on `sieve` with named cases (R6), then R4, R2, R5 -/
example (xs : List Nat) : (sieve xs).length ≤ xs.length := by
  fun_induction sieve xs with
    | case1 => simp
    | case2 x xs ih =>
      rw [List.length_cons, List.length_cons]
      have := rest_le x xs
      omega

/-! ### W3. Membership in a split at 5: R7, then R11 + R12, then R13 -/
example (x : Nat) (xs : List Nat) :
    x ∈ xs.filter (· < 5) ++ xs.filter (fun y => ¬y < 5) ↔ x ∈ xs := by
  rw [List.mem_append]
  simp only [List.mem_filter, decide_eq_true_eq]
  grind

/-! ### W4. The two halves of a split at 5 add up: R15 → R16, R17, R18, R5 -/
example (xs : List Nat) :
    (xs.filter (· < 5)).length + (xs.filter (fun y => ¬y < 5)).length = xs.length := by
  have := (List.filter_append_perm (· < 5) xs).length_eq
  rw [List.length_append] at this
  simp only [decide_not]
  omega

end M017Guide
