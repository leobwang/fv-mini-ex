/- Guide for H012 (Boyer-Moore majority vote with mvcgen).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The `mvcgen` entries need a concrete program, so they use small programs that are NOT the exercise's
(`twice`, `sumL`, `evens`, `quad`, `countTwice`).
Part W: worked combinations on other programs (maximum of a list, sum of a list).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean and `Std.Do`.
-/
import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

namespace H012Guide

/-! # Part R · Reference entries -/

/-! ## Counting and lengths (`grind` and `simp` use these by themselves) -/

/-! ### R1. `List.count_nil` · `List.count a [] = 0` · goal
`List.count a l` is the number of `x ∈ l` with `x == a`. Lean prints it `List.count a l`, not `l.count a`. -/
example {α : Type} [BEq α] (a : α) (P : Nat → Prop) (h : P 0) : P (List.count a []) := by
  rw [List.count_nil]
  exact h

/-! ### R2. `List.length_nil` · `[].length = 0` · goal -/
example {α : Type} (P : Nat → Prop) (h : P 0) : P ([] : List α).length := by
  rw [List.length_nil]
  exact h

/-! ### R3. `List.count_append` · `List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂` · goal -/
example {α : Type} [BEq α] (a : α) (l₁ l₂ : List α) (P : Nat → Prop)
    (h : P (List.count a l₁ + List.count a l₂)) : P (List.count a (l₁ ++ l₂)) := by
  rw [List.count_append]
  exact h

/-! ### R4. `List.count_singleton` · `List.count a [b] = if (b == a) = true then 1 else 0` · goal -/
example {α : Type} [BEq α] (a b : α) (P : Nat → Prop)
    (h : P (if (b == a) = true then 1 else 0)) : P (List.count a [b]) := by
  rw [List.count_singleton]
  exact h

/-! ### R5. `beq_iff_eq` · `(a == b) = true ↔ a = b` · goal: Boolean test → equation
`[LawfulBEq α]` says `==` agrees with `=`; `Nat` has it. -/
example {α : Type} [BEq α] [LawfulBEq α] (a b : α) (P : Prop → Prop) (h : P (b = a)) :
    P ((b == a) = true) := by
  rw [beq_iff_eq]
  exact h

/-! ### R6. `List.length_append` · `(as ++ bs).length = as.length + bs.length` · goal -/
example {α : Type} (as bs : List α) (P : Nat → Prop) (h : P (as.length + bs.length)) :
    P (as ++ bs).length := by
  rw [List.length_append]
  exact h

/-! ### R7. `List.length_singleton` · `[a].length = 1` · goal -/
example {α : Type} (a : α) (P : Nat → Prop) (h : P 1) : P [a].length := by
  rw [List.length_singleton]
  exact h

/-! ## Unfolding a predicate and closing arithmetic -/

/-! ### R8. `unfold D at *` · goal and context: the name `D` → its body, everywhere -/
def D (n : Nat) : Prop := n ≤ 5
example (n m : Nat) (h : D n) (hm : m ≤ n) : D m := by
  unfold D at *
  exact Nat.le_trans hm h

/-! ### R9. `grind` · closes the goal
It combines: linear arithmetic over `Nat` (`+`, `-` truncated at 0, `*` by numerals, `<`, `≤`),
instantiating `∀` hypotheses at the terms it sees, splitting `if`, and rewriting with lemmas tagged
for it, R1–R7 included. -/
example (c x n : Nat) (f : Nat → Nat) (h : ∀ y, y ≠ c → f y ≤ n) (hx : x ≠ c) :
    f x + 1 ≤ n + 1 := by
  grind

example (a b : Nat) (l : List Nat) (hb : b ≠ a) : List.count a (l ++ [b]) = List.count a l := by
  grind

/-! ### R10. `grind [l₁, l₂]` · closes the goal, also using the named lemmas `lᵢ`
`grind` instantiates each `lᵢ` when the terms in its conclusion show up. -/
def Ev (n : Nat) : Prop := n % 2 = 0
theorem ev_add_two (n : Nat) (h : Ev n) : Ev (n + 2) := by
  unfold Ev at *
  grind
example (n m : Nat) (h : Ev n) (hm : m = n + 2) : Ev m := by
  grind [ev_add_two]

/-! ## Hoare triples and `mvcgen` -/

/-! ### R11. `mvcgen [f]` · goal: a Hoare triple → its verification conditions (pure goals)
`⦃⌜True⌝⦄ prog ⦃⇓ r => ⌜Q r⌝⦄`: run from any state, `prog` returns some `r` with `Q r`. `⌜p⌝` turns
the `Prop` `p` into an assertion; `⇓ r => …` prints as `PostCond.noThrow fun r => …`. `mvcgen [f]`
unfolds `f` and leaves what remains to prove; a `let` in the program becomes a `let` hypothesis `a✝ : Nat := …`. -/
def twice (n : Nat) : Id Nat := do
  let a := n + n
  return a

theorem twice_spec (n : Nat) : ⦃⌜True⌝⦄ twice n ⦃⇓ r => ⌜r = 2 * n⌝⦄ := by
  mvcgen [twice]
  grind

/-! ### R12. `List.Cursor` · no step: the type of `cur` in an invariant, a split `xs = cur.prefix ++ cur.suffix` of the list being looped over
`cur.prefix` is the part already processed. In a loop VC, the current element sits between them:
`xs = pref✝ ++ cur✝ :: suff✝`, and the goal is about `pref✝ ++ [cur✝]`. -/
example (xs : List Nat) (cur : xs.Cursor) : cur.prefix ++ cur.suffix = xs := cur.property

/-! ### R13. `mvcgen [f] invariants · ⇓⟨cur, s⟩ => ⌜I⌝` · goal → one VC per loop-body branch
(plus entry `pre` and exit `post` VCs when `mvcgen` cannot close them by itself)
The invariant is a postcondition on `(cursor, value of the let mut)`. Write the `·` line indented
under `mvcgen`. `mvcgen [f] invariants?` prints a starting suggestion. -/
def sumL (l : List Nat) : Id Nat := do
  let mut s := 0
  for x in l do
    s := s + x
  return s

example (xs : List Nat) : ⦃⌜True⌝⦄ sumL xs ⦃⇓ r => ⌜r = xs.sum⌝⦄ := by
  mvcgen [sumL] invariants
    · ⇓⟨cur, s⟩ => ⌜s = cur.prefix.sum⌝
  grind

/-! ### R14. Two `let mut`s · the loop state is a pair `st : Nat × Nat`; write `st.1`, `st.2`
(in declaration order). In the VCs the state prints as `b✝ : Nat × Nat`, with `let` hypotheses such as
`e✝¹ : Nat := b✝.fst` for the old values and `e✝ : Nat := e✝¹ + 1` for the updated one. -/
def evens (l : List Nat) : Id (Nat × Nat) := do
  let mut e := 0
  let mut o := 0
  for x in l do
    if x % 2 = 0 then
      e := e + 1
    else
      o := o + 1
  return (e, o)

example (xs : List Nat) : ⦃⌜True⌝⦄ evens xs ⦃⇓ r => ⌜r.1 + r.2 = xs.length⌝⦄ := by
  mvcgen [evens] invariants
    · ⇓⟨cur, st⟩ => ⌜st.1 + st.2 = cur.prefix.length⌝
  all_goals grind

/-! ## Calling a verified function -/

/-! ### R15. `mvcgen [g, f_spec]` · goal: at the call `let a ← f …`, use the proved triple `f_spec`
The context gains the result `r✝` and its postcondition `h✝ : Q r✝`; `f` is not unfolded. -/
def quad (n : Nat) : Id Nat := do
  let a ← twice n
  return a + a

example (n : Nat) : ⦃⌜True⌝⦄ quad n ⦃⇓ r => ⌜r = 4 * n⌝⦄ := by
  mvcgen [quad, twice_spec]
  grind

/-! ### R16. `invariants | inv1 c _ => ⇓⟨cur, k⟩ => ⌜… c …⌝` · names variables for the invariant
The result of `let c ← f …` is the inaccessible `r✝`, so a `·` invariant cannot mention it.
`| inv1 c _ =>` names, in order, the inaccessible variables in scope of invariant 1 (the result `c`
and its postcondition `_`). Loops are numbered `inv1, inv2, …` in program order. -/
def countTwice (l : List Nat) (n : Nat) : Id Nat := do
  let c ← twice n
  let mut k := 0
  for x in l do
    if x = c then
      k := k + 1
  return k

example (xs : List Nat) (n : Nat) :
    ⦃⌜True⌝⦄ countTwice xs n ⦃⇓ r => ⌜r = List.count (2 * n) xs⌝⦄ := by
  mvcgen [countTwice, twice_spec] invariants
    | inv1 c _ => ⇓⟨cur, k⟩ => ⌜k = List.count c cur.prefix⌝
  all_goals grind

/-! ## From a triple to an equation about `.run` -/

/-! ### R17. `Id.of_wp_run_eq` · `prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x`
`prog.run` is the value an `Id` program computes. With `rfl : prog.run = prog.run`, `apply` turns a
goal `P prog.run` into the weakest-precondition goal `⊢ₛ wp⟦prog⟧ …` ("`Q` holds after `prog`"). -/
example {α : Type} (prog : Id α) (P : α → Prop) (h : ⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) :
    P prog.run := by
  apply Id.of_wp_run_eq rfl P
  exact h

/-! ### R18. A triple `⦃⌜True⌝⦄ prog ⦃Q⦄` proves `⊢ₛ wp⟦prog⟧ Q` · closes the goal
It also closes the `{ down := P a }` form that R17 leaves: that is `⌜P a⌝` unfolded. -/
example {α : Type} (prog : Id α) (P : α → Prop) (h : ⦃⌜True⌝⦄ prog ⦃⇓ a => ⌜P a⌝⦄) :
    ⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝) := by
  exact h

/-! # Part W · Worked combinations (not the exercise's programs) -/

/-! ### W1. A named invariant and one lemma per VC, then `all_goals grind [lemmas]`
`maxL` returns the largest element (0 for `[]`). -/
def maxL (l : List Nat) : Id Nat := do
  let mut m := 0
  for x in l do
    if m < x then
      m := x
  return m

def MaxInv (p : List Nat) (m : Nat) : Prop := ∀ y, y ∈ p → y ≤ m

theorem maxInv_nil : MaxInv [] 0 := by simp [MaxInv]

theorem maxInv_up (p : List Nat) (m x : Nat) (hx : m < x) (h : MaxInv p m) :
    MaxInv (p ++ [x]) x := by
  unfold MaxInv at *
  grind

theorem maxInv_keep (p : List Nat) (m x : Nat) (hx : ¬m < x) (h : MaxInv p m) :
    MaxInv (p ++ [x]) m := by
  unfold MaxInv at *
  grind

example (xs : List Nat) : ⦃⌜True⌝⦄ maxL xs ⦃⇓ r => ⌜∀ y, y ∈ xs → y ≤ r⌝⦄ := by
  mvcgen [maxL] invariants
    · ⇓⟨cur, m⟩ => ⌜MaxInv cur.prefix m⌝
  all_goals grind [maxInv_nil, maxInv_up, maxInv_keep]

/-! ### W2. Term mode: `Id.of_wp_run_eq rfl P spec` is a proof of `P prog.run`; when `P r` is a
`∀ k, … → …`, apply it to more arguments. -/
theorem sumL_spec (xs : List Nat) : ⦃⌜True⌝⦄ sumL xs ⦃⇓ r => ⌜∀ k, xs.sum = k → r = k⌝⦄ := by
  mvcgen [sumL] invariants
    · ⇓⟨cur, s⟩ => ⌜s = cur.prefix.sum⌝
  all_goals grind

example (xs : List Nat) (k : Nat) (hk : xs.sum = k) : (sumL xs).run = k :=
  Id.of_wp_run_eq rfl (fun r => ∀ k, xs.sum = k → r = k) (sumL_spec xs) k hk

end H012Guide
