/- Guide for M022 (Linear search).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own objects, which are NOT the exercise's:
  `len xs`        the length of a list, by structural recursion (R1);
  `isZero n`      an `if` on `n = 0` (R2);
  `stepsDown k n` the number of steps `n, n - 1, …, 0` takes to reach `k`, or `none`: recursion
                  that returns an `Option` and shifts the recursive answer with `Option.map` (R3).
Part W: worked combinations on `stepsDown`.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M022Guide

/-! # Part R · Reference entries -/

/-! ## Writing the function -/

/-! ### R1. `match xs with | [] => … | x :: xs => …` · term: a recursive `def` on a list
Lean accepts the recursive call `len xs` because `xs` is the tail of the matched list (structural
recursion). Each arm is one equation `simp only [len]` can use (R6). -/
def len {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: xs => len xs + 1

example {α : Type} (a b : α) : len [a, b] = 2 := rfl

/-! ### R2. `if a = b then u else v` · term: a branch on an equality of numbers
`a = b` is a `Prop`; `if` works because `Nat` has decidable equality (an algorithm deciding it). -/
def isZero (n : Nat) : Bool := if n = 0 then true else false

example : isZero 0 = true ∧ isZero 3 = false := ⟨rfl, rfl⟩

/-! ### R3. `Option.map f o` and `(· + 1)` · term: apply `f` inside `some`, leave `none` alone
`(· + 1)` is the function `fun n => n + 1`. `o.map f` is the same as `Option.map f o`. -/
example (f : Nat → Nat) (a : Nat) : Option.map f (some a) = some (f a) ∧ Option.map f none = none :=
  ⟨rfl, rfl⟩

example (a : Nat) : (some a).map (· + 1) = some (a + 1) := rfl

/-- `stepsDown k n`: how many steps `n, n - 1, …, 0` takes to reach `k`; `none` if `k > n`. -/
def stepsDown (k : Nat) (n : Nat) : Option Nat :=
  match n with
  | 0 => if 0 = k then some 0 else none
  | n + 1 => if n + 1 = k then some 0 else (stepsDown k n).map (· + 1)

/-! ## Induction with a re-quantified index -/

/-! ### R4. `induction xs generalizing i with | nil => ?_ | cons x xs ih => ?_` · goal list: `[]` and
`x :: xs`; context: `ih : ∀ i, …`
`generalizing i` takes `i` (and every hypothesis mentioning it) out of the context first, so `ih`
holds for EVERY index: you will apply it at `i'`, the recursive call's answer, not at `i`. -/
example {α : Type} (P : List α → Nat → Prop) (h0 : ∀ i, P [] i)
    (hs : ∀ x xs, (∀ i, P xs i) → ∀ i, P (x :: xs) i) (xs : List α) (i : Nat) : P xs i := by
  induction xs generalizing i with | nil => ?_ | cons x xs ih => ?_
  · exact h0 i
  · exact hs x xs ih i

/-! ## Taking a hypothesis about the function apart -/

/-! ### R5. `simp at h` on `h : none = some a` (or `some a = none`) · closes the goal
Different constructors are never equal, so `h` becomes `False` and the goal is closed. -/
example (a : Nat) (G : Prop) (h : (none : Option Nat) = some a) : G := by
  simp at h

example (a : Nat) (G : Prop) (h : some a = none) : G := by
  simp at h

/-! ### R6. `simp only [f] at h` · context: unfold one equation of `f` inside `h`
It fires when the argument is literally a constructor (`[]`, `x :: xs`, `0`, `n + 1`). -/
example (k n : Nat) (o : Option Nat) (G : Prop)
    (hg : (if n + 1 = k then some 0 else (stepsDown k n).map (· + 1)) = o → G)
    (h : stepsDown k (n + 1) = o) : G := by
  simp only [stepsDown] at h
  exact hg h

/-! ### R7. `split at h` · goal list: `h : (if c then u else v) = o` → two goals
The first has `h✝ : c` and `h : u = o`, the second `h✝ : ¬c` and `h : v = o`.
Name the condition with `rename_i hc`, or let `simp_all` use it. -/
example (c : Prop) [Decidable c] (u v o : Option Nat) (G : Prop) (hu : c → u = o → G)
    (hv : ¬c → v = o → G) (h : (if c then u else v) = o) : G := by
  split at h
  · rename_i hc
    exact hu hc h
  · rename_i hc
    exact hv hc h

/-! ### R8. `simp at h` on `h : some a = some b` · context: `h` becomes `a = b`
(lemma `Option.some.injEq`: `some` is injective). -/
example (a b : Nat) (G : Prop) (hg : a = b → G) (h : some a = some b) : G := by
  simp at h
  exact hg h

/-! ### R9. `subst h` with `h : a = i` and `i` a local variable · context: `i` disappears;
every `i` in the goal becomes `a` -/
example (a i : Nat) (P : Nat → Prop) (hp : P a) (h : a = i) : P i := by
  subst h
  exact hp

/-! ## Indexing a cons -/

/-! ### R10. `List.getElem?_cons_zero` · `(a :: l)[0]? = some a` · goal
`l[i]?` is the `i`-th entry of `l` (from 0) as an `Option`: `some` if `i < l.length`, else `none`.
`simp` applies this lemma by itself. -/
example {α : Type} (a : α) (l : List α) (P : Option α → Prop) (h : P (some a)) : P (a :: l)[0]? := by
  rw [List.getElem?_cons_zero]
  exact h

/-! ### R11. `simp_all` · closes the goal by simplifying every hypothesis and the goal with each other
Here `hc : x = k` is used to rewrite `some x` to `some k`, and `j < 0` is recognised as `False`. -/
example (x k : Nat) (l : List Nat) (hc : x = k) :
    (x :: l)[0]? = some k ∧ ∀ j < 0, (x :: l)[j]? ≠ some k := by
  simp_all

/-! ## Splitting on the recursive call -/

/-! ### R12. `cases hs : e with | none => ?_ | some a => ?_` · goal list: one goal per value of `e`;
context gains `hs : e = none` / `hs : e = some a`
It replaces `e` in the GOAL only. A hypothesis `h` that mentions `e` keeps `e`: rewrite it with
`hs` (R13, R14). -/
example (o : Option Nat) (P : Option Nat → Prop) (hn : P none) (hsm : ∀ a, P (some a)) : P o := by
  cases hs : o with | none => ?_ | some a => ?_
  · exact hn
  · exact hsm a

/-! ### R13. `Option.map_none` · `Option.map f none = none` · used by `simp [hs] at h`, it closes the goal
`simp [hs] at h` rewrites `o` to `none` in `h` (by `hs`), then this lemma, then R5. -/
example (f : Nat → Nat) (o : Option Nat) (b : Nat) (G : Prop) (hs : o = none)
    (h : Option.map f o = some b) : G := by
  simp [hs] at h

/-! ### R14. `Option.map_some` · `Option.map f (some a) = some (f a)` · context:
`simp [hs] at h` turns `h : Option.map f o = some b` (with `hs : o = some a`) into `h : f a = b`
(this lemma, then R8). -/
example (f : Nat → Nat) (o : Option Nat) (a b : Nat) (G : Prop) (hg : f a = b → G)
    (hs : o = some a) (h : Option.map f o = some b) : G := by
  simp [hs] at h
  exact hg h

/-! ## Using the induction hypothesis -/

/-! ### R15. `obtain ⟨h1, h2⟩ := ih a hs` · context gains the two halves of `ih` at `a`
`ih : ∀ i, Q i → A i ∧ B i` is a function: `ih a hs` is its value at `a`, and the pattern splits `∧`. -/
example (Q A B : Nat → Prop) (G : Prop) (a : Nat) (hs : Q a) (ih : ∀ i, Q i → A i ∧ B i)
    (hg : A a → B a → G) : G := by
  obtain ⟨h1, h2⟩ := ih a hs
  exact hg h1 h2

/-! ### R16. `refine ⟨by tac, ?_⟩` · goal `A ∧ B` → goal `B`; `tac` proves `A` on the spot -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  refine ⟨by exact ha, ?_⟩
  exact hb

/-! ### R17. `List.getElem?_cons_succ` · `(a :: l)[i + 1]? = l[i]?` · goal: drop the head, index one less
`simp` applies it by itself. -/
example {α : Type} (a : α) (l : List α) (i : Nat) (P : Option α → Prop) (h : P l[i]?) :
    P (a :: l)[i + 1]? := by
  rw [List.getElem?_cons_succ]
  exact h

/-! ### R18. `simpa using e` · closes the goal: simplify the goal and the type of `e`, then they match -/
example {α : Type} (a : α) (l : List α) (i : Nat) (b : α) (h1 : l[i]? = some b) :
    (a :: l)[i + 1]? = some b := by
  simpa using h1

/-! ### R19. `cases j with | zero => ?_ | succ j => ?_` · goal list: `j = 0` and `j = j' + 1` -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ j, P (j + 1)) (j : Nat) : P j := by
  cases j with | zero => ?_ | succ j => ?_
  · exact h0
  · exact hs j

/-! ### R20. `e (by omega)` · term: an argument proved by linear arithmetic on the spot
`h2 j : j < a → Q j` needs a proof of `j < a`; here `omega` derives it from `hj : j + 1 < a + 1`. -/
example (Q : Nat → Prop) (a j : Nat) (h2 : ∀ j, j < a → Q j) (hj : j + 1 < a + 1) : Q j := by
  exact h2 j (by omega)

/-! ## Membership -/

/-! ### R21. `List.not_mem_nil` · `a ∉ []` · `simp` closes the goal -/
example (k : Nat) : k ∉ ([] : List Nat) := by
  simp

/-! ### R22. `Option.map_eq_none_iff` · `Option.map f o = none ↔ o = none` · context (`simp at h`) -/
example (f : Nat → Nat) (o : Option Nat) (G : Prop) (hg : o = none → G)
    (h : Option.map f o = none) : G := by
  simp at h
  exact hg h

/-! ### R23. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · goal
`k ∉ l` is notation for `¬(k ∈ l)`. -/
example {α : Type} (a b : α) (l : List α) (P : Prop → Prop) (h : P ¬(a = b ∨ a ∈ l)) :
    P (a ∉ b :: l) := by
  simp only [List.mem_cons]
  exact h

/-! ### R24. `not_or` · `¬(p ∨ q) ↔ ¬p ∧ ¬q` · goal -/
example (p q : Prop) (P : Prop → Prop) (h : P (¬p ∧ ¬q)) : P ¬(p ∨ q) := by
  simp only [not_or]
  exact h

/-! ### R25. `exact ⟨fun hp => …, hq⟩` · closes `¬p ∧ q`
`¬p` is `p → False`, so its proof is a function from a proof `hp : p` to `False`. -/
example (p q : Prop) (hnp : p → False) (hq : q) : ¬p ∧ q := by
  exact ⟨fun hp => hnp hp, hq⟩

/-! # Part W · Worked combinations (on `stepsDown`, not the exercise's function) -/

/-- W1. Induction generalizing the answer (R4); unfold and split the `if` at `h` (R6, R7);
`simp at h` + `subst` (R8, R9); split on the recursive call (R12, R13, R14); the IH at `a`. -/
theorem stepsDown_some (k n i : Nat) (h : stepsDown k n = some i) : n = k + i := by
  induction n generalizing i with
    | zero =>
      simp only [stepsDown] at h
      split at h
      · simp at h
        omega
      · simp at h
    | succ n ih =>
      simp only [stepsDown] at h
      split at h
      · simp at h
        omega
      · cases hs : stepsDown k n with
          | none => simp [hs] at h
          | some a =>
            simp [hs] at h
            subst h
            have := ih a hs
            omega

/-- W2. The `none` direction: `simp at h` turns `Option.map f o = none` into `o = none` (R22). -/
theorem stepsDown_none (k n : Nat) (h : stepsDown k n = none) : n < k := by
  induction n with
    | zero =>
      simp only [stepsDown] at h
      split at h
      · simp at h
      · omega
    | succ n ih =>
      simp only [stepsDown] at h
      split at h
      · simp at h
      · simp at h
        have := ih h
        omega

end M022Guide
