/- Guide for H013 (Run-length encoding, both directions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about recursive definitions use the guide's own functions `sumL`, `squash` (drop adjacent
duplicates) and the predicate `Up` (strictly increasing), which are NOT the exercise's.
Part W: worked combinations on `squash`.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace H013Guide

/-! # Part R · Reference entries -/

/-! ## Writing the function -/

/-! ### R1. `fun | [] => … | x :: xs => … f xs …` · a definition body by pattern matching
The `:=` of the definition is already written, so its body is one term: a `fun` with match arms.
A call `f xs` on the tail is structural recursion, exactly as with equations `| x :: xs => …`. -/
def sumL : List Nat → Nat :=
  fun
  | [] => 0
  | x :: xs => x + sumL xs

example : sumL [1, 2, 3] = 6 := rfl

/-! ### R2. `match f xs with …` on the recursive result, then `if x = y then … else …`
`[DecidableEq α]` makes `x = y` testable by a program, so `if x = y` is allowed for `x y : α`
(`Nat`, `Char`, `Bool`, `String` all have it). -/
def squash {α : Type} [DecidableEq α] : List α → List α :=
  fun
  | [] => []
  | x :: xs =>
    match squash xs with
    | [] => [x]
    | y :: r => if x = y then y :: r else x :: y :: r

example : squash [1, 1, 2, 2, 2, 1] = [1, 2, 1] := rfl

/-! ## Unfolding a predicate on a list -/

/-- `Up l`: `l` is strictly increasing. Three clauses, like a predicate about neighbours. -/
def Up : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => a < b ∧ Up (b :: r)

/-! ### R3. `cases r with | nil => … | cons q r => …` · goal list: one goal per list constructor
Each arm names the constructor's arguments. Here the arms are `?_`, so both goals stay open and show
in the infoview; in a proof you write the arm's tactics after `=>` instead. -/
example {α : Type} (P : List α → Prop) (h0 : P []) (h1 : ∀ q r, P (q :: r)) (r : List α) : P r := by
  cases r with | nil => ?_ | cons q r => ?_
  · exact h0
  · exact h1 q r

/-! ### R4. `obtain ⟨b, m⟩ := q` · context: a pair `q : α × β` → its two components -/
example {α β : Type} (P : α × β → Prop) (h : ∀ b m, P (b, m)) (q : α × β) : P q := by
  obtain ⟨b, m⟩ := q
  exact h b m

/-! ### R5. `simp only [D] at h ⊢` · context and goal: `D` on a constructor → its clause
`simp only [D]` uses the equations of `D`; it fires only when the argument shows which clause applies. -/
example (a b c : Nat) (r : List Nat) (h : Up (a :: b :: r)) (hc : c < a) :
    Up (c :: a :: b :: r) := by
  simp only [Up] at h ⊢
  exact ⟨hc, h⟩

/-! ### R6. `omega` · closes linear arithmetic over `Nat` and `Int`, using the hypotheses -/
example (n : Nat) (h : 0 < n) : 0 < n + 1 := by
  omega

/-! ### R7. `exact ⟨p, h.2⟩` · closes `A ∧ B`: anonymous constructor, `h.1`/`h.2` are the halves of `h` -/
example (A B C : Prop) (hc : C) (h : A ∧ B) : C ∧ B := by
  exact ⟨hc, h.2⟩

/-! ## Induction on the count and computing one step -/

/-! ### R8. `induction n with | zero => … | succ n ih => …` · goal list, plus `ih` in the step
Arms `?_` as in R3, to show both goals. -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R9. `simp only [List.replicate]` · goal: `List.replicate (0 + 1) a` → `[a]`
`List.replicate n a` is the list of `n` copies of `a`. -/
example {α : Type} (a : α) (P : List α → Prop) (h : P [a]) : P (List.replicate (0 + 1) a) := by
  simp only [List.replicate]
  exact h

/-! ### R10. `List.singleton_append` · `[x] ++ l = x :: l` · goal -/
example {α : Type} (x : α) (l : List α) (P : List α → Prop) (h : P (x :: l)) : P ([x] ++ l) := by
  rw [List.singleton_append]
  exact h

/-! ### R11. `simp only [f]` (or `rw [f]`) · goal: `f (x :: xs)` → the `x :: xs` arm of `f`
For a definition written as `fun | … => …` this exposes the inner `match f xs with …`. -/
example {α : Type} [DecidableEq α] (x : α) (xs : List α) (P : List α → Prop)
    (h : P (match squash xs with
      | [] => [x]
      | y :: r => if x = y then y :: r else x :: y :: r)) :
    P (squash (x :: xs)) := by
  simp only [squash]
  exact h

/-! ### R12. `split` on a `match` · goal list: one goal per arm, each with `heq✝ : e = pattern`
The discriminant `e` (here `g c`) stays in the goal; `heq✝` says which arm you are in. -/
example {α β γ : Type} (g : γ → List α) (c : γ) (u : β) (v : α → List α → β) (P : β → Prop)
    (h0 : g c = [] → P u) (h1 : ∀ y r, g c = y :: r → P (v y r)) :
    P (match g c with
      | [] => u
      | y :: r => v y r) := by
  split
  · exact h0 ‹_›
  · exact h1 _ _ ‹_›

/-! ### R13. `rename_i y r heq` · context: names the last inaccessible hypotheses, in order
`y✝ r✝ heq✝` (made by `split`) become `y r heq`; then you can write `heq` in a tactic.
(`‹_›` is "the hypothesis of the right type": a way to use one that has no name.) -/
example {α β γ : Type} (g : γ → List α) (c : γ) (u : β) (v : α → List α → β) (P : β → Prop)
    (h0 : g c = [] → P u) (h1 : ∀ y r, g c = y :: r → P (v y r)) :
    P (match g c with
      | [] => u
      | y :: r => v y r) := by
  split
  exact h0 ‹_›
  rename_i y r heq
  exact h1 y r heq

/-! ### R14. `split` on an `if` · goal list: `h✝ : c` in the `then` goal, `h✝ : ¬c` in the `else` goal -/
example {β : Type} (c : Prop) [Decidable c] (u v : β) (P : β → Prop)
    (h1 : c → P u) (h2 : ¬c → P v) : P (if c then u else v) := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

/-! ### R15. `subst_vars` · context: every hypothesis `x = e` with a variable side is used and removed;
the variable is replaced by the other side everywhere. -/
example {α : Type} (a y : α) (P : α → α → Prop) (hay : a = y) (h : P y y) : P a y := by
  subst_vars
  exact h

/-! ### R16. `exact absurd h hn` · closes any goal from `h : p` and `hn : ¬p`
`absurd : p → ¬p → q`. Here `¬p` is `e ≠ t`, i.e. `e = t → False`. -/
example {α : Type} (Q : Prop) (e t : α) (h : e = t) (hn : e ≠ t) : Q := by
  exact absurd h hn

/-! ### R17. `List.replicate_succ` · `List.replicate (n + 1) a = a :: List.replicate n a` · goal -/
example {α : Type} (a : α) (n : Nat) (P : List α → Prop) (h : P (a :: List.replicate n a)) :
    P (List.replicate (n + 1) a) := by
  rw [List.replicate_succ]
  exact h

/-! ### R18. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`::` binds tighter than `++`, so `a :: as ++ bs` is `(a :: as) ++ bs`. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R19. `simp` · goal: a `match` on a visible constructor picks its arm; `if a = a` → `then` branch -/
example {α β : Type} [DecidableEq α] (a : α) (t : List α) (u : β) (v w : α → List α → β)
    (P : β → Prop) (h : P (v a t)) :
    P (match a :: t with
      | [] => u
      | y :: r => if a = y then v y r else w y r) := by
  simp
  exact h

/-! ## Many similar cases at once -/

/-! ### R20. `try t` · runs `t`; if `t` fails, does nothing instead of failing
`split <;> (try split) <;> …` splits a `match`, then the `if` in those arms that have one. -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  try constructor
  · exact ha
  · exact hb

/-! ### R21. `simp_all [l]` · closes the goal (or simplifies it): simplifies every hypothesis and the
goal with `l`, the definitions given, and each other; an equation `heq : e = t` rewrites `e` elsewhere. -/
example {α : Type} (f : List α → List α) (e t : List α) (heq : f e = t) (ih : t = e) : f e = e := by
  simp_all

/-! ### R22. `trivial` · closes `True`, and a definition that unfolds to `True` (`Up []`) -/
example : Up [] := by
  trivial

/-! ### R23. `rw [h] at h'` · context: rewrite inside the hypothesis `h'` -/
example {α : Type} (e t : List α) (P : List α → Prop) (heq : e = t) (ih : P e) : P t := by
  rw [heq] at ih
  exact ih

/-! ## Unpacking hypotheses -/

/-! ### R24. `obtain ⟨hn, hab, hr⟩ := h` · context: `h : A ∧ B ∧ C` → three hypotheses -/
example (A B C : Prop) (h : A ∧ B ∧ C) : B := by
  obtain ⟨hn, hab, hr⟩ := h
  exact hab

/-! ### R25. `obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩` · context and goal:
`n` disappears, replaced by `k + 1` everywhere (`rfl` as a pattern substitutes the equation). -/
example (P : Nat → Prop) (n : Nat) (hn : 0 < n) (h : ∀ k, P (k + 1)) : P n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact h k

/-! ### R26. `simpa [l] using e` · closes the goal: simplifies the type of `e` and the goal with `l`,
then they must agree. -/
example (P : List Nat → Prop) (l : List Nat) (e : P (l ++ [])) : P l := by
  simpa using e

/-! ### R27. `intro x y h` on `∀ x y, e ≠ t` · context: `≠` is `= → False`, so `intro` also takes the
equation; the goal becomes `False`. -/
example {α : Type} (f : α → α → List α) (e : List α) (h : ∀ x y, e = f x y → False) :
    ∀ x y, e ≠ f x y := by
  intro x y hxy
  exact h x y hxy

/-! ### R28. `injection h with h₁ h₂` · context: equal constructor applications → equal arguments
For `::` and for pairs `(a, n)`. Then `h₁.symm` turns `a = b` into `b = a`. -/
example {α : Type} (a b : α) (l l' : List α) (h : a :: l = b :: l') (hne : b ≠ a) : False := by
  injection h with h₁ h₂
  exact hne h₁.symm

example {α : Type} (a b : α) (n m : Nat) (h : (a, n) = (b, m)) : b = a := by
  injection h with h₁ h₂
  exact h₁.symm

/-! # Part W · Worked combinations (on `squash`, not the exercise's `encode`) -/

/-! ### W1. Induction + unfold + `split` on the `match`, then on the `if` (R8, R11, R12, R14) -/
example {α : Type} [DecidableEq α] (xs : List α) : (squash xs).length ≤ xs.length := by
  induction xs with
    | nil => simp [squash]
    | cons x xs ih =>
      simp only [squash]
      split
      · simp
      · rename_i y r heq
        rw [heq] at ih
        split
        · simp at ih ⊢; omega
        · simp at ih ⊢; omega

/-! ### W2. A `replicate` run collapses (R8, R9, R10, R11, R17, R18, R19) -/
example {α : Type} [DecidableEq α] (a : α) (n : Nat) : squash (List.replicate (n + 1) a) = [a] := by
  induction n with
    | zero => simp only [List.replicate, squash]
    | succ n ih =>
      rw [List.replicate_succ, squash, ih]
      simp

/-! ### W3. All arms at once (R20, R21) -/
example {α : Type} [DecidableEq α] (x : α) (xs : List α) (hx : squash xs = []) :
    squash (x :: xs) = [x] := by
  simp only [squash]
  split <;> (try split) <;> simp_all

end H013Guide
