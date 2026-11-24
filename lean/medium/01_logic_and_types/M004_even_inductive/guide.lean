/- Guide for M004 (Even as an inductive predicate).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on the toy predicate `Step3` below, which is NOT the exercise's.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M004Guide

/-! ## Toy object used by the entries (not the exercise's) -/

/-- `Step3 n`: "`n` is a multiple of 3", given by two rules (constructors).
`base` is an axiom-like rule with no premise; `next n` turns a derivation of `Step3 n` into one of
`Step3 (n + 3)`. A proof of `Step3 6` is a finite tree (here a chain) built from these rules. -/
inductive Step3 : Nat → Prop
  | base : Step3 0
  | next (n : Nat) : Step3 n → Step3 (n + 3)

/-! # Part R · Reference entries -/

/-! ## Building derivations: rules are functions -/

/-! ### R1. `exact .base` · closes the goal with a rule that has no premise
`.base` is shorthand for `Step3.base`: Lean reads the expected type `Step3 _` and looks the name up
in the namespace `Step3`. -/
example : Step3 0 := by
  exact .base

/-! ### R2. `apply Step3.next` · goal `Step3 (n + 3)` → `Step3 n` (the rule's premise)
`Step3.next : ∀ (n : Nat), Step3 n → Step3 (n + 3)`. `apply` matches the goal against the conclusion
`Step3 (?n + 3)` and leaves the premise. On a literal, Lean solves `6 = ?n + 3` by computing `?n := 3`.
As a term the same step is `.next _ h` (or `Step3.next n h`); `_` lets Lean infer `n`. -/
example (n : Nat) (h : Step3 n) : Step3 (n + 3) := by
  apply Step3.next
  exact h

example (h : Step3 3) : Step3 6 := by
  apply Step3.next
  exact h

example (n : Nat) (h : Step3 n) : Step3 (n + 3) := .next _ h

/-! ## Induction on a number -/

/-! ### R3. `induction n` · goal list: `zero` (`P 0`) and `succ` (`P (n + 1)` with hypothesis `P n`)
Write `induction n with | zero => … | succ n ih => …` to name the new variable `n` and the induction
hypothesis `ih`; without `with` they are the inaccessible `n✝`, `a✝`. `‹_›` (typed `\f<`, `\f>`) is
"the hypothesis in the context whose type is the expected one"; it reaches inaccessible names (E012). -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : Nat) : P n := by
  induction n
  exact h0
  exact hs _ ‹_›

example (P : Nat → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) (n : Nat) : P n := by
  induction n with
    | zero => exact h0
    | succ n ih => exact hs n ih

/-! ## Arithmetic on the index -/

/-! ### R4. `omega` · closes linear arithmetic over `Nat`/`Int` (`+`, `-`, `*` by a literal, `/`, `%`
by a literal), using the hypotheses in the context. -/
example (m k : Nat) (hk : m = 5 * k) : m + 5 = 5 * (k + 1) := by
  omega

/-! ### R5. `have h : a = b := by omega`, then `rw [h]` · goal: the index `a` → `b`
A rule's conclusion has a fixed shape (`_ + 3`). Rewrite the index into that shape before `apply`. -/
example (n : Nat) (P : Nat → Prop) (hp : P (5 * n + 5)) : P (5 * (n + 1)) := by
  have h : 5 * (n + 1) = 5 * n + 5 := by omega
  rw [h]
  exact hp

/-! ## Induction on a derivation -/

/-! ### R6. `induction h` (`h : Step3 n`) · goal list: one goal per rule, the index replaced by the
rule's conclusion; the `next` goal gets the premise `a✝ : Step3 n✝` and the induction hypothesis
`a_ih✝ : Q n✝`. Name them with `induction h with | base => … | next m hm ih => …`.
The index of `h` must be a variable (`h : Step3 n`); every `n` in the goal is then replaced per rule.
On `h : Step3 (n + 3)` Lean refuses: "Index in target's type is not a variable"; use `cases` (R11). -/
example (Q : Nat → Prop) (h0 : Q 0) (hs : ∀ m, Q m → Q (m + 3)) (n : Nat) (h : Step3 n) : Q n := by
  induction h
  exact h0
  exact hs _ ‹_›

example (Q : Nat → Prop) (h0 : Q 0) (hs : ∀ m, Q m → Q (m + 3)) (n : Nat) (h : Step3 n) : Q n := by
  induction h with
    | base => exact h0
    | next m hm ih => exact hs m ih

/-! ## Existentials -/

/-! ### R7. `refine ⟨w, ?_⟩` · goal `∃ k, P k` → `P w`; `exact ⟨w, proof⟩` does both at once
`⟨w, proof⟩` is the anonymous constructor of `Exists`: a witness and a proof about it. A goal such as
`0 = 5 * 0` closes by `rfl` (both sides compute to `0`). -/
example (P : Nat → Prop) (w : Nat) (h : P w) : ∃ k, P k := by
  refine ⟨w, ?_⟩
  exact h

example : ∃ k, 0 = 5 * k := by
  exact ⟨0, rfl⟩

/-! ### R8. `obtain ⟨k, hk⟩ := h` · context: `h : ∃ k, P k` → `k : Nat` and `hk : P k` -/
example (P : Nat → Prop) (G : Prop) (g : ∀ k, P k → G) (h : ∃ k, P k) : G := by
  obtain ⟨k, hk⟩ := h
  exact g k hk

/-! ## Inversion: what a derivation of a given index can be -/

/-! ### R9. `intro h` on `¬ A` · goal `¬ A` → `False`, context gains `h : A`
`¬ A` is defined as `A → False`, so `intro` works on it like on any implication. -/
example (A : Prop) (f : A → False) : ¬ A := by
  intro h
  exact f h

/-! ### R10. `cases h` with no rule able to produce `h`'s index · closes the goal
`h : Step3 1`: `base` would need `1 = 0`, `next m` would need `1 = m + 3`; both are impossible on
`Nat`, so `cases` leaves no goal at all. -/
example (G : Prop) (h : Step3 1) : G := by
  cases h

/-! ### R11. `cases h` with one possible rule · context: `h : Step3 (n + 3)` → its premise `a✝ : Step3 n`
Only `next` concludes `_ + 3` (`base` would need `n + 3 = 0`), and `m + 3 = n + 3` forces `m = n`.
Name the premise with `cases h with | next _ h' => …`. -/
example (n : Nat) (P : Prop) (g : Step3 n → P) (h : Step3 (n + 3)) : P := by
  cases h
  exact g ‹_›

example (n : Nat) (P : Prop) (g : Step3 n → P) (h : Step3 (n + 3)) : P := by
  cases h with
    | next _ h' => exact g h'

/-! # Part W · Worked combinations (on `Step3`, not the exercise's `Ev`) -/

/-! ### W1. A concrete derivation, as a term and step by step (R2, R2, R2, R1) -/
example : Step3 9 := .next _ (.next _ (.next _ .base))

example : Step3 9 := by
  apply Step3.next
  apply Step3.next
  apply Step3.next
  exact .base

/-! ### W2. Why reshape the index first (R5 before R2)
On `Step3 (3 * (n + 1))`, `apply Step3.next` still succeeds, but only by unfolding `*`: the new goal
reads `Step3 (Nat.mul 3 n)`, no longer `3 * n`, and `exact ih` relies on Lean seeing through that.
After `rw` with `3 * (n + 1) = 3 * n + 3` the premise is `Step3 (3 * n)`, syntactically `ih`. -/
example (n : Nat) (ih : Step3 (3 * n)) : Step3 (3 * (n + 1)) := by
  apply Step3.next
  exact ih

example (n : Nat) (ih : Step3 (3 * n)) : Step3 (3 * (n + 1)) := by
  rw [show 3 * (n + 1) = 3 * n + 3 by omega]
  apply Step3.next
  exact ih

/-! ### W3. Induction on a derivation, finished by arithmetic (R6, R4) -/
example (n : Nat) (h : Step3 n) : n % 3 = 0 := by
  induction h
  rfl
  omega

/-! ### W4. Two inversions in a row: `¬ Step3 4` (R9, R11, R10)
`4` can only come from `next 1`, and `1` from no rule. -/
example : ¬ Step3 4 := by
  intro h
  cases h with
    | next _ h' => cases h'

end M004Guide
