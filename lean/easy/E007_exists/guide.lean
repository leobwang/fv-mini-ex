/- Guide for E007 (Exists).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`{α : Type}` is any type (`Nat` in the exercise). `P Q : α → Prop` are predicates: `P w` is a
statement about the value `w : α`. `G : Prop` is "any goal" when the step does not look at it.
A hypothesis `k` in an entry is only there to finish the example; it shows what the goal became.
The one fact behind every entry: a proof of `∃ x, P x` is a PAIR `⟨w, hw⟩` of a witness `w : α` and
a proof `hw : P w`. To prove `∃`, build the pair; to use `∃`, take the pair apart.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001 (`rfl`, `decide`), E003 (`intro`, `exact`, `apply`), E004 (`⟨_, _⟩`, `fun`),
E005 (`obtain ⟨_, _⟩ := h`, `rintro ⟨_, _⟩` on `∧`).
-/

namespace E007Guide

/-! # Part R · Reference entries -/

/-! ## Proving an `∃`: give the witness, then the proof -/

/-! ### R1. `exact ⟨w, hw⟩` · closes `∃ x, P x` from a witness `w : α` and `hw : P w`
The anonymous constructor (E004) builds `Exists.intro w hw`. The witness comes FIRST. -/
example {α : Type} (P : α → Prop) (w : α) (hw : P w) : ∃ x, P x := by
  exact ⟨w, hw⟩

/-! ### R2. `refine ⟨w, ?_⟩` · goal `∃ x, P x` → `P w`
Commit to the witness now; `?_` is a hole that becomes the next goal, with `x` replaced by `w`. -/
example {α : Type} (P : α → Prop) (w : α) (k : P w) : ∃ x, P x := by
  refine ⟨w, ?_⟩
  exact k

/-! ### R3. `exists w` · goal `∃ x, P x` → `P w`, then tries to close it
`exists w` is `refine ⟨w, ?_⟩` followed by `try trivial` (`trivial` tries `rfl`, `decide`, a
hypothesis that matches, …). If that fails, the goal `P w` stays open for you. -/
example {α : Type} (P : α → Prop) (G : Prop) (w : α) (g : G) (k : G → P w) : ∃ x, P x := by
  exists w
  exact k g

example : ∃ n : Nat, n + 2 = 5 := by
  exists 3

/-! ### R4. `rfl` · closes `e = v` when both sides compute to the same value (E001)
With a concrete witness the remaining goal is closed arithmetic on `Nat`; Lean evaluates it.
`exact ⟨w, rfl⟩` does R1 and R4 in one term. -/
example : 4 + 3 = 7 := by
  rfl

/-! ## Using an `∃`: take the pair apart -/

/-! ### R5. `obtain ⟨x, hx⟩ := h` · context: `h : ∃ x, P x` → `x : α`, `hx : P x`
You do not learn WHICH value `x` is, only that it satisfies `P`. `x` is a fresh name: call it what
you like. -/
example {α : Type} (P : α → Prop) (G : Prop) (h : ∃ x, P x) (k : ∀ y, P y → G) : G := by
  obtain ⟨x, hx⟩ := h
  exact k x hx

/-! ### R6. `obtain ⟨x, ha, hb⟩ := h` · context: `h : ∃ x, P x ∧ Q x` → `x`, `ha : P x`, `hb : Q x`
Patterns nest: `⟨x, ha, hb⟩` is short for `⟨x, ⟨ha, hb⟩⟩`. Write `_` for a part you do not need:
`⟨x, _, hb⟩` keeps only `hb`. -/
example {α : Type} (P Q : α → Prop) (G : Prop) (h : ∃ x, P x ∧ Q x) (k : ∀ y, Q y → G) : G := by
  obtain ⟨x, _, hb⟩ := h
  exact k x hb

/-! ### R7. `rintro ⟨x, hx⟩` · goal `(∃ x, P x) → G` → `G`; context gains `x : α`, `hx : P x`
`intro h` followed by `obtain ⟨x, hx⟩ := h`, in one step (E005 did the same for `∧`). -/
example {α : Type} (P : α → Prop) (G : Prop) (k : ∀ y, P y → G) : (∃ x, P x) → G := by
  rintro ⟨x, hx⟩
  exact k x hx

/-! ## Building the new proof -/

/-! ### R8. `exact h w hw` · closes `Q w`: apply a `∀`-hypothesis to a value and a proof
`h : ∀ x, P x → Q x` is a function of two arguments: first the value `w`, then the proof `hw : P w`. -/
example {α : Type} (P Q : α → Prop) (h : ∀ x, P x → Q x) (w : α) (hw : P w) : Q w := by
  exact h w hw

/-! ### R9. `Nat.succ_ne_zero n : n + 1 ≠ 0` · closes `n + 1 ≠ 0`
`a ≠ b` means `¬(a = b)`, i.e. `a = b → False`: a proof of it refutes `a = b`. The lemma's name says
`succ` because `n + 1` is the successor `Nat.succ n`; `#check` prints it as `n.succ ≠ 0`. -/
example (n : Nat) : n + 1 ≠ 0 := by
  exact Nat.succ_ne_zero n

/-! ### R10. `exact ⟨w, ha, hb⟩` · closes `∃ x, A x ∧ B x`
The same flattening as R6, building instead of taking apart: `⟨w, ha, hb⟩` is `⟨w, ⟨ha, hb⟩⟩`.
The witness `w` may be any expression, e.g. `n + 1`; then `ha : A (n + 1)`, `hb : B (n + 1)`. -/
example {α : Type} (A B : α → Prop) (w : α) (ha : A w) (hb : B w) : ∃ x, A x ∧ B x := by
  exact ⟨w, ha, hb⟩

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. A concrete witness, then arithmetic: R2, R4 -/
example : ∃ n : Nat, n + n = 10 := by
  refine ⟨5, ?_⟩
  rfl

/-! ### W2. Unpack, then rebuild in another order: intro, R6, R10 -/
example (P Q : Nat → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  obtain ⟨x, hp, hq⟩ := h
  exact ⟨x, hq, hp⟩

/-! ### W3. The witness is an expression, not the unpacked name: R5, R1 -/
example (P : Nat → Prop) (h : ∃ n, P (2 * n)) : ∃ m, P m := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2 * n, hn⟩

/-! ### W4. Unpack in the intro, then push the proof through two `∀`-hypotheses: R7, R8, R1 -/
example (P Q R : Nat → Prop) (h1 : ∀ x, P x → Q x) (h2 : ∀ x, Q x → R x) :
    (∃ x, P x) → ∃ x, R x := by
  rintro ⟨x, hx⟩
  exact ⟨x, h2 x (h1 x hx)⟩

end E007Guide
