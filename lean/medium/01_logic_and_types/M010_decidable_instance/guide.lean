/- Guide for M010 (Decidable instance).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on the guide's own predicate `IsDouble n := ∃ k, k + k = n`
("n is even"), which is not the exercise's `IsSquare`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M010Guide

/-! # Part R · Reference entries -/

/-! ## Building a `Decidable` instance -/

/-! ### R1. `intro n` (term mode: `fun n => …`) · goal `DecidablePred p` → context gains `n`, goal `Decidable (p n)`
`DecidablePred p` is an abbreviation for `(n : α) → Decidable (p n)`: a function that, for each `n`,
returns a decision of `p n`. So it is introduced like a `∀`. -/
example (p : Nat → Prop) (h : ∀ n, Decidable (p n)) : DecidablePred p := by
  intro n
  exact h n

/-! ### R2. `decidable_of_iff q h` · goal `Decidable p` → goal `q ↔ p` (needs `[Decidable q]`)
`decidable_of_iff : {b : Prop} → (a : Prop) → (a ↔ b) → [Decidable a] → Decidable b` (`#check` prints
these names; here `a` is `q`, `b` is `p`): decide `p` by deciding the equivalent `q`. You choose `q`; Lean must already find an instance `Decidable q`. -/
example (p q : Prop) [Decidable q] (h : q ↔ p) : Decidable p := by
  refine decidable_of_iff q ?_
  exact h

/-! ### R3. `Nat.decidableExistsLE` (an instance) · closes `Decidable (∃ k, k ≤ n ∧ P k)`
A bounded search: Lean tries `k = 0, 1, …, n`. It needs `[DecidablePred P]`; for `P k := (a = b)` on
`Nat` that is `instDecidableEqNat`. The unbounded `∃ k, P k` has no instance. -/
example (n : Nat) (P : Nat → Prop) [DecidablePred P] : Decidable (∃ k, k ≤ n ∧ P k) := by
  exact inferInstance

/-! ## Proving the `↔` -/

/-! ### R4. `constructor` on `A ↔ B` · goal list: `A ↔ B` → `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (h1 : A → B) (h2 : B → A) : A ↔ B := by
  constructor
  exact h1
  exact h2

/-! ### R5. `rintro ⟨k, _, hk⟩` · goal `(∃ k, A k ∧ B k) → G` → context gains `k`, `A k`, `hk : B k`; goal `G`
The pattern follows the nesting `∃ k, (A k ∧ B k)`; `_` keeps the part with an unusable name `left✝`.
For `(∃ k, B k) → G` the pattern is `⟨k, hk⟩`. -/
example (A B : Nat → Prop) (G : Prop) (h : ∀ k, B k → G) : (∃ k, A k ∧ B k) → G := by
  rintro ⟨k, _, hk⟩
  exact h k hk

/-! ### R6. `refine ⟨x, ?_, hb⟩` (or `exact ⟨x, ha, hb⟩`) · goal `∃ k, A k ∧ B k` → goal `A x`
The anonymous constructor flattens: `⟨x, ha, hb⟩` means `⟨x, ⟨ha, hb⟩⟩`. In term mode, a part you still
have to prove can be written `(by …)` in place of `?_`. -/
example (A B : Nat → Prop) (x : Nat) (ha : A x) (hb : B x) : ∃ k, A k ∧ B k := by
  refine ⟨x, ?_, hb⟩
  exact ha

/-! ### R7. `rw [← h]` with `h : f k = n` · goal `P n` → `P (f k)`
Right to left: every `n` in the goal becomes `f k`, so a fact about `f k` can close it. -/
example (f : Nat → Nat) (k n : Nat) (P : Nat → Prop) (h : f k = n) (hp : P (f k)) : P n := by
  rw [← h]
  exact hp

/-! ### R8. `Nat.le_mul_self` · `Nat.le_mul_self : ∀ (n : Nat), n ≤ n * n` · closes `a ≤ a * a` -/
example (a : Nat) : a ≤ a * a := by
  exact Nat.le_mul_self a

/-! ## Deciding concrete cases -/

/-! ### R9. `decide` · closes `Q` (or `¬ Q`) when `Q` has no free variables and a `Decidable Q` instance
evaluates to `isTrue` (or `isFalse`). It runs the instance: here, the bounded search of R3. -/
example : ∃ k, k ≤ 10 ∧ k + k = 10 := by decide

example : ¬ ∃ k, k ≤ 9 ∧ k + k = 9 := by decide

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- "n is even": an unbounded `∃`, so Lean has no `Decidable` instance for it yet. -/
def IsDouble (n : Nat) : Prop := ∃ k, k + k = n

/-! ### W1. The bounded and the unbounded statement are equivalent: R4, R5, R6, R7
`rintro` and `⟨…⟩` see through the definition `IsDouble n := ∃ k, k + k = n`, so no unfolding is needed.
Written without `·` so the infoview shows a state after every line; the first two lines after
`constructor` close case `mp`, the rest close case `mpr`.
`Nat.le_add_right : ∀ (n k : Nat), n ≤ n + k` plays the role R8 plays for `*`. -/
theorem bounded_iff_isDouble (n : Nat) : (∃ k, k ≤ n ∧ k + k = n) ↔ IsDouble n := by
  constructor
  rintro ⟨k, _, hk⟩
  exact ⟨k, hk⟩
  rintro ⟨k, hk⟩
  refine ⟨k, ?_, hk⟩
  rw [← hk]
  exact Nat.le_add_right k k

/-! ### W2. The instance: R1, R2 (R3 supplies `Decidable` of the bounded side) -/
instance decIsDouble : DecidablePred IsDouble :=
  fun n => decidable_of_iff (∃ k, k ≤ n ∧ k + k = n) (bounded_iff_isDouble n)

/-! ### W3. `decide` now goes through `decIsDouble` (R9) -/
example : IsDouble 12 := by decide

example : ¬ IsDouble 13 := by decide

end M010Guide
