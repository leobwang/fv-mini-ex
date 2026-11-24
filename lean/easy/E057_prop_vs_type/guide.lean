/- Guide for E057 (Prop vs Type).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the guide's own types, NOT the exercise's: the subtypes `{ m : Nat // n < m }` and
`{ n : Nat // n < 10 }`, and the Σ-type `(k : Nat) × Fin (2 * k + 1)` with the function `bound` below.
Part W: worked combinations on the same guide types.
Assumed: Lean basics (E001–E033), in particular `rfl` (E001), anonymous constructors `⟨_, _⟩` (E004),
`omega` (E011), `unfold` (E012), structures and projections (E017), `have` (E021), `refine` (E031).
-/

namespace E057Guide

/-- A function on the guide's Σ-type: twice the first component. -/
def bound (s : (k : Nat) × Fin (2 * k + 1)) : Nat := 2 * s.1

/-! # Part R · Reference entries -/

/-! ## Subtypes: a value packed with a proof -/

/-! ### R1. `refine ⟨v, ?_⟩` on a subtype · goal `{ m // p m }` → the proof obligation `p v`
In term mode the same value is written `⟨v, proof⟩`. -/
example (n : Nat) (h : n < n + 1) : { m : Nat // n < m } := by
  refine ⟨n + 1, ?_⟩
  exact h

/-! ### R2. `rfl` on two proofs · closes `h1 = h2` when `h1 h2` prove the same `Prop`
Proof irrelevance is built into Lean's definitional equality: any two proofs of one `Prop` are the
same term as far as `rfl` is concerned. -/
example (a b : Nat) (h1 h2 : a ≤ b) : h1 = h2 := by
  rfl

/-! ### R3. `apply Subtype.ext` · goal `a = b` (two subtype values) → `a.val = b.val`
`Subtype.ext : a1.val = a2.val → a1 = a2`; the proof components never need comparing (R2). -/
example (a b : { n : Nat // n < 10 }) (h : a.val = b.val) : a = b := by
  apply Subtype.ext
  exact h

/-! ## Σ-types: a pair whose second component's type depends on the first -/

/-! ### R4. `s.2` (`Sigma.snd`) · closes a goal whose type mentions `s.1`
`s.1` prints as `s.fst`, `s.2` as `s.snd`. -/
example (s : (k : Nat) × Fin (2 * k + 1)) : Fin (2 * s.1 + 1) := by
  exact s.2

/-! ### R5. `i.val` (`Fin.val`) · closes a `⊢ Nat` hole with the number inside `i : Fin m`
The infoview prints `i.val` as `↑i`. -/
example (m : Nat) (i : Fin m) : Nat := by
  exact i.val

/-! ### R6. `dsimp only` · goal: a projection of a literal pair `⟨a, b⟩.snd` → `b` -/
example (k : Nat) (i : Fin (2 * k + 1)) (P : Fin (2 * k + 1) → Prop) (h : P i) :
    P (⟨k, i⟩ : (k : Nat) × Fin (2 * k + 1)).2 := by
  dsimp only
  exact h

/-! ### R7. `rfl` through a `def` and a projection · closes `f ⟨a, b⟩ = (its value)` -/
example (k : Nat) (i : Fin (2 * k + 1)) : bound ⟨k, i⟩ = 2 * k := by
  rfl

/-! ## Bounds from a `Fin` -/

/-! ### R8. `unfold bound` · goal: the name `bound s` → its body -/
example (s : (k : Nat) × Fin (2 * k + 1)) (P : Nat → Prop) (h : P (2 * s.1)) : P (bound s) := by
  unfold bound
  exact h

/-! ### R9. `have h := i.isLt` (`Fin.isLt`) · context gains `h : ↑i < m` -/
example (m : Nat) (i : Fin m) (G : Prop) (g : i.val < m → G) : G := by
  have h := i.isLt
  exact g h

/-! ### R10. `Nat.le_of_lt_succ` · `m < n.succ → m ≤ n` (`n.succ` is `n + 1`) · closes the goal -/
example (m n : Nat) (h : m < n + 1) : m ≤ n := by
  exact Nat.le_of_lt_succ h

/-! ### R11. `exact` accepts a term whose type matches the goal only after unfolding a `def` · closes -/
example (s : (k : Nat) × Fin (2 * k + 1)) (h : 2 * s.1 ≤ 7) : bound s ≤ 7 := by
  exact h

/-! # Part W · Worked combinations (guide types, not the exercise's) -/

/-! ### W1. A subtype value, in term mode and in tactic mode (R1) -/
def above (n : Nat) : { m : Nat // n < m } := ⟨n + 1, Nat.lt_succ_self n⟩

def aboveTwo (n : Nat) : { m : Nat // n < m } := by
  refine ⟨n + 2, ?_⟩
  omega

/-! ### W2. Two subtype values with equal numbers are equal, whatever their proofs (R3, R2) -/
example (n : Nat) : above n = ⟨n + 1, by omega⟩ := by
  apply Subtype.ext
  rfl

/-! ### W3. The bound carried by the second component, two ways (R9, R8, R10, R11; or `omega`) -/
example (s : (k : Nat) × Fin (2 * k + 1)) : s.2.val ≤ bound s := by
  exact Nat.le_of_lt_succ s.2.isLt

example (s : (k : Nat) × Fin (2 * k + 1)) : s.2.val ≤ bound s := by
  have h := s.2.isLt
  unfold bound
  omega

end E057Guide
