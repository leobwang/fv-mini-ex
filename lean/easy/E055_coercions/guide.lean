/- Guide for E055 (Coercions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
All entries use the structure `Even2` below, NOT the exercise's `Pos`. Its coercion to `Nat` is
`Even2.half` (half the value), so that `↑e` visibly means "whatever function the instance holds".
Part W: worked combinations on `Even2`.
Assumed: Lean basics (E001–E033), in particular structures (E017) and instances (E019).
-/

namespace E055Guide

/-- An even natural number: a value packed with a proof about it. -/
structure Even2 where
  val : Nat
  even : val % 2 = 0

/-- The function behind the coercion. `@[coe]` only changes printing: `Even2.half e` shows as `↑e`. -/
@[coe] def Even2.half (e : Even2) : Nat := e.val / 2

/-- With this instance, an `Even2` may stand wherever a `Nat` is expected. -/
instance : Coe Even2 Nat := ⟨Even2.half⟩

/-! # Part R · Reference entries -/

/-! ## Building values of a structure -/

/-! ### R1. `e.val` · a data field of a structure value (`Even2.val e`) · closes a `⊢ Nat` hole -/
example (e : Even2) : Nat := by
  exact e.val

/-! ### R2. `refine ⟨v, ?_⟩` (anonymous constructor) · goal `⊢ Even2` → the proof field's statement for `v`
In term mode the same value is written `⟨v, proof⟩`. -/
example (e : Even2) (h : (e.val + 2) % 2 = 0) : Even2 := by
  refine ⟨e.val + 2, ?_⟩
  exact h

/-! ### R3. `have h := e.even` · context gains the proof field `h : e.val % 2 = 0`
A proof field is a theorem about this particular value: `e.even : e.val % 2 = 0`. -/
example (e : Even2) (G : Prop) (g : e.val % 2 = 0 → G) : G := by
  have h := e.even
  exact g h

/-! ### R4. `Nat.add_pos_left` · `{m : Nat} (h : 0 < m) (n : Nat) : 0 < m + n` · closes the goal -/
example (m n : Nat) (h : 0 < m) : 0 < m + n := by
  exact Nat.add_pos_left h n

/-! ## What `↑` is -/

/-! ### R5. `unfold Even2.half` · goal: `↑e` (the coercion) → the body of the `@[coe]` function -/
example (e : Even2) (P : Nat → Prop) (h : P (e.val / 2)) : P e := by
  unfold Even2.half
  exact h

/-! ### R6. `dsimp only` · goal: a field of a literal constructor → that field's value
`{ val := n, even := hn }` is how Lean prints the value `⟨n, hn⟩ : Even2`. -/
example (n : Nat) (hn : n % 2 = 0) (P : Nat → Prop) (h : P n) : P (Even2.mk n hn).val := by
  dsimp only
  exact h

/-! ### R7. `rfl` · closes `a = b` when both sides become the same term after unfolding definitions
It unfolds `↑`, the `@[coe]` function, other `def`s and constructor fields by itself (R5, R6). -/
example (e : Even2) : (e : Nat) = e.val / 2 := by
  rfl

/-! ## Changing the shape of a fact -/

/-! ### R8. `Nat.pos_iff_ne_zero` · `{n : Nat} : 0 < n ↔ n ≠ 0`; `.mp` is the `→` direction · closes -/
example (n : Nat) (h : 0 < n) : n ≠ 0 := by
  exact Nat.pos_iff_ne_zero.mp h

/-! ### R9. `exact` accepts a term whose type matches the goal only after unfolding `↑` · closes
`h` mentions `e.val / 2`, the goal mentions `↑e`; they are the same after R5. -/
example (e : Even2) (h : e.val / 2 ≠ 0) : (e : Nat) ≠ 0 := by
  exact h

/-! # Part W · Worked combinations (on `Even2`, not the exercise's `Pos`) -/

/-! ### W1. `rfl` through the coercion and a literal constructor (R7), and the same steps by hand (R5, R6) -/
example : ((⟨6, rfl⟩ : Even2) : Nat) = 3 := by
  rfl

example (n : Nat) (hn : n % 2 = 0) : ((⟨n, hn⟩ : Even2) : Nat) = n / 2 := by
  unfold Even2.half
  dsimp only

/-! ### W2. A new `Even2` from an old one: value, then the proof field via R3 and `omega` (R2, R3) -/
def Even2.double (e : Even2) : Even2 := by
  refine ⟨2 * e.val, ?_⟩
  omega

def Even2.addFour (e : Even2) : Even2 := by
  refine ⟨e.val + 4, ?_⟩
  have h := e.even
  omega

/-! ### W3. When `rfl` is not enough: `↑e.double = e.val` needs arithmetic (R5, R6, then `omega`) -/
example (e : Even2) : (e.double : Nat) = e.val := by
  unfold Even2.half Even2.double
  dsimp only
  omega

/-! ### W4. `0 < x` to `x ≠ 0` (R8), accepted against the coerced goal `↑e ≠ 0` (R9) -/
example (e : Even2) (h4 : 4 ≤ e.val) : (e : Nat) ≠ 0 := by
  have h : 0 < e.val / 2 := by omega
  exact Nat.pos_iff_ne_zero.mp h

end E055Guide
