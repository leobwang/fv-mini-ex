/- Guide for E124 (Quantum oscillator level spacing).
Part R: one reference entry per tactic or library definition the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P : ℝ → Prop` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on an object that is NOT the exercise's (rigid-rotor levels `rot`).
Assumed: Lean basics (E001–E033).

Vocabulary (physlib, via `import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE`):
* `HarmonicOscillator` is `QuantumMechanics.OneDimension.HarmonicOscillator`, a structure with fields
  `m : ℝ` (mass), `ω : ℝ` (angular frequency) and proofs `hω : 0 < ω`, `hm : 0 < m`.
* `Q.eigenValue n` is `HarmonicOscillator.eigenValue Q n`, defined as `(n + 1/2) * ℏ * Q.ω : ℝ`, the
  energy of the n-th level.
* `ℏ` is `Constants.ℏ : {x : ℝ // 0 < x}`, reduced Planck's constant packaged with a proof that it is
  positive (a *subtype*). In a real expression Lean inserts the coercion `Subtype.val`, printed `↑ℏ`.
* `↑k` for `k : ℕ` is the cast `Nat.cast k : ℝ`, the natural number `k` seen as a real number.
-/
import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE

open QuantumMechanics OneDimension Constants

namespace E124Guide

/-! # Part R · Reference entries -/

/-! ### R1. `unfold HarmonicOscillator.eigenValue` · goal: `Q.eigenValue k` → `(↑k + 1 / 2) * ↑ℏ * Q.ω`
`unfold f` replaces every occurrence of the definition `f` (applied to anything) by its body.
The full name is needed: `Q.eigenValue` is dot notation for `HarmonicOscillator.eigenValue Q`. -/
example (Q : HarmonicOscillator) (k : ℕ) (P : ℝ → Prop) (h : P ((↑k + 1 / 2) * ℏ * Q.ω)) :
    P (Q.eigenValue k) := by
  unfold HarmonicOscillator.eigenValue
  exact h

/-! ### R2. `push_cast` · goal: casts move inward, `↑(a + b)` → `↑a + ↑b`, `↑(k + 1)` → `↑k + 1`
It rewrites with the cast lemmas `Nat.cast_add : ↑(a + b) = ↑a + ↑b` and `Nat.cast_one : ↑1 = 1`
(and the same for `*`, `^`, numerals), everywhere in the goal. -/
example (a b : ℕ) (P : ℝ → Prop) (h : P (↑a + ↑b)) : P (↑(a + b)) := by
  push_cast
  exact h

example (k : ℕ) (P : ℝ → Prop) (h : P (↑k + 1)) : P (↑(k + 1)) := by
  push_cast
  exact h

/-! ### R3. `ring` · closes an identity of commutative rings (here `ℝ`)
Anything that is not `+ - * ^`, a numeral or `/` by a numeral is an opaque unknown (an *atom*):
`↑k`, `↑ℏ`, `Q.ω` are atoms, and so is `↑(k + 1)`, which `ring` does not relate to `↑k`. -/
example (x c : ℝ) : (x + 1 / 2) * c + (x + 1 / 2) * c = (2 * x + 1) * c := by
  ring

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- Rigid-rotor levels `E_l = B · l · (l + 1)` (rotational constant `B`, angular momentum `l`). -/
noncomputable def rot (B : ℝ) (l : ℕ) : ℝ := B * l * (l + 1)

/-! ### W1. Unfold, push the casts, close: R1, R2, R3 -/
example (B : ℝ) (l : ℕ) : rot B (l + 1) - rot B l = 2 * B * (l + 1) := by
  unfold rot
  push_cast
  ring

/-! ### W2. Skipping R2: `ring_nf` keeps `↑(1 + l)` as an atom, so `ring` alone fails; push the cast
afterwards and `ring` closes it -/
example (B : ℝ) (l : ℕ) : rot B (l + 1) - rot B l = 2 * B * (l + 1) := by
  unfold rot
  ring_nf
  push_cast
  ring

end E124Guide
