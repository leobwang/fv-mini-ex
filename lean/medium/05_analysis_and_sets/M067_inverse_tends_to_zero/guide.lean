/- Guide for M067 (1/(n+1) tends to 0).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the bound `5 < k`, the
sequence `2 / (k + 3)`).
Assumed: Lean basics.
-/
import Mathlib

namespace M067Guide

/-! # Part R · Reference entries -/

/-! ## Opening the ε-N statement -/

/-! ### R1. `intro ε hε` · goal: a definition whose body is `∀ ε > 0, …` → context gains `ε`, `hε`
`intro` unfolds a definition by itself when its body starts with `∀`. `∀ ε > 0, Q ε` is
`∀ ε, ε > 0 → Q ε`, so it takes two names. -/
def AllPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

example (Q : ℝ → Prop) (h : ∀ ε, ε > 0 → Q ε) : AllPos Q := by
  intro ε hε
  exact h ε hε

/-! ### R2. `refine ⟨K, fun k hk => ?_⟩` · goal `∃ N, ∀ n ≥ N, S n` → context gains `k`, `hk : k ≥ K`; goal `S k`
The anonymous constructor `⟨…⟩` gives the witness `K` and, as a `fun`, the proof of the `∀` part.
`∀ n ≥ N, S n` is `∀ n, n ≥ N → S n`, so the `fun` takes two names. Write `_` for a name you never use. -/
example (S : ℕ → Prop) (K : ℕ) (h : ∀ k, k ≥ K → S k) : ∃ N : ℕ, ∀ n ≥ N, S n := by
  refine ⟨K, fun k hk => ?_⟩
  exact h k hk

/-! ## Constant sequences -/

/-! ### R3. `simp` · goal: `|(fun _ => a) k - a| < e` → `0 < e`
It beta-reduces `(fun _ => a) k` to `a`, then uses `sub_self : a - a = 0`, `abs_zero : |0| = 0`,
and rewrites `x > y` as `y < x`. -/
example (a e : ℝ) (k : ℕ) (h : 0 < e) : |(fun _ => a) k - a| < e := by
  simp
  exact h

/-! ### R4. `simpa using h` · closes the goal: `simp` both the goal and `h`, then `exact h`
Here `h : e > 0` is simplified to `0 < e`, the same as the simplified goal. -/
example (a e : ℝ) (k : ℕ) (h : e > 0) : |(fun _ => a) k - a| < e := by
  simpa using h

/-! ## Choosing `N`: the Archimedean property -/

/-! ### R5. `obtain ⟨x, hx⟩ := e` · `e : ∃ x, Q x` → context gains `x` and `hx : Q x` -/
example {α : Type} (Q : α → Prop) (G : Prop) (e : ∃ x, Q x) (h : ∀ x, Q x → G) : G := by
  obtain ⟨x, hx⟩ := e
  exact h x hx

/-! ### R6. `exists_nat_gt` · `∀ x : ℝ, ∃ n : ℕ, x < ↑n` (Archimedean property) · context gains `K`, `hK`
In general `{R : Type} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] (x : R)`;
`ℝ` and `ℚ` qualify. Use it with R5. -/
example (x : ℝ) (G : Prop) (h : ∀ K : ℕ, x < K → G) : G := by
  obtain ⟨K, hK⟩ := exists_nat_gt x
  exact h K hK

/-! ### R7. `exact_mod_cast h` · context gains the ℕ fact `h` cast to `ℝ`
`(a : ℝ)` is the cast `↑a` (`Nat.cast`). `exact_mod_cast` moves the casts out (`Nat.cast_le`) and
then uses `h`. `k ≥ K` is notation for `K ≤ k`, so it fits either way round. -/
example (a b : ℕ) (hab : b ≥ a) (G : Prop) (h : (a : ℝ) ≤ b → G) : G := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact h hab'

/-! ## Simplifying `|x - 0| < ε` -/

/-! ### R8. `sub_zero` · `a - 0 = a` · goal: `a - 0` → `a`
In general `{G : Type} [SubNegZeroMonoid G] (a : G)`; `ℤ`, `ℚ`, `ℝ`, `ℂ` qualify. -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) : P (a - 0) := by
  rw [sub_zero]
  exact h

/-! ### R9. `abs_of_pos` · `0 < a → |a| = a` · goal rewritten, plus side goal `0 < a`
Write `rw [abs_of_pos (by positivity)]` to close the side goal on the spot. In general
`{α : Type} [Lattice α] [AddGroup α] [AddLeftMono α] {a : α}`; `ℤ`, `ℚ`, `ℝ` qualify. -/
example (a : ℝ) (P : ℝ → Prop) (h : P a) (ha : 0 < a) : P |a| := by
  rw [abs_of_pos]
  exact h
  exact ha

/-! ### R10. `positivity` · closes `0 < e`, `0 ≤ e`, `e ≠ 0` when `e` is built from positive pieces
It knows numerals, casts `↑k` of naturals (`0 ≤ ↑k`), `+`, `*`, `/`, and beta-reduces `(fun k => …) k`. -/
example (k : ℕ) : 0 < (fun k : ℕ => 2 / ((k : ℝ) + 3)) k := by
  positivity

/-! ## Clearing the denominator -/

/-! ### R11. `div_lt_iff₀` · `0 < c → (b / c < a ↔ b < a * c)` · goal `b / c < a` → `b < a * c`
In general `{G₀ : Type} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}`;
`ℚ` and `ℝ` qualify. Give the positivity proof: `div_lt_iff₀ hc` or `div_lt_iff₀ (by positivity)`. -/
example (a b c : ℝ) (hc : 0 < c) (h : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact h

/-! ### R12. `rw [l] at h` · context: hypothesis `h` rewritten (here by R11); goal unchanged -/
example (a b c : ℝ) (hc : 0 < c) (hb : b / c < a) (G : Prop) (h : b < a * c → G) : G := by
  rw [div_lt_iff₀ hc] at hb
  exact h hb

/-! ## Finishing -/

/-! ### R13. `nlinarith` · closes a (non)linear inequality that follows from the hypotheses
`linarith` only adds hypotheses times positive constants, so it cannot use `x ≤ y` and `0 < e`
to get `e * x ≤ e * y`. `nlinarith` also multiplies pairs of hypotheses, which gives that product. -/
example (x y e : ℝ) (he : 0 < e) (hxy : x ≤ y) (h1 : 1 < x * e) : 1 < e * (y + 2) := by
  nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Eventually `5 < k`: R6 with R5, then R2, R7, finish with `linarith` -/
example : ∃ K : ℕ, ∀ k ≥ K, (5 : ℝ) < k := by
  obtain ⟨K, hK⟩ := exists_nat_gt (5 : ℝ)
  refine ⟨K, fun k hk => ?_⟩
  have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-! ### W2. One bound for the sequence `2 / (k + 3)`: R8, R9 with R10, R11, R12, R13 -/
example (e : ℝ) (he : e > 0) (K k : ℕ) (hK : 2 / e < K) (hk : (K : ℝ) ≤ k) :
    |2 / ((k : ℝ) + 3) - 0| < e := by
  rw [sub_zero]
  rw [abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ he] at hK
  nlinarith

end M067Guide
