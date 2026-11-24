/- Guide for E089 (Induction from a base).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
R1 and R6 use `?_` for the new goals so that they show up in the infoview; in the exercise you may put
the tactics right after each `=>` / `:=` instead.
Part W: worked combinations on inequalities that are NOT the exercise's.
Assumed: Lean basics (E001–E033: `induction` (E014), `omega` (E011), `calc` (E020), `rw`, `have`).
-/
import Mathlib

namespace E089Guide

/-! # Part R · Reference entries -/

/-! ## Induction that starts at `n₀` -/

/-! ### R1. `induction n, hn using Nat.le_induction with | base => ?_ | succ k hk ih => ?_` · goal list
For a goal about `n` with `hn : n₀ ≤ n` in the context: one goal → two. Case `base`: `n` is replaced
by `n₀`. Case `succ`: the goal is for `k + 1`, and the context gains `k`, `hk : n₀ ≤ k` and the
induction hypothesis `ih`, the goal for `k`. Both `n` and `hn` must be named after `induction`. -/
example (n₀ : ℕ) (P : ℕ → Prop) (h0 : P n₀) (hs : ∀ k, n₀ ≤ k → P k → P (k + 1)) (n : ℕ)
    (hn : n₀ ≤ n) : P n := by
  induction n, hn using Nat.le_induction with | base => ?_ | succ k hk ih => ?_
  · exact h0
  · exact hs k hk ih

/-! ### R2. `norm_num` · closes a goal made of numerals (`+`, `*`, `^`, `≤` on literals) -/
example : (5 : ℕ) ^ 2 ≤ 3 ^ 3 := by
  norm_num

/-! ## The step `k → k + 1` -/

/-! ### R3. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal: peel one factor off a power -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ### R4. `omega` · closes linear (in)equalities over `ℕ`/`ℤ` from the hypotheses
Any non-linear piece, such as `3 ^ k` or `k ^ 2`, is treated as one opaque number (an *atom*). -/
example (k : ℕ) (hk : 1 ≤ k) (ih : 3 * k ≤ 3 ^ k) : 3 * k + 3 ≤ 3 ^ k * 3 := by
  omega

/-! ### R5. `nlinarith` · closes polynomial (in)equalities; it multiplies hypotheses pairwise first -/
example (x : ℕ) (hx : 3 ≤ x) : 3 * x ≤ x ^ 2 := by
  nlinarith

/-! ### R6. `calc` · goal `a ≤ d` → one goal per link of the chain `a = b ≤ c = d`
The first term must be the goal's left side, the last term its right side. -/
example {α : Type} [Preorder α] (a b c d : α) (h1 : a = b) (h2 : b ≤ c) (h3 : c = d) : a ≤ d := by
  calc a = b := ?_
    _ ≤ c := ?_
    _ = d := ?_
  exacts [h1, h2, h3]

/-! ### R7. `ring` · closes an identity of commutative (semi)rings, `ℕ` included
Exponents of the form `n + 1` with a variable `n` are fine. -/
example {R : Type} [CommSemiring R] (a : R) (n : ℕ) : a ^ (n + 1) + a ^ n = a ^ n * (a + 1) := by
  ring

/-! # Part W · Worked combinations (not the exercise's inequalities) -/

/-! ### W1. R1, then R2 in `base`, R3 → R4 in `succ` -/
example (n : ℕ) (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with | base => ?_ | succ k hk ih => ?_
  · norm_num
  rw [pow_succ]
  omega

/-! ### W2. A helper by R5, then a chain by R6 with R7, R4, R7 -/
example (n : ℕ) (hn : 2 ≤ n) : n ^ 2 ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with | base => ?_ | succ k hk ih => ?_
  · norm_num
  have h : 2 * k + 1 ≤ 2 * k ^ 2 := by nlinarith
  calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
    _ ≤ 3 ^ k + 2 * 3 ^ k := by omega
    _ = 3 ^ (k + 1) := by ring

end E089Guide
