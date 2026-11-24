/- Guide for E093 (abel and group).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace E093Guide

/-! # Part R · Reference entries -/

/-! ## Additive commutative groups: `abel` -/

/-! ### R1. `abel` · closes an identity built from `+`, `-`, `0` in an `AddCommGroup`
`[AddCommGroup G]`: `G` has `+` (associative, commutative), `0`, negation `-a` and `a - b`.
`ℤ`, `ℝ`, `ℂ`, vectors `Fin n → ℝ` qualify; `ℕ` does not (no negation). -/
example {G : Type} [AddCommGroup G] (a b : G) : a + b - a = b := by
  abel

/-! ### R2. `abel` with numeral multiples · closes identities involving `n • a`
`n • a` (`n : ℕ`) is `a + ⋯ + a`, `n` copies ("nsmul"). `abel` treats a numeral `n` as a known
number, so `n • (a + b)` is expanded; a *variable* `n` is not (see Traps). -/
example {G : Type} [AddCommGroup G] (a b : G) : 2 • (a + b) - a = a + 2 • b := by
  abel

/-! ### R3. `abel_nf` · goal: every additive expression → `abel`'s normal form
What `abel` sees: a sum of `k • atom` with integer coefficients `k : ℤ`. Use it when `abel` fails,
to see what is left. -/
example {G : Type} [AddCommGroup G] (a b : G) (P : G → Prop)
    (h : P ((2 : ℤ) • a + (-1 : ℤ) • b)) : P (a - b + a) := by
  abel_nf
  exact h

/-! ## Groups: `group` -/

/-! ### R4. `group` · closes an identity built from `*`, `⁻¹`, `1` in a `Group`
`[Group G]`: `G` has an associative `*`, a unit `1`, and inverses `a⁻¹` (typed `\inv`) with
`a⁻¹ * a = 1`. `*` need NOT be commutative: invertible matrices and permutations qualify. -/
example {G : Type} [Group G] (a b : G) : a * b * b⁻¹ = a := by
  group

/-! ### R5. `group` with an inverse of a product · closes it; it knows `⁻¹` reverses the order -/
example {G : Type} [Group G] (a b : G) : (a * b⁻¹)⁻¹ = b * a⁻¹ := by
  group

/-! ## Using a hypothesis: `calc`, then `rw` -/

/-! ### R6. `calc` with `?_` steps · goal list: `x = z` → one goal per step
`abel` and `group` never read hypotheses. Use `calc` to pass through a middle term where a
hypothesis applies; each `?_` becomes a goal `case calc_k`. Normally you write `:= by tac` instead. -/
example {G : Type} [Group G] (x y z : G) (h₁ : x = y) (h₂ : y = z) : x = z := by
  calc x = y := ?_
    _ = z := ?_
  exact h₁
  exact h₂

/-! ### R7. `rw [h]` on a bracketed product · goal: `c * (a * b)` → `c * 1` when `h : a * b = 1`
`*` groups to the left: `c * a * b` is `(c * a) * b` and does NOT contain `a * b`. Write the
brackets yourself (in a `calc` middle term) so that `rw [h]` finds `a * b`. -/
example {G : Type} [Group G] (a b c : G) (h : a * b = 1) (P : G → Prop) (hP : P (c * 1)) :
    P (c * (a * b)) := by
  rw [h]
  exact hP

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Additive: `calc` through the hypothesis, then `abel` (R6, R7, R1) -/
example {G : Type} [AddCommGroup G] (a b c : G) (h : a + b = c) : c - b = a := by
  calc c - b = (a + b) - b := by rw [h]
    _ = a := by abel

/-! ### W2. Multiplicative, noncommutative: `rw` with a commutation fact, then `group` (R6, R7, R4) -/
example {G : Type} [Group G] (a b : G) (h : a * b = b * a) : a * b * a⁻¹ = b := by
  calc a * b * a⁻¹ = b * a * a⁻¹ := by rw [h]
    _ = b := by group

/-! ### W3. Insert a group identity first, so a hypothesis becomes usable (R6, R4, R7, R4)
Left cancellation: the goal `c = d` contains no `a * c`, so first write `c` as `a⁻¹ * (a * c)`. -/
example {G : Type} [Group G] (a c d : G) (h : a * c = a * d) : c = d := by
  calc c = a⁻¹ * (a * c) := by group
    _ = a⁻¹ * (a * d) := by rw [h]
    _ = d := by group

end E093Guide
