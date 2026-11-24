/- Guide for E038 (Even and Odd).
Part R: one reference entry per tactic or term the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`{α : Type}` is any type; a bracket such as `[Semiring α]` says what `α` must support (a type
class; `ℕ` and `ℤ` meet every bracket used here). `P : α → Prop` stands for "the rest of your
goal": the step changes only the part shown inside `P (…)`. A hypothesis `k` in an entry is only
there to finish the example; it shows what the goal or context became.
The one fact behind every entry: Mathlib DEFINES
  `Even n`  as  `∃ r, n = r + r`          (for any `α` with `+`)
  `Odd n`   as  `∃ m, n = 2 * m + 1`      (for any semiring `α`)
so both are `∃`-statements (E007): unpack a hypothesis with `obtain`, prove a goal with a witness.
Part W: worked combinations on statements that are NOT the exercise's.
Assumed: E001–E033, in particular `∃`, `obtain ⟨x, hx⟩ := h` and `refine ⟨w, ?_⟩` (E007), the
`rfl` pattern in `obtain` (E025), `by` inside a term (E004). New: `import Mathlib`, `ℕ ℤ`, `Even`,
`Odd`, and `ring`.
-/
import Mathlib

namespace E038Guide

/-! # Part R · Reference entries -/

/-! ## Using `Even` / `Odd` hypotheses: take the `∃` apart -/

/-! ### R1. `obtain ⟨r, hr⟩ := h` with `h : Even n` · context: `h` → `r : α`, `hr : n = r + r`
`Even n` unfolds to `∃ r, n = r + r`, so the `∃` pattern from E007 works on it directly. Note the
witness is the HALF `r`, and the equation is `r + r`, not `2 * r`. -/
example {α : Type} [Add α] (n : α) (P : α → Prop) (k : ∀ r, n = r + r → P n) (h : Even n) :
    P n := by
  obtain ⟨r, hr⟩ := h
  exact k r hr

/-! ### R2. `obtain ⟨r, rfl⟩ := h` with `h : Even n` · context loses `n` and `h`; goal: `n` → `r + r`
Writing `rfl` in place of a name for the equation `n = r + r` substitutes it (as in E025): the
variable `n` is replaced by `r + r` everywhere and disappears. `n` must be a local variable. -/
example {α : Type} [Add α] (n : α) (P : α → Prop) (k : ∀ r, P (r + r)) (h : Even n) : P n := by
  obtain ⟨r, rfl⟩ := h
  exact k r

/-! ### R3. `obtain ⟨m, rfl⟩ := h` with `h : Odd n` · context loses `n` and `h`; goal: `n` → `2 * m + 1`
`[Semiring α]`: `α` has `0 1 + *` with the usual laws (`ℕ`, `ℤ`, `ℚ`, `ℝ`); `Odd` needs it
because its definition mentions the numerals `2` and `1`. -/
example {α : Type} [Semiring α] (n : α) (P : α → Prop) (k : ∀ m, P (2 * m + 1)) (h : Odd n) :
    P n := by
  obtain ⟨m, rfl⟩ := h
  exact k m

/-! ## Proving `Even` / `Odd` goals: give the witness -/

/-! ### R4. `refine ⟨w, ?_⟩` on `⊢ Even a` · goal → `a = w + w`
The anonymous constructor builds the `∃` that `Even a` unfolds to; `?_` becomes the next goal. -/
example {α : Type} [Add α] (a w : α) (k : a = w + w) : Even a := by
  refine ⟨w, ?_⟩
  exact k

/-! ### R5. `refine ⟨w, ?_⟩` on `⊢ Odd a` · goal → `a = 2 * w + 1` -/
example {α : Type} [Semiring α] (a w : α) (k : a = 2 * w + 1) : Odd a := by
  refine ⟨w, ?_⟩
  exact k

/-! ## Closing the witness equation -/

/-! ### R6. `ring` · closes an equation that holds by the commutative-semiring laws alone
`[CommSemiring α]`: a semiring whose `*` is commutative (`ℕ`, `ℤ`, `ℚ`, `ℝ`). `ring` expands
both sides into sums of monomials and compares; it never reads hypotheses. A wrong witness makes
the equation false, and `ring` fails. -/
example {α : Type} [CommSemiring α] (a b : α) : 2 * a + 2 * b = (a + b) + (a + b) := by
  ring

/-! ### R7. `exact ⟨w, by ring⟩` · closes `⊢ Even a` or `⊢ Odd a` in one step
R4 (or R5) and R6 as one term: `by ring` proves the equation the `?_` would have left. -/
example {α : Type} [CommSemiring α] (a : α) : Even (2 * a) := by
  exact ⟨a, by ring⟩

/-! # Part W · Worked combinations (not the exercise's statements) -/

/-! ### W1. Even `n` → even `n + 2` over `ℕ`: R2, R4, R6 -/
example (n : ℕ) (h : Even n) : Even (n + 2) := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨r + 1, ?_⟩
  ring

/-! ### W2. Odd `n` → even `n + 1` over `ℕ`: R3, R4, R6 -/
example (n : ℕ) (h : Odd n) : Even (n + 1) := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨m + 1, ?_⟩
  ring

/-! ### W3. Odd `n` → odd `3 * n` over `ℤ`: R3, R5, R6. Witness found by expanding:
`3 * (2 * m + 1) = 6 * m + 3 = 2 * (3 * m + 1) + 1`. -/
example (n : ℤ) (h : Odd n) : Odd (3 * n) := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨3 * m + 1, ?_⟩
  ring

/-! ### W4. W3 with R7: unpack, then witness and equation in one term -/
example (n : ℤ) (h : Odd n) : Odd (3 * n) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨3 * m + 1, by ring⟩

/-! ### W5. A numeral: no hypothesis to unpack, only a witness (`7 = 2 * 3 + 1`) -/
example : Odd (7 : ℤ) := ⟨3, by ring⟩

end E038Guide
