/- Guide for H030 (√2 is irrational).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (3 and 5 instead of 2, an
abstract descent).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H030Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · descent over ℕ -/

/-! ### R1. `induction q using Nat.strong_induction_on generalizing p with | _ q ih => ?_` · context gains `ih`
Strong induction: to prove `P p q` for every `q`, prove it for `q` assuming it for every `m < q`.
`generalizing p` keeps `p` universally quantified inside `ih`, so `ih` may be used with another `p`.
`?_` leaves the case as an ordinary goal (write the proof below, at the same indentation). -/
example (P : ℕ → ℕ → Prop) (step : ∀ q, (∀ m < q, ∀ p, P p m) → ∀ p, P p q) (p q : ℕ) :
    P p q := by
  induction q using Nat.strong_induction_on generalizing p with | _ q ih => ?_
  exact step q ih p

/-! ### R2. `intro h` on `a ≠ b` · goal `a ≠ b` → `False`, context gains `h : a = b`
`a ≠ b` is notation for `a = b → False`, so `intro` works on it. -/
example {α : Type} (a b : α) (hne : a = b → False) : a ≠ b := by
  intro h
  exact hne h

/-! ### R3. `⟨c, h⟩ : a ∣ b` · builds a divisibility proof from `h : b = a * c`
`a ∣ b` (typed `\mid`) means `∃ c, b = a * c`, so an anonymous constructor proves it.
`show T from e` checks that `e` proves `T`; use it when Lean cannot guess `T` by itself. -/
example (a b c : ℕ) (h : b = a * c) : a ∣ b := by
  exact show a ∣ b from ⟨c, h⟩

/-! ### R4. `Nat.prime_two.dvd_of_dvd_pow` · context gains `2 ∣ m` from `2 ∣ m ^ n`
`Nat.Prime.dvd_of_dvd_pow : Nat.Prime p → p ∣ m ^ n → p ∣ m` and `Nat.prime_two : Nat.Prime 2`.
Dot notation: `Nat.prime_two.dvd_of_dvd_pow h` is `Nat.Prime.dvd_of_dvd_pow Nat.prime_two h`. -/
example (m n : ℕ) (h : 2 ∣ m ^ n) (P : Prop) (hP : 2 ∣ m → P) : P := by
  have hm : 2 ∣ m := Nat.prime_two.dvd_of_dvd_pow h
  exact hP hm

/-! ### R5. `obtain ⟨k, rfl⟩ : 2 ∣ p := e` · context: `p` is replaced by `2 * k` everywhere
`e` proves `2 ∣ p`, i.e. `∃ k, p = 2 * k`; the pattern `rfl` substitutes the equation away. -/
example (P : ℕ → Prop) (p : ℕ) (hd : 2 ∣ p) (hp : P p) (h : ∀ k, P (2 * k) → False) : False := by
  obtain ⟨k, rfl⟩ : 2 ∣ p := hd
  exact h k hp

/-! ### R6. `linarith` · closes a linear (in)equality that follows from the hypotheses
It first normalises with `ring_nf`, so `(3 * a) ^ 2` counts as `9 * a ^ 2` and `a ^ 2` is one unknown. -/
example (a b : ℕ) (h : (3 * a) ^ 2 = 3 * b ^ 2) : b ^ 2 = 3 * a ^ 2 := by
  linarith

/-! ### R7. `exact hne … e` · closes `False` by feeding an equation to a `≠` fact
A proof of `x ≠ y` is a function from `x = y` to `False`. `∀ m < q, X` means `∀ m, m < q → X`,
so the arguments are: `m`, a proof of `m < q`, `p`, a proof of `0 < m`, the equation. -/
example (f g : ℕ → ℕ → ℕ) (q : ℕ) (ih : ∀ m < q, ∀ (p : ℕ), 0 < m → f p m ≠ g p m)
    (m p : ℕ) (hm : m < q) (hpos : 0 < m) (e : f p m = g p m) : False := by
  exact ih m hm p hpos e

/-! ### R8. `omega` · closes linear arithmetic over `ℕ` and `ℤ` (constants times variables, `<`, `≤`, `=`) -/
example (m : ℕ) (h : 0 < 3 * m) : m < 3 * m := by
  omega

/-! ## Part 2 · from ℝ back to ℕ -/

/-! ### R9. `rw [irrational_iff_ne_rational]` · goal `Irrational x` → `∀ a b : ℤ, b ≠ 0 → x ≠ ↑a / ↑b`
`Irrational x` is defined as `x ∉ Set.range Rat.cast` (x is not the image of a rational). -/
example (x : ℝ) (h : ∀ a b : ℤ, b ≠ 0 → x ≠ a / b) : Irrational x := by
  rw [irrational_iff_ne_rational]
  exact h

/-! ### R10. `intro a b hb h` · strips `∀ a b`, `b ≠ 0 →` and the final `≠` (R2) in one step -/
example (f g : ℤ → ℤ → ℝ) (hfg : ∀ a b : ℤ, b ≠ 0 → f a b = g a b → False) :
    ∀ a b : ℤ, b ≠ 0 → f a b ≠ g a b := by
  intro a b hb h
  exact hfg a b hb h

/-! ### R11. `exact_mod_cast h` · closes a goal that is `h` up to casts `↑` (ℕ → ℤ → ℝ)
Both directions: up (`b ≠ 0` gives `(↑b : ℝ) ≠ 0`) and down (an equation of casts in ℝ gives
the equation in ℤ). -/
example (b : ℤ) (hb0 : b ≠ 0) : (b : ℝ) ≠ 0 := by
  exact_mod_cast hb0

example (a b : ℤ) (h : (a : ℝ) ^ 2 = 3 * (b : ℝ) ^ 2) : a ^ 2 = 3 * b ^ 2 := by
  exact_mod_cast h

/-! ### R12. `have := Real.sq_sqrt hx` · context gains `this : √x ^ 2 = x`
`Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`. A concrete `hx` is written `(show (0 : ℝ) ≤ 3 by norm_num)`.
`have :=` with no name calls the new fact `this`. -/
example (x : ℝ) (hx : 0 ≤ x) (P : Prop) (hP : √x ^ 2 = x → P) : P := by
  have := Real.sq_sqrt hx
  exact hP this

/-! ### R13. `rw [h] at hs` · rewrites a hypothesis instead of the goal -/
example (P : ℝ → Prop) (s t : ℝ) (h : s = t) (hs : P s) : P t := by
  rw [h] at hs
  exact hs

/-! ### R14. `div_pow` · `(a / b) ^ n = a ^ n / b ^ n` -/
example {α : Type} [DivisionCommMonoid α] (a b : α) (n : ℕ) (hs : (a / b) ^ n = a) :
    a ^ n / b ^ n = a := by
  rw [div_pow] at hs
  exact hs

/-! ### R15. `field_simp at hs` · hypothesis: clears denominators it knows are nonzero
It needs the fact `hb : b ≠ 0` in the context. The factor order of the result is `field_simp`'s choice
(here `b * c`, not `c * b`): read it in the infoview before the next step. -/
example (a b c : ℝ) (hb : b ≠ 0) (hs : a / b = c) : a = b * c := by
  field_simp at hs
  exact hs

/-! ### R16. `have := congrArg f h` · context gains `this : f x = f y` from `h : x = y` -/
example (x y : ℤ) (h : x = y) (P : Prop) (hP : x.natAbs = y.natAbs → P) : P := by
  have := congrArg Int.natAbs h
  exact hP this

/-! ### R17. `Int.natAbs_mul` · `(a * b).natAbs = a.natAbs * b.natAbs`
`Int.natAbs : ℤ → ℕ` is the absolute value as a natural number, printed `a.natAbs`. -/
example (a b : ℤ) (P : ℕ → Prop) (h : P (a.natAbs * b.natAbs)) : P (a * b).natAbs := by
  rw [Int.natAbs_mul]
  exact h

/-! ### R18. `Int.natAbs_pow` · `(n ^ k).natAbs = n.natAbs ^ k` -/
example (n : ℤ) (k : ℕ) (P : ℕ → Prop) (h : P (n.natAbs ^ k)) : P (n ^ k).natAbs := by
  rw [Int.natAbs_pow]
  exact h

/-! ### R19. `simpa [l₁, l₂] using h` · closes the goal: simplifies `h` and the goal with the
lemmas `lᵢ` (plus `simp`'s defaults, e.g. `(3 : ℤ).natAbs = 3`), then matches them -/
example (a b : ℤ) (h : (a * b).natAbs = 7) : a.natAbs * b.natAbs = 7 := by
  simpa [Int.natAbs_mul] using h

/-! ### R20. `Int.natAbs_pos.mpr` · `0 < a.natAbs ↔ a ≠ 0`; `.mpr` uses it right to left
For `hiff : A ↔ B`, `hiff.mp : A → B` and `hiff.mpr : B → A`. -/
example (a : ℤ) (ha : a ≠ 0) : 0 < a.natAbs := by
  exact Int.natAbs_pos.mpr ha

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Abstract descent: if every witness has a smaller witness, there is none (R1, R2, R7) -/
example (P : ℕ → Prop) (h : ∀ n, P n → ∃ m < n, P m) (n : ℕ) : ¬ P n := by
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro hn
  obtain ⟨m, hm, hPm⟩ := h n hn
  exact ih m hm hPm

/-! ### W2. One divisibility step with 3 instead of 2 (R3, R4, R5, R6) -/
example (p q : ℕ) (h : p ^ 2 = 3 * q ^ 2) : ∃ k, q ^ 2 = 3 * k ^ 2 := by
  obtain ⟨k, rfl⟩ : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ 2 from ⟨q ^ 2, h⟩)
  exact ⟨k, by linarith⟩

/-! ### W3. From an equation of real casts to `ℕ` (R11, R16, R19 with R17, R18) -/
example (a b : ℤ) (h : (a : ℝ) ^ 2 = 5 * (b : ℝ) ^ 2) : a.natAbs ^ 2 = 5 * b.natAbs ^ 2 := by
  have h' : a ^ 2 = 5 * b ^ 2 := by exact_mod_cast h
  have := congrArg Int.natAbs h'
  simpa [Int.natAbs_mul, Int.natAbs_pow] using this

end H030Guide
