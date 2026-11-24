/- Guide for M029 (GCD by Euclid).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about well-founded recursion use the guide's own function `dbl` (doubling `a`, `b`
times), which is NOT the exercise's `euclid` but has the same `if b = 0 then … else …` shape.
Part W: worked combinations on `dbl` and on arbitrary numbers.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M029Guide

/-- `dbl a b = a * 2 ^ b`: stop when `b = 0`, otherwise double `a` and count `b` down.
`b - 1` is not a constructor pattern, so Lean cannot see on its own that the recursion stops:
`termination_by b` names the measure (`b` gets smaller at each call) and `decreasing_by` proves
it, here `¬b = 0 ⊢ b - 1 < b` by `omega`. -/
def dbl (a b : Nat) : Nat := if b = 0 then a else dbl (a + a) (b - 1)
termination_by b
decreasing_by omega

/-! # Part R · Reference entries -/

/-! ## Induction that follows the recursion -/

/-! ### R1. `fun_induction f a b with | case1 a => … | case2 a b h ih => …` · goal list: one goal per branch
`fun_induction dbl a b` does induction along `dbl`'s own recursion, so it works where `induction b`
does not (`b - 1`, or `a % b`, is not `b`'s predecessor). One goal per branch of the `if`, with the
call `dbl a b` already replaced by that branch's right-hand side:
`case1` is `b = 0` (and `b` is replaced by `0` everywhere); `case2` is `b ≠ 0`, with the condition
`h : ¬b = 0` and `ih`, the claim for the recursive call. An arm names, in order: the variables,
the `if` condition, the IH. Here the arms are `?_`, so both goals stay open; in a proof you write the
arm's tactics after `=>`. -/
example (a b : Nat) (P : Nat → Prop) (h1 : ∀ x, P x) : P (dbl a b) := by
  fun_induction dbl a b with
    | case1 a => ?_
    | case2 a b h ih => ?_
  · exact h1 a
  · exact ih

/-! ## Conjunctions -/

/-! ### R2. `exact ⟨p, q⟩` (anonymous constructor for `And.intro`) · closes `A ∧ B`
`⟨p, q⟩` builds `A ∧ B` from `p : A` and `q : B`. The goal fixes which structure is built, so the
same brackets also build `∃` and structures. -/
example (A B : Prop) (p : A) (q : B) : A ∧ B := by
  exact ⟨p, q⟩

/-! ### R3. `h.1`, `h.2` (`And.left`, `And.right`) · context: one half of `h : A ∧ B`
`h.1 : A` and `h.2 : B`. Usually written inline as an argument (`f h.1`); here `have` shows it. -/
example (A B : Prop) (h : A ∧ B) (P : Prop) (hp : B → P) : P := by
  have hb := h.2
  exact hp hb

/-! ## Divisibility on `Nat` -/

/-! ### R4. `Nat.dvd_refl` · `Nat.dvd_refl a : a ∣ a` · closes the goal
`a ∣ b` (typed `\|`, not the bar `|`) is `Dvd.dvd a b`: `∃ c, b = a * c`. -/
example (a : Nat) : a ∣ a := by
  exact Nat.dvd_refl a

/-! ### R5. `Nat.dvd_zero` · `Nat.dvd_zero a : a ∣ 0` · closes the goal
Every number divides `0` (`0 = a * 0`), including `0` itself. -/
example (a : Nat) : a ∣ 0 := by
  exact Nat.dvd_zero a

/-! ### R6. `Nat.dvd_mod_iff` with `.mp` · `k ∣ n → (k ∣ m % n ↔ k ∣ m)` · goal `k ∣ m` → `k ∣ m % n`
The lemma's arguments `{k m n}` are implicit; you pass only the proof `hk : k ∣ n`, and get an
`↔`. `.mp` is its left-to-right direction, `(Nat.dvd_mod_iff hk).mp : k ∣ m % n → k ∣ m`. Why it
holds: `m = n * (m / n) + m % n`, and `k` divides `n`. Write the parentheses: `Nat.dvd_mod_iff.mp`
is an unknown name, because `.mp` belongs to the `↔`, which exists only after `hk` is given. -/
example (k m n : Nat) (hk : k ∣ n) (h : k ∣ m % n) : k ∣ m := by
  apply (Nat.dvd_mod_iff hk).mp
  exact h

/-! ### R7. `Nat.dvd_mod_iff` with `.mpr` · goal `k ∣ m % n` → `k ∣ m`
`.mpr` is the right-to-left direction, `(Nat.dvd_mod_iff hk).mpr : k ∣ m → k ∣ m % n`. -/
example (k m n : Nat) (hk : k ∣ n) (h : k ∣ m) : k ∣ m % n := by
  apply (Nat.dvd_mod_iff hk).mpr
  exact h

/-! ## Induction with hypotheses about the arguments -/

/-! ### R8. `fun_induction` with a hypothesis `hq` that mentions `a` or `b` · the IH becomes an implication
You do not `revert` anything: a hypothesis mentioning the induction variables is moved into every
case, rewritten for that case (in `case1` with `b` replaced by `0`), and is listed AFTER `ih`.
`ih` then asks for that hypothesis about the recursive call's arguments:
`ih : Q (a + a) → P (dbl (a + a) (b - 1))`. -/
example (a b : Nat) (Q P : Nat → Prop) (hq : Q a) (h1 : ∀ x, Q x → P x)
    (hQ : ∀ x, Q x → Q (x + x)) : P (dbl a b) := by
  fun_induction dbl a b with
    | case1 a => ?_
    | case2 a b h ih => ?_
  · exact h1 a hq
  · exact ih (hQ a hq)

/-! ### R9. `apply ih` on `ih : A → B → C` · goal list: goal `C` → goals `A`, `B`
`apply` matches the conclusion `C` against the goal and leaves one goal per premise. As a term in
one line: `exact ih pa pb`. -/
example (A B C : Prop) (ih : A → B → C) (pa : A) (pb : B) : C := by
  apply ih
  exact pa
  exact pb

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1 on `dbl`: `a` never shrinks. `Nat.le_refl a : a ≤ a`,
`Nat.le_trans : n ≤ m → m ≤ k → n ≤ k`, `Nat.le_add_right a a : a ≤ a + a` -/
theorem le_dbl (a b : Nat) : a ≤ dbl a b := by
  fun_induction dbl a b with
    | case1 a => exact Nat.le_refl a
    | case2 a b h ih => exact Nat.le_trans (Nat.le_add_right a a) ih

/-! ### W2. R8 + R9 on `dbl`: a divisor of `a` divides `dbl a b`.
`Nat.dvd_add : k ∣ m → k ∣ n → k ∣ m + n` -/
example (a b d : Nat) (hd : d ∣ a) : d ∣ dbl a b := by
  fun_induction dbl a b with
    | case1 a => exact hd
    | case2 a b h ih =>
      apply ih
      exact Nat.dvd_add hd hd

/-! ### W3. R2 with R7, and R3 with R6, on plain numbers -/
example (k m n : Nat) (hk : k ∣ n) (hm : k ∣ m) : k ∣ m % n ∧ k ∣ n := by
  exact ⟨(Nat.dvd_mod_iff hk).mpr hm, hk⟩

example (k m n : Nat) (h : k ∣ n ∧ k ∣ m % n) : k ∣ m := by
  exact (Nat.dvd_mod_iff h.1).mp h.2

end M029Guide
