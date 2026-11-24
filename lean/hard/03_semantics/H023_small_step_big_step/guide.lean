/- Guide for H023 (Small-step and big-step IMP agree).
Part R: one reference entry per tactic or proof-term move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal". A hypothesis `h…` in an entry is only there to finish the
example; it shows what the goal became.
The entries work on three small objects defined below, NOT the exercise's:
  `Rtc r`  the reflexive-transitive closure of a relation `r` (same shape as `Star`),
  `Tm`     a tiny expression language with a big-step evaluation `Ev` and a small step `Step`,
  `Inc`    a one-rule step relation on pairs `Nat × Nat`.
Part W: worked combinations of the entries on those objects.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace H023Guide

/-- Zero or more `r`-steps from `a` to `c`. `refl` takes its point explicitly, `step` implicitly. -/
inductive Rtc {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Rtc r a a
  | step {a b c : α} : r a b → Rtc r b c → Rtc r a c

/-- Expressions: a literal, a sum, and a nondeterministic choice `pick a b`. -/
inductive Tm where
  | lit (n : Nat)
  | add (a b : Tm)
  | pick (a b : Tm)

/-- Big-step evaluation `Ev t v`: `t` can evaluate to the value `v`. -/
inductive Ev : Tm → Nat → Prop
  | lit {n : Nat} : Ev (.lit n) n
  | add {a b : Tm} {m n : Nat} : Ev a m → Ev b n → Ev (.add a b) (m + n)
  | pickL {a b : Tm} {n : Nat} : Ev a n → Ev (.pick a b) n
  | pickR {a b : Tm} {n : Nat} : Ev b n → Ev (.pick a b) n

/-- One small step on expressions: add two literals, or step inside the left operand. -/
inductive Step : Tm → Tm → Prop
  | addLit {m n : Nat} : Step (.add (.lit m) (.lit n)) (.lit (m + n))
  | addL {a a' b : Tm} : Step a a' → Step (.add a b) (.add a' b)

/-- One step on pairs: bump the first component, keep the second. -/
inductive Inc : Nat × Nat → Nat × Nat → Prop
  | mk {n m : Nat} : Inc (n, m) (n + 1, m)

/-! # Part R · Reference entries -/

/-! ## Building derivations -/

/-! ### R1. `refine .step hab ?_` / `exact .refl _` · goal: apply a constructor of an inductive predicate
`.step` means `Rtc.step`: Lean reads the constructor name off the goal's type. Implicit arguments
(`a b c`) are found by matching the goal; each `?_` becomes a new goal. -/
example {α : Type} (r : α → α → Prop) (a b c : α) (hab : r a b) (hbc : Rtc r b c) : Rtc r a c := by
  refine .step hab ?_
  exact hbc

example {α : Type} (r : α → α → Prop) (a : α) : Rtc r a a := by
  exact .refl _

/-! ## Induction on a derivation -/

/-! ### R2. `induction h with | refl x => … | step hab hbc ih => …` · goal list: one goal per constructor
Works directly when the indices of `h`'s type (`a b` in `Rtc r a b`) are distinct variables. The `step`
goal gains the constructor's explicit fields `hab hbc` and the induction hypothesis `ih` for `hbc`. The
implicit fields (`a b c` of `step`) stay unnamed: `a✝² b✝ c✝`. -/
example {α : Type} (r : α → α → Prop) (P : α → α → Prop) (a b : α) (h : Rtc r a b)
    (hP : ∀ x y, P x y) : P a b := by
  induction h with
    | refl x => ?_
    | step hab hbc ih => ?_
  exact hP _ _
  exact hP _ _

/-! ### R3. `| @step x y z hxy hyz ih => …` · context: name the implicit fields too
With `@`, the pattern lists every field in order, implicit ones included (`_` skips one). -/
example {α : Type} (r : α → α → Prop) (P : α → α → Prop) (a b : α) (h : Rtc r a b)
    (hP : ∀ x y, P x y) : P a b := by
  induction h with
    | refl x => ?_
    | @step x y z hxy hyz ih => ?_
  exact hP _ _
  exact hP _ _

/-! ### R4. `generalize hp : (a, b) = p at h` · context: a compound index becomes a variable
`induction h` refuses `h : Rtc r (a, b) q` ("index in target's type is not a variable"). `generalize`
replaces the term `(a, b)` in `h` by a fresh variable `p` and records `hp : (a, b) = p`. -/
example {α β : Type} (r : α × β → α × β → Prop) (a : α) (b b' : β) (P : Prop)
    (h : Rtc r (a, b) (a, b')) (hP : ∀ p, Rtc r p (a, b') → P) : P := by
  generalize hp : (a, b) = p at h
  exact hP p h

/-! ### R5. `induction h generalizing a b` · context: the induction hypothesis holds for ALL `a b`
`hp : (a, b) = p` mentions the index `p`, so `induction` carries it along: it becomes a premise of `ih`.
Without `generalizing a b`, `ih` would only speak about the original `(a, b)`; with it, `ih` is
`∀ {a b}, (a, b) = y → …`, usable at the middle point `y`. -/
example {α β : Type} (r : α × β → α × β → Prop) (P : α → β → Prop) (p q : α × β) {a : α} {b : β}
    (hp : (a, b) = p) (h : Rtc r p q) (hP : ∀ x y, P x y) : P a b := by
  induction h generalizing a b with
    | refl x => ?_
    | @step x y z hxy hyz ih => ?_
  exact hP _ _
  exact hP _ _

/-! ## Cleaning up equations between pairs -/

/-! ### R6. `subst hp` (or `cases hp`) with `hp : e = x`, `x` a variable · context: `x` replaced by `e` -/
example {α β : Type} (r : α × β → α × β → Prop) (P : α × β → Prop) (a : α) (b : β) (x y : α × β)
    (hp : (a, b) = x) (hxy : r x y) (hP : ∀ z, P z) : P x := by
  subst hp
  exact hP _

/-! ### R7. `cases h` with `h : (a, b) = (a', b')`, `a' b'` variables · context: both components unified
`cases` splits the pair equation into `a = a'` and `b = b'` and substitutes both. -/
example {α β : Type} (P : α → β → Prop) (a a' : α) (b b' : β)
    (h : (a, b) = (a', b')) (hP : P a b) : P a' b' := by
  cases h
  exact hP

/-! ### R8. `obtain ⟨x, y⟩ := q` · context: a pair variable `q` replaced by `(x, y)` everywhere -/
example {α β : Type} (r : α × β → α × β → Prop) (P : α × β → Prop) (p q : α × β)
    (hpq : r p q) (hP : ∀ z, P z) : P q := by
  obtain ⟨x, y⟩ := q
  exact hP _

/-! ### R9. `ih rfl` · context/goal: discharge a premise `(a, b) = (x, y)` of `ih` with `rfl`
The implicit `a b` of `ih` are solved by unification with `x y`, so `rfl` proves the premise. -/
example {α β : Type} (P : α → β → Prop) (x : α) (y : β)
    (ih : ∀ {a : α} {b : β}, (a, b) = (x, y) → P a b) : P x y := by
  have h := ih rfl
  exact h

/-! ## Inversion: `cases` on a derivation whose index is a constructor -/

/-! ### R10. `cases h` with `h : Ev (.lit n) v` · context: `h` gone, `v` replaced by `n`
Only `Ev.lit` can produce an index `.lit n`, so one goal is left and its equations are substituted. -/
example (P : Nat → Prop) (n v : Nat) (h : Ev (.lit n) v) (hP : P n) : P v := by
  cases h
  exact hP

/-! ### R11. `cases h with | add ha hb => …` · context: the premises of the one fitting constructor -/
example (P : Nat → Prop) (a b : Tm) (v : Nat) (h : Ev (.add a b) v) (hP : ∀ k, P k) : P v := by
  cases h with
    | add ha hb => ?_
  exact hP _

/-! ### R12. `cases h with | pickL h => … | pickR h => …` · goal list: one goal per fitting constructor -/
example (P : Nat → Prop) (a b : Tm) (v : Nat) (h : Ev (.pick a b) v) (hP : ∀ k, P k) : P v := by
  cases h with
    | pickL h => ?_
    | pickR h => ?_
  exact hP _
  exact hP _

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Inversion twice, then compute: R11, R10, R10 -/
example (v : Nat) (h : Ev (.add (.lit 1) (.lit 2)) v) : v = 3 := by
  cases h with
    | add ha hb => ?_
  cases ha
  cases hb
  rfl

/-! ### W2. Induction on a step, then inversion of the big-step run: R2, R10, R11, R1
`generalizing v` because the value changes when the step happens inside `add`. -/
example {t t' : Tm} {v : Nat} (hs : Step t t') (he : Ev t' v) : Ev t v := by
  induction hs generalizing v with
    | addLit => ?_
    | addL _ ih => ?_
  · cases he
    exact .add .lit .lit
  · cases he with
    | add ha hb => exact .add (ih ha) hb

/-! ### W3. `Rtc` between pairs: R4 twice, R5 with R3, then R6/R7, R8, inversion, R9
The second component never changes along `Inc` steps. -/
example {n m n' m' : Nat} (h : Rtc Inc (n, m) (n', m')) : m' = m := by
  generalize hp : (n, m) = p at h
  generalize hq : (n', m') = q at h
  induction h generalizing n m with
    | refl x => ?_
    | @step x y z hxy _ ih => ?_
  · subst hp
    cases hq
    rfl
  · subst hp
    obtain ⟨k, l⟩ := y
    cases hxy
    exact ih rfl hq

end H023Guide
