/- Guide for E003 (intro, exact, apply).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`A B C G : Prop` are arbitrary propositions (statements); a hypothesis `h : A → B` is a proof that
`A` implies `B`. A hypothesis `k` in an entry is only there to finish the example.
Part W: worked combinations on propositions and predicates that are NOT the exercise's.
Assumed: E001 (`theorem`/`example`, `rfl`, `decide`) and E002 (`def` on `Nat`).
-/

namespace E003Guide

/-! # Part R · Reference entries -/

/-! ## Moving assumptions into the context -/

/-! ### R1. `intro h` · goal `A → B` → goal `B`; context gains `h : A`
`by` switches to tactic mode; each tactic on its own line (or separated by `;`) changes the state. -/
example (A B : Prop) (k : A → B) : A → B := by
  intro h
  exact k h

/-! ### R2. `intro h1 h2 h3` · one name per `→`, left to right; context gains all three
`A → B → C → G` is `A → (B → (C → G))`: `→` nests to the right. -/
example (A B C G : Prop) (k : A → B → C → G) : A → B → C → G := by
  intro h1 h2 h3
  exact k h1 h2 h3

/-! ## Closing a goal -/

/-! ### R3. `exact h` · closes the goal when `h` states it exactly -/
example (A : Prop) (h : A) : A := by
  exact h

/-! ## Working backwards -/

/-! ### R4. `apply h` (`h : A → B`) · goal `B` → goal `A`
"To prove `B` it suffices to prove `A`": the goal must match the conclusion of `h`. -/
example (A B : Prop) (h : A → B) (k : A) : B := by
  apply h
  exact k

/-! ### R5. `apply h` (`h : A → B → C → G`) · goal list: `G` → three goals `A`, `B`, `C`, in that order
One new goal per premise of `h`, left to right. Prove them one after the other (here: three `exact`s). -/
example (A B C G : Prop) (h : A → B → C → G) (ka : A) (kb : B) (kc : C) : G := by
  apply h
  exact ka
  exact kb
  exact kc

/-! ## Proofs as functions -/

/-! ### R6. `exact h a b c` · closes `G` from `h : A → B → C → G` and `a : A`, `b : B`, `c : C`
A proof of `A → B → C → G` is a function: feed it proofs of `A`, `B`, `C` and it returns a proof of
`G`. Arguments are written with spaces, no parentheses: `h a b c`, not `h(a, b, c)`. They go in the
order of `h`'s premises, whatever order the hypotheses were introduced in. -/
example (A B C G : Prop) (h : A → B → C → G) (a : A) (b : B) (c : C) : G := by
  exact h a b c

/-! ### R7. `exact h 3` (`h : ∀ n, q n`) · closes `q 3`
`q : Nat → Prop` is a predicate: `q n` is a statement about the number `n`. A proof of `∀ n, q n`
is a function too: applied to `3` it proves `q 3`. -/
example (q : Nat → Prop) (h : ∀ n, q n) : q 3 := by
  exact h 3

/-! ### R8. `apply h` (`h : ∀ n, q n → q (n + 1)`) · goal `q 5` → goal `q 4`
`apply` finds `n` itself: it matches the conclusion `q (n + 1)` against `q 5` and picks `n := 4`
(`5` and `4 + 1` compute to the same `Nat`, as with `rfl` in E001). -/
example (q : Nat → Prop) (h : ∀ n, q n → q (n + 1)) (k : q 4) : q 5 := by
  apply h
  exact k

/-! # Part W · Worked combinations (not the exercise's propositions) -/

/-! ### W1. R2 then R4 then R3: introduce, work backwards, close -/
example (A B : Prop) : (A → B) → A → B := by
  intro hab ha
  apply hab
  exact ha

/-! ### W2. R5 with two premises, where the first new goal needs one more R4 -/
example (A B C G : Prop) (h : A → B → C) (f : G → A) (g : G) (kb : B) : C := by
  apply h
  apply f
  exact g
  exact kb

/-! ### W3. R8 twice, with a step of 2: walking a predicate down from `q 5` to `q 1` -/
example (q : Nat → Prop) (h : ∀ n, q n → q (n + 2)) (k : q 1) : q 5 := by
  apply h
  apply h
  exact k

/-! ### W4. The same as one term (R6, R7): `h n` is a proof of `q n → q (n + 2)` -/
example (q : Nat → Prop) (h : ∀ n, q n → q (n + 2)) (k : q 1) : q 5 := by
  exact h 3 (h 1 k)

end E003Guide
