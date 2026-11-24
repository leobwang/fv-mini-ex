/- Guide for M003 (Postage stamps).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of your goal" as a function of the number; `G` is an arbitrary goal. A
hypothesis `h`/`step`/`k` in an entry is only there to finish the example; it shows what the goal became.
The entries write `induction … with | _ n ih => ?_` so that the new goal shows up in the infoview;
in the exercise you may put the tactics right after `=>` instead.
Part W: a worked combination on "every `n` is even or odd" (steps back by 2), not on the exercise's
stamps.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M003Guide

/-! # Part R · Reference entries -/

/-! ## Strong induction -/

/-! ### R1. `induction n using Nat.strongRecOn with | _ n ih => ?_` · context gains
`ih : ∀ (m : Nat), m < n → P m`; goal unchanged
`Nat.strongRecOn` is core Lean's strong (course-of-values) induction principle: to prove `P n` you
may assume `P m` for EVERY `m < n`, not only for `n - 1`. There is one case, named `ind`; `_` matches
it without naming it. -/
example (P : Nat → Prop) (step : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  exact step n ih

/-! ### R2. The same, with a hypothesis `h : c ≤ n` in the context · `ih` gains the premise `c ≤ m`
`induction` first reverts every hypothesis that mentions `n`, so the statement proved by induction
is `c ≤ n → Q n`. Afterwards `h` is back in the context, and `ih` asks for THREE things:
`m`, a proof of `m < n`, and a proof of `c ≤ m`. -/
example (c : Nat) (Q : Nat → Prop) (n : Nat) (h : c ≤ n)
    (step : ∀ n, (∀ m, m < n → c ≤ m → Q m) → c ≤ n → Q n) : Q n := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  exact step n ih h

/-! ## Peeling off base cases -/

/-! ### R3. `by_cases h4 : n = 4` · goal list: one goal → two; context gains `h4 : n = 4` in
the first (`case pos`) and `h4 : ¬n = 4` in the second (`case neg`)
`· tac` then proves the first goal; the lines after it work on the second one. -/
example (n : Nat) (G : Prop) (h1 : n = 4 → G) (h2 : ¬n = 4 → G) : G := by
  by_cases h4 : n = 4
  · exact h1 h4
  exact h2 h4

/-! ## Giving the witnesses -/

/-! ### R4. `refine ⟨x, y, ?_⟩` · goal `∃ a b, R a b` → `R x y`
`⟨x, y, p⟩` is the anonymous constructor for the nested `∃ a, ∃ b, R a b`. `exact ⟨x, y, by omega⟩`
does R4 and R5 in one line. -/
example (n : Nat) (h : n = 7) : ∃ a b : Nat, n = 2 * a + 3 * b := by
  refine ⟨2, 1, ?_⟩
  omega

/-! ### R5. `omega` · closes linear arithmetic over `Nat`, using the hypotheses in the context
It reads equations `n = 7`, negations `¬n = 4`, bounds `4 ≤ n`, and truncated subtraction `n - 2`
(`n - 2 = 0` when `n < 2`), and splits cases on them by itself. -/
example (n : Nat) (h : 4 ≤ n) (h4 : ¬n = 4) (h5 : ¬n = 5) : 4 ≤ n - 2 := by
  omega

/-! ## Using the induction hypothesis -/

/-! ### R6. `have hm := ih m hlt hle` · context gains `hm : Q m`
`ih : ∀ (m : Nat), m < n → 4 ≤ m → Q m` is a function: apply it to the number and to the two
proofs. In the exercise the proofs are written in place as `(by omega)`. -/
example (n : Nat) (Q : Nat → Prop) (ih : ∀ m, m < n → 4 ≤ m → Q m) (hlt : n - 2 < n)
    (hle : 4 ≤ n - 2) (k : Q (n - 2) → Q n) : Q n := by
  have hm := ih (n - 2) hlt hle
  exact k hm

/-! ### R7. `obtain ⟨a, b, hab⟩ := e` · context: `e : ∃ a b, Q a b` → `a b : Nat`, `hab : Q a b`
`obtain ⟨…⟩ := ih m p q` does R6 and R7 in one line, without keeping `hm`. -/
example (Q : Nat → Nat → Prop) (G : Prop) (e : ∃ a b, Q a b) (k : ∀ a b, Q a b → G) : G := by
  obtain ⟨a, b, hab⟩ := e
  exact k a b hab

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Every `n` is even or odd, by strong induction stepping back by 2: R1, two base cases
with R3 → R4 → R5, then R6 + R7 in one `obtain` and R4 → R5. There is no hypothesis on `n`, so `ih`
takes two arguments only (compare R2). -/
example (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  by_cases h0 : n = 0
  · exact ⟨0, by omega⟩
  by_cases h1 : n = 1
  · exact ⟨0, by omega⟩
  obtain ⟨k, hk⟩ := ih (n - 2) (by omega)
  exact ⟨k + 1, by omega⟩

end M003Guide
