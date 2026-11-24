/- M004 | Even as an inductive predicate | 10-15 min | inductive Prop, induction on derivations, cases inversion
GOAL
  `Ev n` holds when it can be derived from the two rules. Prove it agrees with `∃ k, n = 2 * k`
  and use inversion to refute and peel derivations.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M004

-- BEGIN SPEC
inductive Ev : Nat → Prop
  | zero : Ev 0
  | step (n : Nat) : Ev n → Ev (n + 2)
-- END SPEC

/- SKELETON · ev_four
  1. Apply the `step` rule backwards: `Ev 4` → `Ev 2` → `Ev 0`:             R2, R2
  2. Close with the premise-free rule:                                     R1
     (Or write the whole derivation as one term: `.step _ (…)`, W1.)
-/
-- BEGIN SPEC
theorem ev_four : Ev 4 :=
-- END SPEC
  .step _ (.step _ .zero)

/- SKELETON · ev_double
  1. Induct on the number `n`:                                              R3
  2. `zero`: `2 * 0` computes to `0`; close with the `zero` rule:           R1
  3. `succ n ih` (`ih : Ev (2 * n)`, goal `Ev (2 * (n + 1))`):
       reshape the index, `h : 2 * (n + 1) = 2 * n + 2`:                    R4 → R5
       apply `step`, whose premise is now `ih`:                             R2
-/
-- BEGIN SPEC
theorem ev_double (n : Nat) : Ev (2 * n) :=
-- END SPEC
  by
    induction n with
    | zero => exact .zero
    | succ n ih =>
      have h : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [h]
      exact .step _ ih

/- SKELETON · ev_exists
  1. Induct on the derivation `h`, not on `n`:                              R6
  2. `zero`: goal `∃ k, 0 = 2 * k`; witness `0`:                            R7
  3. `step m _ ih` (`ih : ∃ k, m = 2 * k`, goal `∃ k, m + 2 = 2 * k`):
       unpack `ih` into `k`, `hk : m = 2 * k`:                              R8
       witness `k + 1`, then the arithmetic from `hk`:                      R7 → R4
-/
-- BEGIN SPEC
theorem ev_exists (n : Nat) (h : Ev n) : ∃ k, n = 2 * k :=
-- END SPEC
  by
    induction h with
    | zero => exact ⟨0, rfl⟩
    | step m _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by omega⟩

/- SKELETON · not_ev_one
  1. `¬ Ev 1` is `Ev 1 → False`: introduce the derivation:                  R9
  2. Invert it: no rule concludes `Ev 1`, so no goal is left:               R10
-/
-- BEGIN SPEC
theorem not_ev_one : ¬ Ev 1 :=
-- END SPEC
  by
    intro h
    cases h

/- SKELETON · ev_minus_two
  1. Invert `h : Ev (n + 2)`: only `step` fits, and its premise is the
     derivation you need; name it and use it:                              R11
-/
-- BEGIN SPEC
theorem ev_minus_two (n : Nat) (h : Ev (n + 2)) : Ev n :=
-- END SPEC
  by
    cases h with
    | step _ h' => exact h'

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Rules are functions: `Ev.step n h : Ev (n + 2)` from `h : Ev n`. A hypothesis `h : Ev n` is a
    derivation: you can induct on it (one case per rule) or invert it with `cases` (which rules could
    have produced this index?).
H2. `ev_four`: two `step`s then `zero`. `ev_double`: `induction n`, and in `succ` rewrite
    `2 * (n + 1)` to `2 * n + 2` before applying `step`. `ev_exists`: `induction h`, witness `0`, then
    `k + 1`. `not_ev_one`: `intro h; cases h`. `ev_minus_two`: `cases h`.
H3. `ev_double`, case `succ n ih`: `have h : 2 * (n + 1) = 2 * n + 2 := by omega`, `rw [h]`, then
    `.step _ ih`. `ev_exists`, case `step m _ ih`: `obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, by omega⟩`.
    `ev_minus_two`: `cases h with | step _ h' => …`.
-/
