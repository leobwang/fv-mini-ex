/- E003 | intro, exact, apply | 2-3 min | intro, exact, apply
GOAL
  Prove four implications with the three basic tactics.
BANNED: simp, simp_all, grind

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · imp_trans
  1. Move the three premises into the context, one name each:                    R2
  2. Goal `R`: work backwards through the hypothesis that concludes `R`:         R4
  3. Goal `Q`: once more, through the hypothesis that concludes `Q`:              R4
  4. Goal `P` is now a hypothesis:                                                R3
-/
-- BEGIN SPEC
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R :=
-- END SPEC
  by
    intro hpq hqr hp
    apply hqr
    apply hpq
    exact hp

/- SKELETON · two_premises
  1. Nothing to introduce (the goal `R` has no `→`). `R` is the conclusion of `h`:
     apply it; one goal per premise, `P` then `Q`:                                R5
  2. Close each goal with its hypothesis, in that order:                          R3, R3
     (or the whole proof in one step: feed `h` both proofs                        R6)
-/
-- BEGIN SPEC
theorem two_premises (P Q R : Prop) (h : P → Q → R) (hp : P) (hq : Q) : R :=
-- END SPEC
  by
    apply h
    exact hp
    exact hq

/- SKELETON · swap_args
  1. Move the three premises into the context (note: `Q` comes before `P`):      R2
  2. Goal `R`: feed the first hypothesis its two proofs, in ITS order `P`, `Q`:  R6
     (or: R5 → R3, R3)
-/
-- BEGIN SPEC
theorem swap_args (P Q R : Prop) : (P → Q → R) → (Q → P → R) :=
-- END SPEC
  by
    intro h hq hp
    exact h hp hq

/- SKELETON · step_twice
  1. Goal `p 2`: work backwards through `step` (Lean picks `n := 1`):            R8
  2. Goal `p 1`: again (`n := 0`):                                                R8
  3. Goal `p 0` is a hypothesis:                                                  R3
     (or the whole proof as one term: `step` applied to a number and a proof     R7, R6)
-/
-- BEGIN SPEC
theorem step_twice (p : Nat → Prop) (step : ∀ n, p n → p (n + 1)) (h0 : p 0) : p 2 :=
-- END SPEC
  by
    apply step
    apply step
    exact h0

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read the goal. Each `→` in front of it is a premise you can `intro` (R1, R2). A goal that is the
    conclusion of a hypothesis can be `apply`d (R4, R5, R8). A goal that is a hypothesis: `exact` (R3).
H2. `imp_trans`, `swap_args`: `intro` every premise first, then look at the goal `R`. `two_premises`,
    `step_twice`: no `intro`; work backwards with `apply` until each goal is a hypothesis. A hypothesis
    `h : P → Q → R` is also a function: `h hp hq` proves `R` (R6).
H3. `imp_trans`: after `intro hpq hqr hp` the goal is `R`, and `apply hqr` makes it `Q`.
    `swap_args`: after `intro h hq hp`, the key line is `exact h hp hq` (arguments in `h`'s order).
    `step_twice`: `apply step` turns `p 2` into `p 1`, and again into `p 0`.
-/
