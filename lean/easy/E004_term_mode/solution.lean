/- E004 | Term-mode proofs | 2-3 min | fun, anonymous constructor, term mode
GOAL
  Prove the statements as terms (no `by`): proofs are functions and pairs.

BANNED: by

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · and_swap
  1. Bind the premise, taking the pair apart at the binder (one name per
     component):                                                           R3
  2. Build the result pair, the two components in the new order:           R2
-/
-- BEGIN SPEC
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
-- END SPEC
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

/- SKELETON · curry_and
  1. Bind the three premises: the function, then the two proofs:           R4
  2. Only the function produces `R`: apply it to its one argument:         R5
  3. That argument is a pair built from the two proofs:                    R2
-/
-- BEGIN SPEC
theorem curry_and (P Q R : Prop) : (P ∧ Q → R) → P → Q → R :=
-- END SPEC
  fun h hp hq => h ⟨hp, hq⟩

/- SKELETON · uncurry_and
  1. Bind the two premises, keeping the pair whole under one name:          R4
  2. Apply the function to its two arguments, in its premise order:         R5
  3. Those arguments are the pair's components:                            R6, R6
     (or split the pair at the binder instead:                             R3 → R5)
-/
-- BEGIN SPEC
theorem uncurry_and (P Q R : Prop) : (P → Q → R) → P ∧ Q → R :=
-- END SPEC
  fun h hpq => h hpq.1 hpq.2

/- SKELETON · and_imp_iff
  1. Bind the proof of `P`:                                                 R1
  2. Build the pair `R ∧ Q`:                                                R2
  3. First component `R`: `hr` applied to a proof of `Q`; that argument is
     itself an application, so parenthesize it:                            R5, R8
  4. The proof of `Q` (inside step 3, and again as the second component):
     the `↔` read left to right, applied to the proof of `P`:              R7
-/
-- BEGIN SPEC
theorem and_imp_iff (P Q R : Prop) (h : P ↔ Q) (hr : Q → R) : P → R ∧ Q :=
-- END SPEC
  fun hp => ⟨hr (h.1 hp), h.1 hp⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read each `→` as "takes an argument" and each `∧` as "a pair". To see what a spot expects,
    write `_` there and read the error (then remove the `_`).
H2. Start every term with `fun ... =>` binding all the premises (R1, R4; R3 splits a pair at the
    binder), then assemble the result: a pair `⟨_, _⟩` (R2) or a hypothesis applied to arguments (R5).
    `curry_and`: the first premise wants ONE argument, a pair. `uncurry_and`: it wants two, the
    pair's components (R6). `and_imp_iff`: `h.1` turns a proof of `P` into one of `Q` (R7).
H3. `and_swap`: `fun ⟨hp, hq⟩ => ⟨hq, hp⟩`; `uncurry_and`: `fun h hpq => h hpq.1 hpq.2`.
    `and_imp_iff`: after `fun hp =>`, the proof of `Q` is `h.1 hp`, and it is used twice.
-/
