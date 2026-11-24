/- E077 | Tactic macros | 2-3 min | macro, syntax, macro_rules, tactic quotation, first
GOAL
  Define your own tactic `crush` (edit the stub macro, which expands to `sorry`) so that the three
  frozen `by crush` proofs go through.

BANNED: grind, trivial, solve_by_elim, exact?, apply?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E077

/- SKELETON · crush (the macro below; t1, t2, t3 check it)
  The theorems are frozen, `by crush` included: only the macro line changes.
  1. Find one closer per goal (each either closes its goal or fails):
       t1  `n + 0 = n`   computes to `n = n`                                  R1
       t2  `a + 1 ≤ b`   linear, uses `h : a < b`                             R2
       t3  `P ∧ Q`       from `hp`, `hq`; no names inside a macro            R3, R7
  2. Combine the three closers into one tactic, in an order where each
     earlier one fails on the goals it does not solve:                      R4
  3. Put that tactic in the quotation, replacing `sorry`:                   R5
     (the two-step form, one `macro_rules` per closer, also works:          R6)
-/
-- Your macro (edit this line):
macro "crush" : tactic => `(tactic| sorry)

-- BEGIN SPEC
theorem t1 (n : Nat) : n + 0 = n := by crush
theorem t2 (a b : Nat) (h : a < b) : a + 1 ≤ b := by crush
theorem t3 (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by crush
-- END SPEC

end E077

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A macro is a name for a tactic script you could have typed after `by` yourself: find, for each of
    `t1`, `t2`, `t3`, a single tactic that closes it, then make one tactic out of the three.
H2. `t1` computes (`rfl`), `t2` is linear arithmetic (`omega`), `t3` needs the hypotheses but cannot name
    them (hygiene): `simp_all` or `constructor <;> assumption`. Join them with `first | … | … | …`.
H3. macro "crush" : tactic => `(tactic| first | rfl | omega | ...)   with a third alternative for `t3`.
-/
