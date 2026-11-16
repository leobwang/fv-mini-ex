/- E077 | Tactic macros | 2-3 min | macro, syntax, macro_rules, tactic quotation, first
GOAL
  Define your own tactic `crush` (edit the stub macro, which expands to `sorry`) so that the three
  frozen `by crush` proofs go through.

REFERENCE
  macro "triv" : tactic => `(tactic| first | rfl | decide)   -- a new tactic that names a tactic script
  example : 2 + 2 = 4 := by triv
  syntax "triv2" : tactic                            -- or: declare the syntax first …
  macro_rules | `(tactic| triv2) => `(tactic| rfl)   -- … then give it one or more expansions;
  macro_rules | `(tactic| triv2) => `(tactic| omega) -- if one expansion fails, Lean tries another
  `first | t1 | t2 | t3` runs the first of the tactics that does not fail. `(tactic| …)` quotes tactic syntax.
  Names inside a quotation are hygienic: `hp` written in the macro is not the goal's `hp`, so refer
  to hypotheses through tactics that search for them (`assumption`, `simp_all`).
BANNED: grind, trivial, solve_by_elim, exact?, apply?, try?
NOTE: the theorems, including `by crush`, are frozen; only the macro line is yours to change.
NOTE: the bans remove one-word tactics that close all three goals alone; the point is to combine tactics.
-/

namespace E077

-- Your macro (edit this line):
macro "crush" : tactic => `(tactic| first | rfl | omega | simp_all)

-- BEGIN SPEC
theorem t1 (n : Nat) : n + 0 = n := by crush
theorem t2 (a b : Nat) (h : a < b) : a + 1 ≤ b := by crush
theorem t3 (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by crush
-- END SPEC

end E077

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A macro is a name for a tactic script you could have typed after `by` yourself.
H2. Each goal falls to a tactic you know (`rfl`, `omega`, and one that uses hypotheses such as
    `simp_all` or `constructor <;> assumption`). One tactic must cover all three: combine them with `first`.
H3. macro "crush" : tactic => `(tactic| first | rfl | omega | ...)   with a third alternative for `t3`.
-/
