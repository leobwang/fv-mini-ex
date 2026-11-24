/- E118 | Ising bond energy | 2-3 min | Bool, cases, spin variables, simp with definitions, mathlib
GOAL
  Encode an Ising spin as `Bool` (`true ↦ +1`, `false ↦ -1`). A bond with coupling `J` has energy
  `-J s_a s_b`: show it is `-J` when aligned and `+J` when anti-aligned, and that flipping both spins
  (`!a` is Boolean negation) leaves it unchanged.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E118

-- BEGIN SPEC
/-- An Ising spin: `true` is spin up (`+1`), `false` is spin down (`-1`). -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Energy of one bond with coupling `J` between spins `a` and `b`. -/
def bond (J : ℝ) (a b : Bool) : ℝ := -J * (spin a * spin b)
-- END SPEC

/- SKELETON · bond_values
  1. `a` is a variable, so `spin a` cannot be evaluated: split it into
     `a = false` and `a = true`.                                                R1
  2. In both goals (join with `<;>`), one `simp` naming both definitions.
     It unfolds them, evaluates `!a` and the `if`s, multiplies the `±1`s,
     and closes both sides of the `∧`:                                         R3 → R4, R5 → R6 → R7, R8, R9 → R10
-/
-- BEGIN SPEC
theorem bond_values (J : ℝ) (a : Bool) : bond J a a = -J ∧ bond J a (!a) = J :=
-- END SPEC
  by cases a <;> simp [bond, spin]

/- SKELETON · bond_flip
  1. Two spin variables: split both, four goals.                                 R2
  2. In all four goals, the same `simp` as in `bond_values`:                     R3 → R4, R5 → R6 → R7, R8, R9
-/
-- BEGIN SPEC
theorem bond_flip (J : ℝ) (a b : Bool) : bond J (!a) (!b) = bond J a b :=
-- END SPEC
  by cases a <;> cases b <;> simp [bond, spin]

end E118

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `spin a` with a variable `a` is stuck at an `if`. A `Bool` has only two values: split into cases,
    then every `if` has a literal condition and the goal is arithmetic with `±1`.
H2. `bond_values`: one case split on `a` (R1), `bond_flip`: two, on `a` and `b` (R2). Then one `simp`
    that unfolds `bond` and `spin` (R3) does the rest in every goal: R4–R9, plus R10 for the `∧`.
H3. `cases a <;> simp [bond, spin]` for `bond_values`; `bond_flip` is the same with `b` split too.
-/
