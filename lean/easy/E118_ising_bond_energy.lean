/- E118 | Ising bond energy | 2-3 min | Bool, cases, spin variables, simp with definitions, mathlib
GOAL
  Encode an Ising spin as `Bool` (`true ↦ +1`, `false ↦ -1`). A bond with coupling `J` has energy
  `-J s_a s_b`: show it is `-J` when aligned and `+J` when anti-aligned, and that flipping both spins
  (`!a` is Boolean negation) leaves it unchanged.

REFERENCE
  example (P : Bool → Prop) (b : Bool) (h0 : P false) (h1 : P true) : P b := by cases b <;> assumption
  example : (!true) = false := rfl        -- `!b` is `not b`
  example : (if true then (1 : ℝ) else -1) = 1 := by simp
  `simp [bond, spin]` unfolds your definitions; after `cases a` the `if` has a literal condition and
  simp reduces it. `t1 <;> t2` runs `t2` on every goal `t1` produces.
-/
import Mathlib

namespace E118

-- BEGIN SPEC
/-- An Ising spin: `true` is spin up (`+1`), `false` is spin down (`-1`). -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Energy of one bond with coupling `J` between spins `a` and `b`. -/
def bond (J : ℝ) (a b : Bool) : ℝ := -J * (spin a * spin b)
-- END SPEC

-- BEGIN SPEC
theorem bond_values (J : ℝ) (a : Bool) : bond J a a = -J ∧ bond J a (!a) = J :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem bond_flip (J : ℝ) (a b : Bool) : bond J (!a) (!b) = bond J a b :=
-- END SPEC
  sorry

end E118

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `Bool` has only two values: split into cases and compute.
H2. `bond_values` needs one case split (on `a`), `bond_flip` two (on `a` and on `b`).
H3. `cases a <;> simp [bond, spin]`; `cases a <;> cases b <;> simp [bond, spin]`.
-/
