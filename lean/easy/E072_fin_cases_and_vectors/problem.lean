/- E072 | fin_cases and vectors | 2 min | fin_cases, ![..], Fin, ZMod, simp_all, mathlib
GOAL
  Prove facts about every value of a finite type (`Fin n`, `ZMod n`) by splitting into one goal per value.
BANNED: decide

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E072

-- BEGIN SPEC
def f : Fin 3 → ℕ := ![5, 7, 9]
-- END SPEC

/- SKELETON · f_ge
  1. One goal per value of `i` (three goals; use `<;>`):                                  R2
  2. Each goal, in one `simp` with the name `f`:                                          R3
     it rewrites the printed index, reads the entry of `![…]`, compares the numerals:     R4 → R5 → R6
-/
-- BEGIN SPEC
theorem f_ge (i : Fin 3) : f i ≥ 5 :=
-- END SPEC
  sorry

/- SKELETON · f_eq_seven
  1. One goal per value of `i`; `h` is split along with the goal:                         R2
  2. Each goal: simplify `h` and the goal together, with the name `f`.
     Cases 0 and 2: `h` becomes `False` (`5 = 7`, `9 = 7`) and closes the goal (R7);
     case 1: `h` becomes `True` and the goal `(fun i => i) ⟨1, ⋯⟩ = 1` becomes `1 = 1` (R4):  R8 (R3–R5, R7 inside)
-/
-- BEGIN SPEC
theorem f_eq_seven (i : Fin 3) (h : f i = 7) : i = 1 :=
-- END SPEC
  sorry

/- SKELETON · sq_lt
  1. One goal per value of `i` (four goals):                                              R2
  2. Each goal, in one `simp`: the cast `↑((fun i => i) ⟨k, ⋯⟩)` becomes `k`, then the numerals: R9 → R6
-/
-- BEGIN SPEC
theorem sq_lt (i : Fin 4) : (i : ℕ) ^ 2 < 10 :=
-- END SPEC
  sorry

/- SKELETON · zmod3_prod
  1. One goal per residue of `x : ZMod 3` (three goals):                                  R10
  2. Each goal is closed arithmetic mod 3: compute both sides (not `simp`, see Traps):     R11
-/
-- BEGIN SPEC
theorem zmod3_prod (x : ZMod 3) : x * (x + 1) * (x + 2) = 0 :=
-- END SPEC
  sorry

end E072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each statement is about one variable with only 3 or 4 possible values: check them all, one goal per value.
H2. Split with `fin_cases` (R2, R10) and finish every case with the same tactic via `<;>`. The case goals
    mention `f ((fun i => i) ⟨0, ⋯⟩)` …, so the finisher must unfold `f` (`simp [f]`); in `f_eq_seven` it must
    also simplify `h` (`simp_all`); in `ZMod 3` `simp` cannot compute, `rfl` can.
H3. `fin_cases i <;> simp [f]`; `fin_cases i <;> simp_all [f]`; `fin_cases i <;> simp`; `fin_cases x <;> rfl`.
-/
