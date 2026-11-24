/- E072 | fin_cases and vectors | 2 min | fin_cases, ![..], Fin, ZMod, simp_all, mathlib
GOAL
  Prove facts about every value of a finite type (`Fin n`, `ZMod n`) by splitting into one goal per value.

REFERENCE
  example : (![5, 7, 9] : Fin 3 → ℕ) 1 = 7 := rfl   -- `![a, b, c]` is the function 0 ↦ a, 1 ↦ b, 2 ↦ c
  example (i : Fin 2) : (i : ℕ) < 2 := by fin_cases i <;> simp   -- one goal per value of `i`
  example : (2 : ZMod 3) + 2 = 1 := rfl   -- `ZMod n` is ℤ modulo n; `rfl` computes in it
  `fin_cases i` replaces `i` by each element of its finite type; `<;> simp [f]` then unfolds `f` and
  computes in every goal. `simp_all` also simplifies hypotheses: a case where `h : f 0 = 7` reads
  `5 = 7` becomes `False`, which closes that case.
BANNED: decide
NOTE: `decide` could check all cases at once here; it is banned so you practise `fin_cases`, which still
  works when the values are real numbers and `decide` cannot compute (E074's matrices).
-/
import Mathlib

namespace E072

-- BEGIN SPEC
def f : Fin 3 → ℕ := ![5, 7, 9]
-- END SPEC

-- BEGIN SPEC
theorem f_ge (i : Fin 3) : f i ≥ 5 :=
-- END SPEC
  by fin_cases i <;> simp [f]

-- BEGIN SPEC
theorem f_eq_seven (i : Fin 3) (h : f i = 7) : i = 1 :=
-- END SPEC
  by fin_cases i <;> simp_all [f]

-- BEGIN SPEC
theorem sq_lt (i : Fin 4) : (i : ℕ) ^ 2 < 10 :=
-- END SPEC
  by fin_cases i <;> simp

-- BEGIN SPEC
theorem zmod3_prod (x : ZMod 3) : x * (x + 1) * (x + 2) = 0 :=
-- END SPEC
  by fin_cases x <;> rfl

end E072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each statement is about one variable that has only 3 or 4 possible values.
H2. Split with `fin_cases`, then finish every case with the same tactic via `<;>`. The case goals mention
    `f 0`, `f 1`, … so the finishing tactic must unfold `f`; in `f_eq_seven` it must also use `h`.
H3. `fin_cases i <;> simp [f]`; `fin_cases i <;> simp_all [f]`; `fin_cases i <;> simp`; `fin_cases x <;> rfl`.
-/
