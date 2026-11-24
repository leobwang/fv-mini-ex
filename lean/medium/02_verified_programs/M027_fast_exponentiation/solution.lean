/- M027 | Fast exponentiation | 15 min | fun_induction, Nat.pow lemmas, let [R11]
GOAL
  `powFast` computes `b ^ e` with O(log e) multiplications by repeated squaring. Prove it correct.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M027

-- BEGIN SPEC
def powFast (b e : Nat) : Nat :=
  if e = 0 then 1
  else
    let r := powFast (b * b) (e / 2)
    if e % 2 = 0 then r else b * r
termination_by e
-- END SPEC

/- SKELETON · powFast_eq
  1. One goal per branch of `powFast` (e = 0, even, odd), naming everything:        R1
       `fun_induction powFast b e with`
       `| case1 b => …`, `| case2 b e he r h2 ih => …`, `| case3 b e he r h2 ih => …`
     `ih` is the theorem at the recursive call's arguments `(b * b, e / 2)`.
  2. case1 (`⊢ 1 = b ^ 0`): close it                                               R2 (`simp`)
  3. case2 (even, `⊢ r = b ^ e`):
       unfold the local definition `r`, so the IH can rewrite                      R3
       use the IH                                                                  rw [ih]
       `(b * b) ^ (e / 2)` → `b ^ (2 * (e / 2))`                                    R4 → R5
       compare exponents, then `2 * (e / 2) = e` from `h2`                         R6, R7
  4. case3 (odd, `⊢ b * r = b ^ e`): as case2, and absorb the lone factor `b`
     into the power before comparing exponents:                  R3, rw [ih], R4 → R5 → R8, R6, R7
-/
-- BEGIN SPEC
theorem powFast_eq (b e : Nat) : powFast b e = b ^ e :=
-- END SPEC
  by
    fun_induction powFast b e with
    | case1 b => simp
    | case2 b e he r h2 ih =>
      show powFast (b * b) (e / 2) = b ^ e
      rw [ih, ← Nat.pow_two, ← Nat.pow_mul]
      congr 1
      omega
    | case3 b e he r h2 ih =>
      show b * powFast (b * b) (e / 2) = b ^ e
      rw [ih, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
      congr 1
      omega

end M027

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Follow the three branches of `powFast` (`e = 0`, even, odd) with `fun_induction powFast b e`; the IH
    is the theorem at `(b * b, e / 2)`. The `let r` shows up as a local definition `r : Nat := …`.
H2. In each recursive case: `show` the goal with `r` unfolded, `rw [ih]`, turn `(b * b) ^ (e / 2)` into
    `b ^ (2 * (e / 2))` with `← Nat.pow_two, ← Nat.pow_mul` (odd case: then `← Nat.pow_succ'`), and
    reduce to an equation of exponents with `congr 1`, which `omega` closes using `h2`.
H3. Even case: `show powFast (b * b) (e / 2) = b ^ e; rw [ih, ← Nat.pow_two, ← Nat.pow_mul]; congr 1; omega`.
    Odd case: `show b * powFast (b * b) (e / 2) = b ^ e`, and add `← Nat.pow_succ'` to the `rw`.
-/
