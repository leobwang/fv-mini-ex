/- M25 | Fast exponentiation | 15 min | fun_induction, Nat.pow lemmas, let [R11]
GOAL
  `powFast` computes `b ^ e` with O(log e) multiplications by repeated squaring. Prove it correct.

REFERENCE
  #check Nat.pow_two    -- a ^ 2 = a * a
  #check Nat.pow_mul    -- a ^ (m * n) = (a ^ m) ^ n
  #check Nat.pow_succ'  -- b ^ (n + 1) = b * b ^ n
  example (e : Nat) (h : e % 2 = 1) : 2 * (e / 2) + 1 = e := by omega
  -- In `fun_induction` cases, `let r := ...` shows up as a local definition `r : Nat := ...`;
  -- `show <goal with r unfolded>` replaces it by its value. `congr 1` reduces `b ^ x = b ^ y` to `x = y`.
-/

namespace M25

-- BEGIN SPEC
def powFast (b e : Nat) : Nat :=
  if e = 0 then 1
  else
    let r := powFast (b * b) (e / 2)
    if e % 2 = 0 then r else b * r
termination_by e
-- END SPEC

-- BEGIN SPEC
theorem powFast_eq (b e : Nat) : powFast b e = b ^ e :=
-- END SPEC
  sorry

end M25

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three branches: `e = 0`, even `e`, odd `e`. Use `fun_induction powFast b e` to get the IH for `(b * b, e / 2)`.
H2. `(b * b) ^ (e / 2) = b ^ (2 * (e / 2))`, and `2 * (e / 2)` is `e` (even) or `e - 1` (odd).
H3. Even case: `show powFast (b * b) (e / 2) = b ^ e; rw [ih, ← Nat.pow_two, ← Nat.pow_mul]; congr 1; omega`. Odd case adds `← Nat.pow_succ'`.
-/
