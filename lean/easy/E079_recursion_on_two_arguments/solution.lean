/- E079 | Recursion on two arguments | 3 min | pattern matching on two args, lexicographic termination, Ackermann
GOAL
  `ack` is the Ackermann function. Lean accepted it with no `termination_by`: it found the
  lexicographic order on `(m, n)` by itself. Prove `ack 2 3 = 9` and closed forms for `ack 1 n`, `ack 2 n`.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E079

-- BEGIN SPEC
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
-- END SPEC

/- SKELETON · ack_small
  1. A closed computation (no variables): rewrite with the equations of `ack`
     until only numerals are left; `rfl` and `decide` cannot do it:         R1
-/
-- BEGIN SPEC
theorem ack_small : ack 2 3 = 9 :=
-- END SPEC
  by simp [ack]

/- SKELETON · ack_one
  1. Induction on `n`:                                                      R3
  2. Case `zero`: `ack 1 0 = 0 + 2` is a closed computation:                R1
  3. Case `succ k ih`, goal `ack 1 (k + 1) = k + 1 + 2`:
       unfold once (equation 3) → `ack 0 (ack 1 k)`                         R2
       rewrite `ack 1 k` with `ih` → `ack 0 (k + 2)`                         rw [ih]
       unfold `ack 0` (equation 1) → `k + 2 + 1 = k + 1 + 2`; `rw`         R2
       closes it by itself (it tries `rfl` after rewriting)
     (one `simp` with `ack` and `ih` does step 3)                            R4
-/
-- BEGIN SPEC
theorem ack_one (n : Nat) : ack 1 n = n + 2 :=
-- END SPEC
  by
  induction n with
  | zero => simp [ack]
  | succ k ih => simp [ack, ih]

/- SKELETON · ack_two
  1. Induction on `n`:                                                      R3
  2. Case `zero`: `ack 2 0` is a closed computation:                        R1
  3. Case `succ k ih`: unfold once → `ack 1 (ack 2 k)`, then `ih`:          R2, rw [ih]
       now `ack 1 (2 * k + 3)`: replace it with the closed form proved
       above, the theorem `ack_one` at `2 * k + 3`:                          R5
     (one `simp` with `ack`, `ih` and `ack_one` does step 3)                 R4, R5
  4. What is left is linear arithmetic over `Nat`:                          R6
-/
-- BEGIN SPEC
theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 :=
-- END SPEC
  by
  induction n with
  | zero => simp [ack]
  | succ k ih => simp [ack, ih, ack_one]; omega

end E079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ack_small` has no variables: evaluate it with the equations of `ack` (`rfl` fails on well-founded
    recursion). The other two hold for every `n`, so they need induction on `n`.
H2. In the step, unfold once and use `ih`: `ack 1 (k + 1) = ack 0 (ack 1 k)` and
    `ack 2 (k + 1) = ack 1 (ack 2 k)`. The second leaves `ack 1 (2 * k + 3)`, which only `ack_one` removes.
H3. `induction n with | zero => simp [ack] | succ k ih => simp [ack, ih]`; for `ack_two` the step is
    `simp [ack, ih, ack_one]` followed by `omega`.
-/
