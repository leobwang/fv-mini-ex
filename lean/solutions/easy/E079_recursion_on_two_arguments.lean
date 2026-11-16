/- E079 | Recursion on two arguments | 3 min | pattern matching on two args, lexicographic termination, Ackermann
GOAL
  `ack` is the Ackermann function. Lean accepted it with no `termination_by`: it found the
  lexicographic order on `(m, n)` by itself. Prove `ack 2 3 = 9` and closed forms for `ack 1 n`, `ack 2 n`.

REFERENCE
  def t : Nat → Nat → Nat | 0, _ => 0 | m + 1, 0 => t m 9 | m + 1, n + 1 => t (m + 1) n + 1 termination_by m n => (m, n)
    -- match two arguments at once; the measure `(m, n)` is compared lexicographically:
    -- each call lowers `m`, or keeps `m` and lowers `n`. Lean guessed this measure for `ack`.
  #check @ack.eq_3     -- ack (m+1) (n+1) = ack m (ack (m+1) n), one equation lemma per pattern
  example (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]   -- unfold one step
  example : ack 1 1 = 3 := by simp [ack]   -- `simp [ack]` rewrites with all equations, also on literals
  `induction n with | zero => … | succ k ih => …`, then `simp [ack, ih]` in the step.
NOTE: `ack` uses well-founded recursion, so `rfl` and `decide` cannot evaluate it; use `simp [ack]`.
-/

namespace E079

-- BEGIN SPEC
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
-- END SPEC

-- BEGIN SPEC
theorem ack_small : ack 2 3 = 9 :=
-- END SPEC
  by simp [ack]

-- BEGIN SPEC
theorem ack_one (n : Nat) : ack 1 n = n + 2 :=
-- END SPEC
  by
  induction n with
  | zero => simp [ack]
  | succ k ih => simp [ack, ih]

-- BEGIN SPEC
theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 :=
-- END SPEC
  by
  induction n with
  | zero => simp [ack]
  | succ k ih => simp [ack, ih, ack_one]; omega

end E079

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ack_small` is a closed computation; the other two are statements for every `n`, so induct on `n`.
H2. In the step, `ack 1 (k + 1) = ack 0 (ack 1 k)`: unfold once, then use the induction hypothesis.
    `ack_two` needs `ack_one` as well, since `ack 2 (k + 1) = ack 1 (ack 2 k)`.
H3. `induction n with | zero => simp [ack] | succ k ih => simp [ack, ih]`; for `ack_two` add `ack_one`
    to the simp set and finish with `omega`.
-/
