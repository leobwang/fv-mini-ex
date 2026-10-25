/- E33 | Library search | 2-3 min | exact?, apply?, library names
GOAL
  Find the library lemma for each goal with `exact?`, then paste the name it suggests.

REFERENCE
  example (n : Nat) (h : n ≠ 0) : 0 < n := by exact?
    -- prints "Try this: exact Nat.zero_lt_of_ne_zero h"; replace `exact?` by that line
  `apply?` also suggests lemmas that leave side goals; `#check Nat.le_of_dvd` shows a statement.
  Library names follow the statement: `List.length_reverse`, `Nat.le_of_dvd`, `List.reverse_append`.
BANNED: simp, simp_all, omega, grind, decide
-/

-- BEGIN SPEC
theorem len_rev (xs : List Nat) : xs.reverse.length = xs.length :=
-- END SPEC
  List.length_reverse

-- BEGIN SPEC
theorem dvd_le (a b : Nat) (h : a ∣ b) (hb : 0 < b) : a ≤ b :=
-- END SPEC
  Nat.le_of_dvd hb h

-- BEGIN SPEC
theorem rev_app (xs ys : List Nat) : (xs ++ ys).reverse = ys.reverse ++ xs.reverse :=
-- END SPEC
  List.reverse_append

-- BEGIN SPEC
theorem mod_lt_of_pos (a b : Nat) (hb : 0 < b) : a % b < b :=
-- END SPEC
  Nat.mod_lt a hb

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Put `by exact?` in each hole and wait a moment.
H2. If `exact?` is slow, guess the name from the statement: `List.length_reverse` style.
H3. `List.length_reverse`, `Nat.le_of_dvd hb h`, `List.reverse_append`, `Nat.mod_lt a hb`.
-/
