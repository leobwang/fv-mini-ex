/- E033 | Library search | 2-3 min | exact?, apply?, library names
GOAL
  Find the library lemma for each goal with `exact?`, then paste the name it suggests.
BANNED: simp, simp_all, omega, grind, decide

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · len_rev
  1. Put `by exact?` in the hole and read the `Try this` line:              R1
  2. Replace the hole by the lemma it names; all its arguments are
     implicit, so the bare name is the proof:                              R4
-/
-- BEGIN SPEC
theorem len_rev (xs : List Nat) : xs.reverse.length = xs.length :=
-- END SPEC
  List.length_reverse

/- SKELETON · dvd_le
  1. Put `by exact?` in the hole, or guess the name from the shape
     "`≤` from `∣`" and confirm it with `#check`:                            R1 or R2
  2. Replace the hole by the lemma applied to the two hypotheses, in the
     lemma's order (positivity first):                                     R5
-/
-- BEGIN SPEC
theorem dvd_le (a b : Nat) (h : a ∣ b) (hb : 0 < b) : a ≤ b :=
-- END SPEC
  Nat.le_of_dvd hb h

/- SKELETON · rev_app
  1. Guess the name from the shape "reverse of an append" (or `exact?`):   R2 or R1
  2. Replace the hole by the bare name (all arguments implicit):           R6
-/
-- BEGIN SPEC
theorem rev_app (xs ys : List Nat) : (xs ++ ys).reverse = ys.reverse ++ xs.reverse :=
-- END SPEC
  List.reverse_append

/- SKELETON · mod_lt_of_pos
  1. `#check` the lemma "`%` is `<`" to see which arguments are explicit
     (or `exact?`):                                                         R2 or R1
  2. Replace the hole by the lemma applied to the number and to `hb`:      R7
-/
-- BEGIN SPEC
theorem mod_lt_of_pos (a b : Nat) (hb : 0 < b) : a % b < b :=
-- END SPEC
  Nat.mod_lt a hb

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Put `by exact?` in each hole and wait a moment; paste the `Try this` line it prints (R1).
H2. Without `exact?`: guess each name from the statement's shape, outermost function first
    ("length of a reverse", "`≤` from `∣`", "reverse of an append", "`%` is `<`"), and `#check`
    it for the argument order (R2). Two of the four lemmas take explicit arguments (R5, R7).
H3. `List.length_reverse`, `Nat.le_of_dvd hb h`, `List.reverse_append`, `Nat.mod_lt a hb`.
-/
