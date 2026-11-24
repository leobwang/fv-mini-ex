/- E086 | Strings and chars | 2-3 min | String, Char, toList, List.countP, decide on literals
GOAL
  Write `countDigits s` (how many characters of `s` are digits `0`–`9`), check literal facts with
  `decide`, and prove: on a one-character string (`String.singleton c`) the count is 1 if `c` is a
  digit and 0 otherwise, it adds up over `++`, and it never exceeds `s.length`.

BANNED: grind, exact?, try?

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E086

/- SKELETON · countDigits
  A one-line term, no tactics:
  1. Turn `s` into its characters, a `List Char`:                       R2
  2. Count the characters that pass the `Bool` test `Char.isDigit`:     R3
-/
-- BEGIN SPEC
def countDigits (s : String) : Nat :=
-- END SPEC
  sorry

/- SKELETON · lit_facts
  1. All three conjuncts are computations on literals: close the whole
     goal at once, no splitting:                                        R1
-/
-- BEGIN SPEC
theorem lit_facts : "hello".length = 5 ∧ 'a'.toNat = 97 ∧ '7'.isDigit = true :=
-- END SPEC
  sorry

/- SKELETON · toList_lit
  1. A computation on a literal: evaluate it:                           R2 (with R1)
-/
-- BEGIN SPEC
theorem toList_lit : "abc".toList = ['a', 'b', 'c'] :=
-- END SPEC
  sorry

/- SKELETON · countDigits_lit
  1. Needs `countDigits` written first (Part 1). Then a computation on a
     literal; `decide` unfolds your definition by itself:              R1, R3
-/
-- BEGIN SPEC
theorem countDigits_lit : countDigits "a1b22" = 3 :=
-- END SPEC
  sorry

/- SKELETON · countDigits_singleton
  `c` is a variable, so `decide` cannot evaluate this.
  1. Replace `countDigits` by its body:                                 R4
  2. String → list: the one-character string becomes `[c]`:            R5
  3. Count on a one-element list; both sides then agree:                R6
-/
-- BEGIN SPEC
theorem countDigits_singleton (c : Char) :
    countDigits (String.singleton c) = if c.isDigit then 1 else 0 :=
-- END SPEC
  sorry

/- SKELETON · countDigits_append
  1. Replace all three `countDigits` by their bodies:                   R4
  2. String → list: `(s ++ t).toList` becomes a list append:            R7
  3. Split the count over the list append; both sides then agree:       R8
-/
-- BEGIN SPEC
theorem countDigits_append (s t : String) :
    countDigits (s ++ t) = countDigits s + countDigits t :=
-- END SPEC
  sorry

/- SKELETON · countDigits_le
  1. Replace `countDigits` by its body:                                 R4
  2. The right side is `s.length`; make it a list length
     (right to left, `simp` will not do it):                            R9
  3. Close with the list fact `countP ≤ length`:                        R10
-/
-- BEGIN SPEC
theorem countDigits_le (s : String) : countDigits s ≤ s.length :=
-- END SPEC
  sorry

end E086

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `String` is not a list: turn it into `s.toList : List Char` and let the `List` library do the
    work. The three literal theorems are computations, not proofs.
H2. Define `countDigits` with `String.toList` and `List.countP` (R2, R3). Each literal theorem is one
    `decide` (R1). For the other three: `unfold countDigits` (R4), rewrite the string lemma that moves
    to lists (R5 / R7 / R9), then use the matching `countP` lemma (R6 / R8 / R10). `simp` makes no
    progress on `… ≤ s.length`.
H3. `def countDigits (s : String) : Nat := s.toList.countP Char.isDigit`;
    `countDigits_le`: after `unfold countDigits`, the key step is `rw [← String.length_toList]` (R9);
    the list fact R10 then closes it.
-/
