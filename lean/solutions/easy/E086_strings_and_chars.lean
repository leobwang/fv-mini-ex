/- E086 | Strings and chars | 2-3 min | String, Char, toList, List.countP, decide on literals
GOAL
  Write `countDigits s` (how many characters of `s` are digits `0`–`9`), check literal facts with
  `decide`, and prove: on a one-character string (`String.singleton c`) the count is 1 if `c` is a
  digit and 0 otherwise, it adds up over `++`, and it never exceeds `s.length`.

REFERENCE
  example : "ab" ++ "c" = "abc" := by decide       -- `decide` (or `rfl`) evaluates literals
  example : "hi".toList = ['h', 'i'] := by decide  -- `'h'` is a Char; `.toList : List Char`
  example : 'a'.toNat = 97 := rfl                   -- `.toNat` is the character's code point
  example : '7'.isDigit = true := rfl               -- Char tests such as `isDigit` return Bool
  example : [1, 20, 3].countP (· > 2) = 2 := by decide  -- count entries passing a Bool test
  #check @String.toList_append   -- (s ++ t).toList = s.toList ++ t.toList
  #check @String.length_toList   -- s.toList.length = s.length
  #check @List.countP_append     -- countP p (l₁ ++ l₂) = countP p l₁ + countP p l₂
  #check @List.countP_le_length  -- countP p l ≤ l.length
  #check @String.toList_singleton  -- (String.singleton c).toList = [c]
  #check @List.countP_singleton    -- countP p [a] = if p a = true then 1 else 0
BANNED: grind, exact?, try?
NOTE: a `String` is UTF-8 data, not a `List Char`; reason about it through `s.toList`.
-/

namespace E086

-- BEGIN SPEC
def countDigits (s : String) : Nat :=
-- END SPEC
  s.toList.countP Char.isDigit

-- BEGIN SPEC
theorem lit_facts : "hello".length = 5 ∧ 'a'.toNat = 97 ∧ '7'.isDigit = true :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem toList_lit : "abc".toList = ['a', 'b', 'c'] :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem countDigits_lit : countDigits "a1b22" = 3 :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem countDigits_singleton (c : Char) :
    countDigits (String.singleton c) = if c.isDigit then 1 else 0 :=
-- END SPEC
  by
    unfold countDigits
    rw [String.toList_singleton, List.countP_singleton]

-- BEGIN SPEC
theorem countDigits_append (s t : String) :
    countDigits (s ++ t) = countDigits s + countDigits t :=
-- END SPEC
  by
    unfold countDigits
    rw [String.toList_append, List.countP_append]

-- BEGIN SPEC
theorem countDigits_le (s : String) : countDigits s ≤ s.length :=
-- END SPEC
  by
    unfold countDigits
    -- WHY: `simp` does not rewrite `s.length` to `s.toList.length` on its own.
    rw [← String.length_toList]
    exact List.countP_le_length

end E086

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Turn the string into a list of characters first; the list library then does the work.
H2. Define `countDigits` with `List.countP` and `Char.isDigit`. The three literal theorems are
    one `decide` each. For the other three, `unfold countDigits` and rewrite with the card's
    `_singleton` / `_append` / `length_toList` lemmas. (`simp` misses `s.toList.length = s.length`.)
H3. `def countDigits (s : String) : Nat := s.toList.countP Char.isDigit`;
    `countDigits_le`: `unfold countDigits; rw [← String.length_toList]; ...`.
-/
