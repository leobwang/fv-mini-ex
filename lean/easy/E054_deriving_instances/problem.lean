/- E054 | Deriving instances | 2-3 min | deriving, DecidableEq, Repr, BEq, decide on data
GOAL
  `deriving DecidableEq, Repr` makes Lean write an equality test and a printer for your types.
  Use them: write the Bool test `sameSuit`, then decide facts about concrete and symbolic cards.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E054

-- BEGIN SPEC
inductive Suit where
  | hearts | spades | clubs
  deriving DecidableEq, Repr

structure Card where
  rank : Nat
  suit : Suit
  deriving DecidableEq, Repr
-- END SPEC

/- SKELETON · sameSuit (definition body)
  1. Compare only the `suit` fields (fields: E017); the rank is ignored.
     Write the Bool test `==` that `DecidableEq Suit` supplies:                R1
     (or the same test as `decide (… = …)`:                                    R2)
-/
-- BEGIN SPEC
def sameSuit (a b : Card) : Bool :=
-- END SPEC
  sorry

/- SKELETON · sameSuit_iff
  1. Replace `sameSuit a b` by your body:                                       R3
  2. Turn the Bool fact into the Prop: the library iff matching your body      R4 (for `==`) or R5 (for `decide`)
     (`rw` closes the resulting `X ↔ X` itself.)
  Shortcut: skip step 1, `exact` sees through the definition:                  R6
     (`exact beq_iff_eq` for `==`; `exact decide_eq_true_iff` for `decide`)
-/
-- BEGIN SPEC
theorem sameSuit_iff (a b : Card) : sameSuit a b = true ↔ a.suit = b.suit :=
-- END SPEC
  sorry

/- SKELETON · cards_ne
  1. Both cards are closed values and `Card` derives `DecidableEq`:
     let Lean compute the answer.                                               R7
-/
-- BEGIN SPEC
theorem cards_ne : ({ rank := 3, suit := .hearts } : Card) ≠ { rank := 3, suit := .spades } :=
-- END SPEC
  sorry

/- SKELETON · suit_cases
  1. `s` is a variable, so R7 does not apply. Split it, one goal per suit:     R8
  2. In all three goals at once (`<;>`), one tactic settles each case:           R9
       hearts: `h1 : Suit.hearts ≠ Suit.hearts` is False                        R9
       spades: `h1 : Suit.spades ≠ Suit.hearts` is True (distinct constructors,
               dropped), `h2 : Suit.spades ≠ Suit.spades` is False              R10, R9
       clubs:  the goal `Suit.clubs = Suit.clubs` holds by `rfl`; the same
               tactic closes it (`x = x` simplifies to True)                   R9
-/
-- BEGIN SPEC
theorem suit_cases (s : Suit) (h1 : s ≠ .hearts) (h2 : s ≠ .spades) : s = .clubs :=
-- END SPEC
  sorry

end E054

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sameSuit` compares only the `suit` fields. `DecidableEq Suit` gives you a Bool test for free (R1, R2).
    `cards_ne` is about two closed values; `suit_cases` is about a variable `s` of a three-constructor type.
H2. `sameSuit_iff`: unfold `sameSuit`, then use the library iff that matches your body (R4 `beq_iff_eq` for
    `==`, R5 `decide_eq_true_iff` for `decide`). `cards_ne`: the derived `DecidableEq Card` computes it (R7).
    `suit_cases`: split `s` into its constructors (R8) and let `simp_all` settle every case (R9, R10).
H3. `def sameSuit (a b : Card) : Bool := a.suit == b.suit`; then `sameSuit_iff` is `beq_iff_eq` (R6, or
    `simp [sameSuit]`), `cards_ne` is `by decide`, and `suit_cases` is `by cases s <;> simp_all`.
-/
