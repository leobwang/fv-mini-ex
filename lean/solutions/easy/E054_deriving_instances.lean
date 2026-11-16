/- E054 | Deriving instances | 2-3 min | deriving, DecidableEq, Repr, BEq, decide on data
GOAL
  `deriving DecidableEq, Repr` makes Lean write an equality test and a printer for your types.
  Use them: write the Bool test `sameSuit`, then decide facts about concrete and symbolic cards.

REFERENCE
  inductive Color where | red | green deriving DecidableEq, Repr   -- generate both instances
  #eval (Color.red : Color)                  -- printing a value needs `Repr`
  example : Color.red ≠ Color.green := by decide   -- `decide` needs `DecidableEq` (also on structures)
  example (a b : Color) : Bool := decide (a = b)   -- a decidable Prop as a Bool
  example (a b : Color) : Bool := a == b           -- `==` (BEq) also comes from DecidableEq
  example (p : Prop) [Decidable p] : decide p = true ↔ p := decide_eq_true_iff
  example (a b : Color) : (a == b) = true ↔ a = b := beq_iff_eq
  deriving instance Inhabited for Color      -- add an instance after the fact
NOTE: core has no `Fintype`, so `decide` cannot check `∀ s : Suit, …`; split with `cases s` instead.
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

-- BEGIN SPEC
def sameSuit (a b : Card) : Bool :=
-- END SPEC
  a.suit == b.suit

-- BEGIN SPEC
theorem sameSuit_iff (a b : Card) : sameSuit a b = true ↔ a.suit = b.suit :=
-- END SPEC
  beq_iff_eq

-- BEGIN SPEC
theorem cards_ne : ({ rank := 3, suit := .hearts } : Card) ≠ { rank := 3, suit := .spades } :=
-- END SPEC
  by decide

-- BEGIN SPEC
theorem suit_cases (s : Suit) (h1 : s ≠ .hearts) (h2 : s ≠ .spades) : s = .clubs :=
-- END SPEC
  by cases s <;> simp_all

end E054

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sameSuit` only compares the `suit` fields; the derived instances give you both `decide (… = …)` and `==`.
H2. `sameSuit_iff` is one of the two library iffs on the card, after unfolding `sameSuit`. `cards_ne` is closed
    values, so the derived `DecidableEq Card` can just compute it.
H3. `def sameSuit (a b : Card) : Bool := a.suit == b.suit`; then `sameSuit_iff` is `beq_iff_eq` (or `simp [sameSuit]`),
    `cards_ne` is `by decide`, and `suit_cases` is `by cases s <;> simp_all`.
-/
