/- E018 | Inductive types | 2-3 min | inductive, match, cases
GOAL
  Define `Color.next` (red → green → blue → red) and prove it cycles with period 3.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
inductive Color where
  | red | green | blue
  deriving DecidableEq
-- END SPEC

/- SKELETON · Color.next (definition body)
  1. Inspect which constructor `c` is, one arm per constructor (next_values gives
     the three values: red → green, green → blue, blue → red):                       R1
  2. Write each pattern and each value with the leading-dot shorthand `.red`:        R2
-/
-- BEGIN SPEC
def Color.next (c : Color) : Color :=
-- END SPEC
  match c with
  | .red => .green
  | .green => .blue
  | .blue => .red

/- SKELETON · next_values
  1. Split the two nested `∧` into three goals (or write one term triple):           R3
  2. Each goal is `next` on a specific constructor: it computes to its arm:          R4
-/
-- BEGIN SPEC
theorem next_values : Color.red.next = .green ∧ Color.green.next = .blue ∧ Color.blue.next = .red :=
-- END SPEC
  ⟨rfl, rfl, rfl⟩

/- SKELETON · next_next_next
  1. `c` is a variable, so nothing computes yet: one goal per constructor:           R5
  2. On every goal at once (`<;>`, TACTIC_STATES): three steps of computation:       R4
-/
-- BEGIN SPEC
theorem next_next_next (c : Color) : c.next.next.next = c :=
-- END SPEC
  by cases c <;> rfl

/- SKELETON · next_ne
  1. One goal per constructor:                                                       R5
  2. On every goal (`<;>`): compute `next` on the constructor, then the two sides
     are different constructors:                                                     R6 → R7
     (R6 and R7 in one call: `simp` given the definition's name; R8 also does R7)
-/
-- BEGIN SPEC
theorem next_ne (c : Color) : c.next ≠ c :=
-- END SPEC
  by cases c <;> simp [Color.next]

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `next_values` pins down `next` completely: one `match` arm per color (R1, R2). Every theorem about an
    arbitrary `c` is stuck until you know which constructor `c` is.
H2. `next_values`: split and compute (R3, R4). The other two: split `c` into its three constructors (R5),
    then compute on each goal; for `≠`, finish with the fact that different constructors differ (R6, R7).
H3. `match c with | .red => .green | .green => .blue | .blue => .red`; `next_values` is `⟨rfl, rfl, rfl⟩`;
    then `cases c <;> rfl` and `cases c <;> simp [Color.next]`.
-/
