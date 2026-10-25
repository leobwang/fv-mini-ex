/- E18 | Inductive types | 2-3 min | inductive, match, cases
GOAL
  Define `Color.next` (red → green → blue → red) and prove it cycles with period 3.

REFERENCE
  inductive Dir where
    | up | down
    deriving DecidableEq
  def Dir.flip : Dir → Dir | .up => .down | .down => .up   -- `.up` means `Dir.up` here
  example (d : Dir) : d.flip.flip = d := by cases d <;> rfl
  example : Dir.up ≠ Dir.down := by decide            -- uses the derived DecidableEq
  example (d : Dir) : d.flip ≠ d := by cases d <;> simp [Dir.flip]   -- simp knows ctors differ
-/

-- BEGIN SPEC
inductive Color where
  | red | green | blue
  deriving DecidableEq
-- END SPEC

-- BEGIN SPEC
def Color.next (c : Color) : Color :=
-- END SPEC
  match c with
  | .red => .green
  | .green => .blue
  | .blue => .red

-- BEGIN SPEC
theorem next_values : Color.red.next = .green ∧ Color.green.next = .blue ∧ Color.blue.next = .red :=
-- END SPEC
  ⟨rfl, rfl, rfl⟩

-- BEGIN SPEC
theorem next_next_next (c : Color) : c.next.next.next = c :=
-- END SPEC
  by cases c <;> rfl

-- BEGIN SPEC
theorem next_ne (c : Color) : c.next ≠ c :=
-- END SPEC
  by cases c <;> simp [Color.next]

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `next_values` pins down `next` completely: one `match` arm per color.
H2. Every theorem about an arbitrary `c` follows by splitting `c` into its three constructors.
H3. `match c with | .red => .green | .green => .blue | .blue => .red`; then `cases c <;> rfl` and `cases c <;> simp [Color.next]`.
-/
