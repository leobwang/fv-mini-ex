# E018 · Inductive types: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E017, in particular `rfl` and `decide` (E001), `match` (E002), `exact` (E003),
anonymous constructors `⟨_, _⟩` (E004), `simp` and `simp only [f]` (E010), `cases` and `<;>` on `Bool` and
`Option` (E016), dot notation `p.f` (E017). **New here:** declaring your own `inductive` type with several
constructors, `deriving DecidableEq`, the leading-dot shorthand `.c`, defining a function by one `match` arm
per constructor, and the fact that different constructors are never equal. No library lemmas.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : Dir → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- All entries use the guide's type `Dir` (constructors `north | east | south | west`, `deriving DecidableEq`)
  and `Dir.turn`, a quarter turn clockwise (north → east → south → west → north). In the exercise, `Color`
  plays the role of `Dir` and `Color.next` the role of `Dir.turn`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `inductive` in one paragraph

`inductive Color where | red | green | blue` declares a new type `Color` whose values are **exactly** the
three constructors `Color.red`, `Color.green`, `Color.blue` (an *enumeration*: no constructor takes
arguments). Two facts make it usable: every `c : Color` is one of the three, so `cases c` covers all of
them (R5); and different constructors are different values, so `Color.red ≠ Color.green` holds and
`simp` proves it (R7). A function out of `Color` is defined by `match` with one arm per constructor (R1),
and applying it to a constructor computes by picking that arm (R4, R6). `deriving DecidableEq` asks Lean to
generate a function deciding `a = b` for any `a b : Color`, which `decide` runs (R8). `#print Color` lists
the constructors.

## Reading the goals

| You see | It means |
|---|---|
| `Color` (as a goal, in a `def` body) | you must produce a value of type `Color` |
| `Color.red`, `.red` | the constructor `red` of `Color`; `.red` is the short form, allowed where a `Color` is expected (R2). The infoview prints `Color.red` |
| `c.next` | dot notation: `Color.next c` |
| `Color.red.next` | `Color.next Color.red`: `next` applied to the constructor `red`; reduces to that arm (R4, R6) |
| `c.next.next.next` | `Color.next (Color.next (Color.next c))`; dots chain left to right |
| `a ≠ b` | `¬ (a = b)`, i.e. `a = b → False` |
| `case red`, `case green`, `case blue` | after `cases c`: the goal with `c` replaced by that constructor (R5) |
| `case refine_1`, `refine_2`, … | after `refine ⟨?_, ?_, ?_⟩`: the goal for each `?_`, left to right (R3) |

---

## Part 1 · `Color.next` (definition body)

Statement: `Color.next (c : Color) : Color`. You write the body; `next_values` pins it down: red → green,
green → blue, blue → red. Match on `c` (R1) and give each arm its value with the leading-dot shorthand (R2).

**R1 · `match d with | .north => a | …`** is a **term**: it inspects which constructor `d` is and returns
that arm's value. Every constructor needs exactly one arm, otherwise Lean reports missing cases. In a `def`
body you write it directly after `:=` (as `Dir.turn` is written in the guide); as a tactic,
`exact match d with …` **closes** a goal of type `Dir`. Placeholders: `(d : Dir)`.

| Before | After |
|---|---|
| `d : Dir ⊢ Dir` | no goals |

**R2 · `.east` (leading-dot constructor)** changes **nothing**: where Lean expects a `Dir`, `.east` means
`Dir.east`, and the infoview prints the full name. It works in `match` patterns (`| .north => …`), in arm
values, and in statements (`… = .green`). Placeholders: `(P : Dir → Prop)`.

| Before | After `exact h` |
|---|---|
| `h : P Dir.east ⊢ P Dir.east` | no goals |

## Part 2 · `next_values`

Statement: `Color.red.next = .green ∧ Color.green.next = .blue ∧ Color.blue.next = .red`. Three equations
about specific constructors. Split the `∧`s (R3); each piece holds by computation (R4). In term mode the
whole proof is one triple of the same term.

**R3 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: `A ∧ B ∧ C` (which is `A ∧ (B ∧ C)`) becomes three
goals, one per `?_`. The term form `⟨ha, hb, hc⟩` gives all three at once. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C` | `⊢ A` (`case refine_1`), `⊢ B` (`case refine_2`), `⊢ C` (`case refine_3`) |

**R4 · `rfl`** **closes** `f c = v` when `c` is a constructor: `f c` unfolds to the `match`, the `match` sees
the constructor `c` and reduces to its arm, and both sides agree. Placeholders: none (`Dir.turn` from the
guide).

| Before | After |
|---|---|
| `⊢ Dir.north.turn = Dir.east` | no goals |

## Part 3 · `next_next_next`

Statement: `∀ c : Color, c.next.next.next = c`. Here `c` is a variable, so the `match` inside `c.next` cannot
pick an arm and `rfl` fails on the goal as given. Split `c` into its constructors first (R5); then every
goal is about a specific constructor and R4 closes it. Run R4 on all three goals with `<;>`.

**R5 · `cases d`** changes the **goal list and the context**: `d` leaves the context, and there is one goal
per constructor with `d` replaced by it, labelled `case north`, …, `case west`. Placeholders:
`(P : Dir → Prop) (d : Dir)`.

| Before | After |
|---|---|
| `d : Dir ⊢ P d` | `⊢ P Dir.north`, `⊢ P Dir.east`, `⊢ P Dir.south`, `⊢ P Dir.west` |

**W3: four quarter turns.** `d.turn.turn.turn.turn = d` falls to `cases d <;> rfl`: R5 gives four goals such
as `Dir.north.turn.turn.turn.turn = Dir.north`, and R4 computes each one turn at a time.

```lean-goal
⊢ d.turn.turn.turn.turn = d
```

## Part 4 · `next_ne`

Statement: `∀ c : Color, c.next ≠ c`. Split `c` (R5). Each goal is then `Color.red.next ≠ Color.red` and so
on: compute `next` on the constructor (R6), and what is left is two different constructors, which `simp`
knows are unequal (R7) or `decide` checks (R8). `simp [Color.next]` does R6 and R7 in one call.

**R6 · `simp only [Dir.turn]`** changes the **goal**: `Dir.turn` applied to a constructor is replaced by the
value of that arm. Placeholders: `(P : Dir → Prop)`.

| Before | After |
|---|---|
| `⊢ P Dir.east.turn` | `⊢ P Dir.south` |

**R7 · `simp`** **closes** `c₁ ≠ c₂` when `c₁` and `c₂` are different constructors. Distinct constructors of an
inductive type are never equal, and `simp` uses this for every inductive type (no lemma to name).
Placeholders: none.

| Before | After |
|---|---|
| `⊢ Dir.east ≠ Dir.north` | no goals |

**R8 · `decide`** **closes** the same goal another way: it runs the decision procedure from
`deriving DecidableEq` on the two concrete values. It needs concrete values: on `d.turn ≠ d` with a variable
`d` it fails. Placeholders: none.

| Before | After |
|---|---|
| `⊢ Dir.east ≠ Dir.north` | no goals |

**W1: one constructor by hand**, R6 then R7:

```lean-goal
⊢ Dir.north.turn ≠ Dir.north
⊢ Dir.east ≠ Dir.north
```

**W2: an arbitrary `d`.** `cases d` (R5) gives four goals, and `all_goals simp [Dir.turn]` closes each with
R6 + R7:

```lean-goal
⊢ d.turn ≠ d
⊢ Dir.north.turn ≠ Dir.north
⊢ Dir.east.turn ≠ Dir.east
⊢ Dir.south.turn ≠ Dir.south
⊢ Dir.west.turn ≠ Dir.west
```

---

## Traps

- `rfl` (or `decide`) on `c.next.next.next = c` **before** `cases c` fails: `c` is a variable, so the `match`
  cannot choose an arm and the left side does not reduce. Split first.
- `simp only [Color.next]` stops at `Color.green ≠ Color.red`; it does not close it. Finish with `simp` (R7),
  or use `simp [Color.next]` from the start.
- `cases c; rfl` runs `rfl` on the **first** goal only. Use `cases c <;> rfl` (TACTIC_STATES, "Structure").
- `.green` needs Lean to know a `Color` is expected. In `Color.red.next = .green` the left side fixes the
  type; a bare `.green = .green` with nothing else does not elaborate.
- A `match` arm is matched by constructor name: a typo such as `| .gren => …` is an error
  (``Unknown constant `Color.gren` ``), and a missing arm is an error too (`Missing cases: Color.blue`), not a
  default.
- `decide` needs concrete values: on `c.next ≠ c` with a variable `c` it fails with "Expected type must not
  contain free variables". Split with `cases c` first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a function out of `Color` | `match c with \| .red => _ \| .green => _ \| .blue => _` | R1 |
| name a constructor where the type is known | `.red` (= `Color.red`) | R2 |
| split `A ∧ B ∧ C` | `refine ⟨?_, ?_, ?_⟩`, or the term `⟨h₁, h₂, h₃⟩` | R3 |
| `f` on a constructor equals its arm | `rfl` | R4 |
| one goal per constructor | `cases c` | R5 |
| run a tactic on every goal | `t <;> u` | TACTIC_STATES |
| compute `f` on a constructor | `simp only [Color.next]` | R6 |
| two different constructors are unequal | `simp` | R7 |
| the same, by evaluation | `decide` | R8 |
| list a type's constructors | `#print Color` | |
| see the state | infoview | |
