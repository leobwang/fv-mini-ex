# E017 · Structures: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E016, in particular `rfl` (E001), `exact` (E003), anonymous constructors
`⟨_, _⟩` for `∧` (E004), `constructor` (E005), `unfold` (E010). **New here:** `structure` declarations,
the constructor `T.mk`, structure-instance notation `{ f := v, … }`, the anonymous constructor `⟨…⟩` for a
structure, projections `p.f`, dot notation `p.g` for functions in the namespace `T`, `dsimp only` to reduce a
projection, and structure eta. No library lemmas.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- All entries use the guide's structure `Cell` (fields `row col : Nat`) with
  `Cell.down c := ⟨c.row + 1, c.col⟩` and `Cell.corner := { row := 5, col := 7 }`. In the exercise,
  `Point` with fields `x y` plays the role of `Cell`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `structure` in one paragraph

`structure Point where x : Nat; y : Nat` declares a new type `Point` whose values carry two `Nat`s. Lean
generates the **constructor** `Point.mk : Nat → Nat → Point` (the only way to make a `Point`) and one
**projection** per field, `Point.x : Point → Nat` and `Point.y : Point → Nat`. A value can be written
`Point.mk a b`, `⟨a, b⟩` (anonymous constructor: arguments in field-declaration order) or
`{ x := a, y := b }` (structure-instance notation: fields by name). All three are the same term, and the
infoview always prints `{ x := a, y := b }`. Projections compute: `{ x := a, y := b }.x` reduces to `a`
by definition, so `rfl` proves equations that follow from it. `{ p with x := a }` (functional update) is a
copy of `p` with field `x` replaced, i.e. `{ x := a, y := p.y }` (guide W4; not needed here). `#print Point`
lists the fields and the constructor.

## Reading the goals

| You see | It means |
|---|---|
| `Point` (as a goal, in a `def` body) | you must build a value of type `Point` |
| `case x`, `case y` | after `constructor` on a `Point` goal: the goal for field `x`, for field `y` |
| `p.x` | the projection `Point.x p`: the `x` field of `p` |
| `p.swap` | dot notation: `Point.swap p`, because `p : Point` and `swap` lives in the namespace `Point` |
| `p.swap.swap` | `Point.swap (Point.swap p)`; dots chain left to right |
| `origin.x` | `Point.x origin`; `origin` is a constant, so no argument goes before the dot |
| `{ x := a, y := b }` | the value `Point.mk a b`; this is how `⟨a, b⟩` prints |
| `{ x := a, y := b }.y` | the `y` field of that value; reduces to `b` (R6) |
| `case left`, `case right` | the two halves of an `∧` after `constructor` (R4) |

---

## Part 1 · `origin` (definition body)

Statement: `origin : Point`. You write the value; `origin_spec` says both fields must be `0`.

**R1 · `{ row := a, col := b }`** is a **term** (structure-instance notation): it builds a value by naming
each field, in any order. As a tactic, `exact { row := a, col := b }` **closes** a goal of type `Cell`.
In a `def` body you write the term itself after `:=`. Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `a b : Nat ⊢ Cell` | no goals |

## Part 2 · `Point.swap` (definition body)

Statement: `Point.swap (p : Point) : Point`. You write the body; `swap_fields` says the new `x` is the old
`y` and the new `y` is the old `x`. Read the old fields with projections (R3) and build the result with
R1 or R2.

**R2 · `⟨a, b⟩` / `constructor`** changes the **goal list**. The term `⟨a, b⟩` is `Cell.mk a b`; its
arguments fill the fields **in declaration order**, `row` first. The tactic `constructor` applies `Cell.mk`
and leaves one goal per field, labelled `case row` and `case col`. Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `a b : Nat ⊢ Cell` | `a b : Nat ⊢ Nat` (`case row`), `a b : Nat ⊢ Nat` (`case col`) |

**R3 · projections and dot notation** change **nothing**: they are two spellings of one term. `c.row` is
`Cell.row c`, and `c.down` is `Cell.down c`. `x.f` with `x : Cell` resolves to `Cell.f x` for any `Cell.f`
whose first explicit argument is a `Cell`, a field or a `def Cell.f`. The infoview prints the dotted form,
even for a hypothesis you wrote as `Cell.row (Cell.down c)`. Placeholders: `(c : Cell) (P : Nat → Prop)`.

| Before | After `exact h` |
|---|---|
| `h : P c.down.row ⊢ P c.down.row` | no goals |

## Part 3 · `origin_spec`

Statement: `origin.x = 0 ∧ origin.y = 0`. Split the `∧` (R4). Each half is a projection of a constructor
value once `origin` is unfolded (R5, R6); `rfl` does both at once (R7). In term mode the whole proof is a
pair of `rfl`s.

**R4 · `constructor` (or `⟨_, _⟩`) on `A ∧ B`** changes the **goal list**: `∧` is itself a structure,
`And.intro (left : A) (right : B)`, so R2 applies to it unchanged. The term form `⟨ha, hb⟩` gives both
halves at once. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ A` (`case left`), `⊢ B` (`case right`) |

**R5 · `unfold D`** changes the **goal**: the defined name `D` is replaced by its body. A body written
`⟨…⟩` shows up as `{ … }`. Placeholders: `(c : Cell) (P : Nat → Prop)`, `D := Cell.down`.

| Before | After |
|---|---|
| `⊢ P c.down.row` | `⊢ P { row := c.row + 1, col := c.col }.row` |

**R6 · `dsimp only`** changes the **goal**: a projection of a constructor value reduces to the value stored
in that field. `dsimp` is a `simp` that only uses definitional steps; `only` means it uses no library
lemmas, just these reductions. If both sides of an `=` then agree, it closes the goal (it does not close an
`∧`). Placeholders: `(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P { row := a, col := b }.row` | `⊢ P a` |

**R7 · `rfl`** **closes** `a = b` when both sides become the same term after unfolding definitions and
reducing projections: R5 and R6 happen inside it, you do not need to do them first.
Placeholders: `(c : Cell)`.

| Before | After |
|---|---|
| `c : Cell ⊢ c.down.col = c.col` | no goals |

## Part 4 · `swap_fields`

Statement: `p.swap.x = p.y ∧ p.swap.y = p.x`. The same route as Part 3: R4 splits; each half is closed by
R7 (or by R5 → R6 by hand). Here `p` is a variable, which does not matter: the projection reduces as soon
as `Point.swap` is unfolded, whatever `p` is.

**W2: the route by hand** on `c.down.down.row = c.row + 1 + 1 ∧ c.down.down.col = c.col`: `constructor` (R4),
then on the first goal `unfold Cell.down` (R5) and `dsimp only` (R6, which closes it), then `rfl` (R7) on the
second:

```lean-goal
⊢ c.down.down.row = c.row + 1 + 1 ∧ c.down.down.col = c.col
⊢ c.down.down.row = c.row + 1 + 1
⊢ { row := { row := c.row + 1, col := c.col }.row + 1, col := { row := c.row + 1, col := c.col }.col }.row = c.row + 1 + 1
⊢ c.down.down.col = c.col
```

## Part 5 · `swap_swap`

Statement: `p.swap.swap = p`. Unfolding `Point.swap` (R5) turns the left side into
`{ x := { x := p.y, y := p.x }.y, y := { x := p.y, y := p.x }.x }`. Reducing those projections (R6) would give
`{ x := p.x, y := p.y }`: `p` rebuilt from its own fields, which equals `p` by structure eta (R8), although
nothing is known about `p.x` and `p.y`. `dsimp only` does the reduction and the eta step together and
**closes** the goal, so after R5 → R6 there is nothing left (a following `rfl` would fail with "no goals").
`rfl` alone does all of it (R7 + R8).

**R8 · structure eta** **closes** the goal: for any `c : Cell`, `{ row := c.row, col := c.col }` is
definitionally `c`, so `rfl` proves the equation. `dsimp only` closes it too. Placeholders: `(c : Cell)`.

| Before | After `rfl` |
|---|---|
| `c : Cell ⊢ { row := c.row, col := c.col } = c` | no goals |

**W3:** `Trip.rot t := ⟨t.b, t.c, t.a⟩` on a three-field structure. `t.rot.rot.rot = t` holds by `rfl`: three
rotations reduce to `⟨t.a, t.b, t.c⟩` (R5, R6), which is `t` (R8).

---

## Traps

- `⟨a, b⟩` fills fields **by position**: for `Point`, `⟨p.y, p.x⟩` sets `x := p.y` and `y := p.x`. Writing
  `{ x := …, y := … }` names them and avoids the mix-up.
- `dsimp only` does not close `0 = 0 ∧ 0 = 0`; split the `∧` first (R4), or close each half with `rfl`.
- In a definition, the body after `:=` is a term: write `{ x := 0, y := 0 }` or `⟨p.y, p.x⟩` directly. The
  tactic forms (`by exact …`, `by constructor`) also work but are not needed.
- `rfl` for `swap_swap` works without knowing `p`: you do **not** need `cases p` (which would replace `p` by
  `{ x := x✝, y := y✝ }`). Structure eta makes `{ x := p.x, y := p.y } = p` definitional.
- After `dsimp only` closes a goal, any further tactic on it errors with "no goals". In `swap_swap`,
  `unfold Point.swap` then `dsimp only` is already a complete proof.
- `x✝` in the infoview (e.g. after `cases p`) is a name Lean invented that you cannot type; name it
  yourself with `cases p with | mk a b => …` if you need it.
- Dot notation needs the function in the type's namespace: `def Point.swap` makes `p.swap` work; a plain
  `def swap` would not.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a structure value, fields by name | `{ x := a, y := b }` | R1 |
| a structure value, fields by position | `⟨a, b⟩` (= `Point.mk a b`) | R2 |
| one goal per field | `constructor` | R2 |
| read a field / call a `Point.f` | `p.x` / `p.f` | R3 |
| split `A ∧ B` | `constructor`, or the term `⟨h₁, h₂⟩` | R4 |
| see a definition's body | `unfold Point.swap` | R5 |
| `{ x := a, y := b }.x` → `a` | `dsimp only` | R6 |
| an equation that holds by unfolding | `rfl` | R7 |
| `{ x := p.x, y := p.y } = p` | `rfl` (or `dsimp only`) | R8 |
| a copy of `p` with `x` replaced | `{ p with x := a }` | W4 |
| list a structure's fields and constructor | `#print Point` | |
| see the state | infoview | |
