# E053 · Structures with extends: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` (E001), anonymous constructors
`⟨_, _⟩` (E004), `rw` (E009), `simp` (E010), `unfold` (E012, E030), structures, fields, projections and dot notation
(E017), `refine` (E031). **New here:** `structure B extends A`: inherited fields, the parent projection
`B.toA`, the constructor `B.mk (toA : A) …`, functional update `{ x with f := v }` from a parent value, and
how projections of a constructed value reduce. Two core `Int` lemmas. No Mathlib.

## How to read an entry

Each entry is one tactic, one term, or one lemma used with `rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Rect → Prop` or `P : Int → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- All entries use the guide's own structures: `Rect` (fields `w h : Int`) and `Box extends Rect` (new field
  `d : Int`), with `Box.vol b := b.w * b.h * b.d`, `Box.cube r := { r with d := r.w }` and
  `Box.flat r := ⟨r, 0⟩`. In the exercise, `Point`/`Point3`/`z` play the roles of `Rect`/`Box`/`d`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `extends` in one paragraph

`structure Box extends Rect where d : Int` does **not** copy `w` and `h` into `Box`. It stores one field
`toRect : Rect` (the parent part) and one new field `d`. So the constructor is
`Box.mk (toRect : Rect) (d : Int) : Box`, and `Box.toRect : Box → Rect` is an ordinary projection. Lean adds
conveniences on top: `b.w` is accepted and means `b.toRect.w` (both print as `b.w`), flat field syntax
`{ w := 1, h := 2, d := 3 }` builds the nested value for you, and `{ r with d := v }` with `r : Rect`
fills the parent part from `r`. `#print Box` lists the parent, all fields, and the constructor.

## Reading the goals

| You see | It means |
|---|---|
| `Point3.lift p z` | your function applied; `(Point3.lift p z).z` is its `z` field |
| `q.toPoint` | `Point3.toPoint q : Point`, the parent part of `q : Point3` |
| `q.x` for `q : Point3` | the inherited field: really `q.toPoint.x`, printed as `q.x` |
| `{ toPoint := p, z := z }` | the value `Point3.mk p z`; this is how `{ p with z := z }` and `⟨p, z⟩` print |
| `{ toPoint := p, z := 0 }.x` | the `x` field of that value; reduces to `p.x` (R5) |
| `(Point3.lift p 0).normSq` | `Point3.normSq (Point3.lift p 0)` (dot notation, E017) |
| `0 * 0` | the `z * z` term of `normSq` after `z := 0`; `Int.mul_zero` turns it into `0` (R7) |

---

## Part 1 · `Point3.lift` (definition body)

Statement: `Point3.lift (p : Point) (z : Int) : Point3`. You write the body. `lift_toPoint` and `lift_z` say
what it must be: the parent part is `p`, the new field is `z`.

**R1 · `{ r with d := v }`** is a **term** (functional update): it copies the fields of `r` and sets the
listed ones. `r` may have the **parent** type: with `r : Rect` it gives a `Box` whose parent part is `r`.
As a tactic, `exact { r with d := v }` **closes** a hole of type `Box`. The result prints as
`{ toRect := r, d := v }`. Placeholders: `(r : Rect) (v : Int)`.

| Before | After |
|---|---|
| `r : Rect, v : Int ⊢ Box` | no goals |

**R2 · `refine ⟨r, ?_⟩`** changes the **goal**: `⟨_, _⟩` fills the constructor `Box.mk` in order, parent part
`r` first, so the goal becomes the type of the remaining field `d`. In term mode the whole value is
`⟨r, v⟩`; it is the same value as R1. Placeholders: `(r : Rect) (v : Int)`.

| Before | After |
|---|---|
| `r : Rect, v : Int ⊢ Box` | `r : Rect, v : Int ⊢ Int` |

## Part 2 · `lift_toPoint`

Statement: `(Point3.lift p z).toPoint = p`: the parent part of the lifted point is the original point.
Unfold `Point3.lift` (R3), and the left side is `{ toPoint := p, z := z }.toPoint`, which reduces to `p`
(R4). `rfl` does both steps at once (R6).

**R3 · `unfold D`** changes the **goal**: the defined name `D` is replaced by its body. Placeholders:
`(r : Rect) (P : Rect → Prop)`, `D := Box.cube` with body `{ r with d := r.w }`.

| Before | After |
|---|---|
| `⊢ P (Box.cube r).toRect` | `⊢ P { toRect := r, d := r.w }.toRect` |

**R4 · `dsimp only`** changes the **goal**: a field of a constructor value reduces to the value stored in it,
`{ toRect := r, d := v }.toRect` → `r` and `{ toRect := r, d := v }.d` → `v`. If both sides then agree,
`dsimp only` closes the goal. Placeholders: `(r : Rect) (v : Int) (P : Rect → Prop)`.

| Before | After |
|---|---|
| `⊢ P { toRect := r, d := v }.toRect` | `⊢ P r` |

**R6 · `rfl`** **closes** `a = b` when both sides are the same term after unfolding definitions and reducing
projections: R3, R4 and R5 happen inside it. Placeholders: `(r : Rect)`.

| Before | After |
|---|---|
| `r : Rect ⊢ (Box.cube r).d = r.w` | no goals |

## Part 3 · `lift_z`

Statement: `(Point3.lift p z).z = z`: the new field is the given `z`. Same route as Part 2: R3 then R4 by
hand, or `rfl` (R6) in one step.

## Part 4 · `normSq_lift_zero`

Statement: `(Point3.lift p 0).normSq = p.x * p.x + p.y * p.y`: lifting with `z = 0` adds nothing to the
squared norm. Unfold `Point3.normSq` and `Point3.lift` (R3 with two names). The left side becomes
`{ toPoint := p, z := 0 }.x * … + { toPoint := p, z := 0 }.z * { toPoint := p, z := 0 }.z`. Reduce the
inherited fields `.x`, `.y` (R5) and the new field `.z` (R4) with one `dsimp only`; what is left is
`p.x * p.x + p.y * p.y + 0 * 0`. Then R7 (`0 * 0 → 0`) and R8 (`… + 0 → …`). `simp` with both names does all of
it in one step (R9).

**R5 · `dsimp only` on an inherited field** changes the **goal**: `{ toRect := r, d := v }.w` is
`{ toRect := r, d := v }.toRect.w`, so it reduces to `r.w`. Placeholders: `(r : Rect) (v : Int) (P : Int → Prop)`.

| Before | After |
|---|---|
| `⊢ P { toRect := r, d := v }.w` | `⊢ P r.w` |

**R7 · `rw [Int.mul_zero]`** changes the **goal**. The lemma is `Int.mul_zero : ∀ (a : Int), a * 0 = 0`.
Placeholders: `(a : Int) (P : Int → Prop)`. In the exercise `a` is `0`, matching `0 * 0`.

| Before | After |
|---|---|
| `⊢ P (a * 0)` | `⊢ P 0` |

**R8 · `rw [Int.add_zero]`** changes the **goal**. The lemma is `Int.add_zero : ∀ (a : Int), a + 0 = a`.
Placeholders: `(a : Int) (P : Int → Prop)`. After the last `rw`, `rw` tries `rfl` and closes a goal whose two
sides agree.

| Before | After |
|---|---|
| `⊢ P (a + 0)` | `⊢ P a` |

**R9 · `simp [D₁, D₂]`** changes the **goal**: it unfolds `D₁, D₂` (R3), reduces projections (R4, R5), and
applies its default lemmas, `Int.mul_zero` and `Int.add_zero` among them (R7, R8). It closes the goal when the
two sides then agree. Placeholders: `(r : Rect) (P : Int → Prop)`, names `Box.vol, Box.cube`.

| Before | After |
|---|---|
| `⊢ P (Box.cube r).vol` | `⊢ P (r.w * r.h * r.w)` |

**W2: the same route by hand** on `(Box.flat r).vol = 0`: `unfold Box.vol Box.flat` (R3), `dsimp only`
(R4, R5), then `rw [Int.mul_zero]` (R7) closes it:

```lean-goal
⊢ (Box.flat r).vol = 0
⊢ { toRect := r, d := 0 }.w * { toRect := r, d := 0 }.h * { toRect := r, d := 0 }.d = 0
⊢ r.w * r.h * 0 = 0
```

**W3:** `simp [Box.vol, Box.flat]` closes the same goal in one step (R9).

---

## Traps

- The constructor of a child takes the parent part as **one** argument: `⟨p, z⟩`, not `⟨p.x, p.y, z⟩`
  (the anonymous constructor fills `Point3.mk (toPoint : Point) (z : Int)`). Flat names work only in the
  `{ … }` syntax: `{ x := p.x, y := p.y, z := z }`.
- `{ p with z := z }` is fine although `p : Point` is not a `Point3`: the source of a functional update may be
  the parent, and every field the source lacks (`z`) must be listed.
- `.x` on a `Point3` is really `.toPoint.x`. The infoview hides this, so a goal `q.x = …` is about
  `Point.x (Point3.toPoint q)`; `dsimp only` / `rfl` handle it, you never write `toPoint` yourself.
- `unfold Point3.normSq` alone leaves `(Point3.lift p 0).x`, which does not reduce until `Point3.lift` is also
  unfolded: unfold both names (or give both to `simp`).
- `simp` without the names does nothing useful: it does not unfold your `def`s unless you list them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a child from a parent value plus the new field | `{ p with z := z }` | R1 |
| the same with the constructor (parent first) | `⟨p, z⟩`, or `by refine ⟨p, ?_⟩` | R2 |
| see a definition's body | `unfold Point3.lift` | R3 |
| `{ toPoint := p, z := z }.toPoint` → `p`, `.z` → `z` | `dsimp only` | R4 |
| `{ toPoint := p, z := z }.x` → `p.x` | `dsimp only` | R5 |
| an equation that holds by unfolding | `rfl` | R6 |
| `a * 0` → `0` / `a + 0` → `a` | `rw [Int.mul_zero]` / `rw [Int.add_zero]` | R7, R8 |
| unfold, reduce and clean up in one step | `simp [Point3.normSq, Point3.lift]` | R9 |
| list a structure's fields and constructor | `#print Point3` | |
| see the state | infoview | |
