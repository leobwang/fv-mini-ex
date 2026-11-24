# E056 · Sections and variables: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `have`, `rw`, `simp`, `rfl`, `omega`,
`∧`/`↔` and their projections, `List` and `++`. **New here:** the commands `section … end`, `variable`,
`include … in`, `namespace … end` and `open … in`, which change *which names and arguments a declaration
gets*, not what it proves. No Mathlib.

## How to read an entry

Each entry is one command, tactic, or lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : List α → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `α : Type`, `xs : List α` in the context | section variables this declaration received (R1) |
| `twice xs` | the section `def` applied to its argument; inside the section you write the argument too |
| `hne : xs ≠ []` in the context | received through `include hne in` (R7) |
| `a ≠ b` | `¬ (a = b)`, i.e. `a = b → False` |
| `l.length` | `List.length l` (dot notation) |
| `Shape.area w h` | the `area` of namespace `Shape`; the infoview prints the full name outside the namespace |
| `xs ++ ys` | `List.append xs ys`: the elements of `xs`, then those of `ys` |
| `[]` | the empty list (`List.nil`) |
| `h2 : xs = [] ∧ xs = []` | what R9 gives for `h : twice xs = []`: both halves are the same fact |

### Commands that decide what a declaration receives

| Command | Effect |
|---|---|
| `section S` … `end S` | a scope: `variable`, `include` and `open` lines inside it stop at `end S` |
| `variable {α : Type} (xs : List α)` | every later declaration in the scope may use `α`, `xs` without binding them |
| which variables a declaration gets | a `theorem` or `def` gets the variables its **statement** (for a `def`: its type and body) mentions, plus what their types need (`xs` needs `α`). A `theorem`'s proof cannot add more |
| `include h in` + one declaration | that declaration also gets `h`, as an extra argument, though its statement never mentions it |
| outside the section | the variables become ordinary arguments: `twice : {α : Type} → List α → List α`, `twice_ne_nil : ∀ {α : Type} (xs : List α), xs ≠ [] → twice xs ≠ []` |
| `namespace X` … `end X` | every name declared inside gets the prefix `X.`; inside, the short name works |
| `open X in cmd` / `open X in tac` | the short names of `X` work for that one command or tactic |

---

## Part 1 · `twice_length`

Statement: `(twice xs).length = 2 * xs.length`. Doubling a list doubles its length.

**R1 · `variable` in a `section`** changes the **context** of every declaration after it: a theorem
receives the variables its statement mentions and no others. Placeholders: `variable {α : Type} (l m : List α)
(x : α) (hl : l.length = 3)`; the theorem `l ++ [] = l` mentions only `l`.

| Before (source) | After (proof state) |
|---|---|
| `variable {α : Type} (l m : List α) (x : α) (hl : l.length = 3)` | `α : Type, l : List α ⊢ l ++ [] = l` |

**R2 · a section `def`, then `unfold snoc`** changes the **goal**: the defined name is replaced by its body.
`def snoc : List α := l ++ [x]` mentions `l` and `x`, so it takes both: inside and outside the section you write
`snoc l x`. Placeholders: `(P : List α → Prop)`.

| Before | After |
|---|---|
| `x : α ⊢ P (snoc l x)` | `x : α ⊢ P (l ++ [x])` |

**R3 · `rw [List.length_append]`** changes the **goal**. The lemma is
`List.length_append : (as ++ bs).length = as.length + bs.length`. Placeholders: `{α : Type} (p q : List α)
(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (p ++ q).length` | `⊢ P (p.length + q.length)` |

**R4 · `simp [snoc]`** changes the **goal**: it unfolds `snoc` (R2), applies R3 and `[x].length = 1`, and stops
at arithmetic it cannot finish. It does not reorder sums, so `l.length + 1 = 1 + l.length` is left.

| Before | After |
|---|---|
| `⊢ (snoc l x).length = 1 + l.length` | `⊢ l.length + 1 = 1 + l.length` |

**R5 · `omega`** **closes** a linear goal over `Nat` or `Int`. Any other subterm, such as `l.length`, `f a b` or
`a * b`, is an opaque unknown to it. Placeholders: `(f : Nat → Nat → Nat) (a b : Nat)`.

| Before | After |
|---|---|
| `⊢ f a b + f a b = 2 * f a b` | no goals |

**W1.** `def thrice : List α := l ++ l ++ l`. `simp [thrice]` reassociates the sum, then `omega` closes it:

```lean-goal
⊢ (thrice l).length = 3 * l.length
⊢ l.length + (l.length + l.length) = 3 * l.length
```

## Part 2 · `twice_append`

Statement: `twice (xs ++ ys) = xs ++ ys ++ (xs ++ ys)`: `twice` applied to an append. This theorem mentions
`ys`, so it receives `ys` too (R1).

**R6 · `rfl`** **closes** an equation whose sides agree after unfolding definitions; no rewriting is needed.

| Before | After |
|---|---|
| `⊢ snoc l x = l ++ [x]` | no goals |

## Part 3 · `twice_ne_nil`

Statement: `twice xs ≠ []`, which is false for `xs = []`. The hypothesis `hne : xs ≠ []` is a section variable
the statement never mentions, so only the frozen `include hne in` line puts it in the context.

**R7 · `include hl in`** changes the **context** of the next declaration: it gains `hl`. Placeholders: the
section variable `(hl : l.length = 3)`; the theorem `0 < l.length`.

| Before (without `include hl in`) | After |
|---|---|
| `hl` absent: `omega` fails, and writing `hl` is "Unknown identifier" | `hl : l.length = 3 ⊢ 0 < l.length` |

**R8 · `intro h`** on a `≠` goal changes the **goal and the context**. `a ≠ b` unfolds to `a = b → False`, so
`intro` assumes the equation. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R9 · `have h2 := List.append_eq_nil_iff.mp h`** changes the **context**. The lemma is
`List.append_eq_nil_iff : p ++ q = [] ↔ p = [] ∧ q = []`; `.mp` is its left-to-right direction, a function from
`p ++ q = []` to the conjunction. `h` may also be `twice xs = []`: Lean unfolds `twice` when it checks the
argument. Placeholders: `{α : Type} (p q : List α) (h : p ++ q = [])`.

| Before | After |
|---|---|
| `h : p ++ q = [] ⊢ G` | `h2 : p = [] ∧ q = [] ⊢ G` |

**R10 · `have ha := h.1`** changes the **context**: `h.1 : A` and `h.2 : B` for `h : A ∧ B` (`And.left`,
`And.right`). Placeholders: `(A B : Prop) (h : A ∧ B)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `ha : A ⊢ G` |

**R11 · `exact hne hp`** **closes** `False`: `hne : p ≠ []` is a function `p = [] → False`, applied to
`hp : p = []`. Placeholders: `{α : Type} (p : List α)`.

| Before | After |
|---|---|
| `hne : p ≠ [], hp : p = [] ⊢ False` | no goals |

R9–R11 also fit in one term, `hne (List.append_eq_nil_iff.mp h).1`, after R8.

**W2.** With `include hm in` for `hm : m ≠ []`, prove `l ++ m ≠ []` from the **right** half, `h2.2`:

```lean-goal
⊢ l ++ m ≠ []
⊢ False
```

## Part 4 · `area_twice`

Statement: `Shape.area w h + Shape.area h w = 2 * Shape.area w h`. `Shape.area w h` is `w * h`, and `omega`
sees `w * h` and `h * w` as two unrelated unknowns, so first make both summands the same term with the frozen
lemma `Shape.area_comm (w h : Nat) : area w h = area h w`.

**R12 · `rw [Rect.perim_comm b a]`** changes the **goal**. Outside `namespace Rect`, the lemma is called by its
full name. The explicit arguments fix the instance: it rewrites `Rect.perim b a` and leaves `Rect.perim a b`
alone. Without arguments `rw` fixes them from the first match it finds and rewrites every copy of that
term. Placeholders:
`def perim (w h : Nat) : Nat := 2 * w + 2 * h` and `perim_comm (w h : Nat) : perim w h = perim h w` in
`namespace Rect`, `(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Rect.perim a b + Rect.perim b a)` | `⊢ P (Rect.perim a b + Rect.perim a b)` |

**R13 · `open Rect in rw [perim_comm a b]`** is the same step with the short name; the `open` lasts for this one
tactic. Here the arguments `a b` select `Rect.perim a b`.

| Before | After |
|---|---|
| `⊢ P (Rect.perim a b + Rect.perim b a)` | `⊢ P (Rect.perim b a + Rect.perim b a)` |

Then R5 finishes: `Shape.area w h` is a single unknown to `omega`.

**W3.** R13, then R5, on `Rect.perim`:

```lean-goal
⊢ Rect.perim b a + 2 * Rect.perim a b = 3 * Rect.perim a b
⊢ Rect.perim a b + 2 * Rect.perim a b = 3 * Rect.perim a b
```

---

## Traps

- Never add a `variable` or `include` line yourself, not even after a spec region: it changes the arguments of
  the frozen statements after it, and the checker rejects that.
- An `example` inside a section sees **every** `variable`; a `theorem` sees only the ones its statement
  mentions or that are `include`d. A proof that works as an `example` can fail as a `theorem` with "Unknown
  identifier".
- `include h in` covers one declaration. A bare `include h` (no `in`) covers the rest of the section.
- Do not unfold `Shape.area` for `area_twice`: `w * h + h * w = 2 * (w * h)` is nonlinear, and `omega` fails on
  it. `Nat.mul_comm` is banned; the namespaced lemma is the intended route.
- `rw [Shape.area_comm]` without arguments fixes `w h` from the first `area` it meets and rewrites every copy of
  that term. Here that happens to work too (goal `Shape.area h w + Shape.area h w = 2 * Shape.area h w`), but in
  general give the arguments, so you choose which occurrence moves.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| know what a theorem in a section receives | the variables its statement mentions | R1 |
| expose a definition's body | `unfold f` | R2 |
| `(p ++ q).length` → sum | `rw [List.length_append]` | R3 |
| unfold and simplify lengths | `simp [f]` | R4 |
| linear arithmetic, atoms allowed | `omega` | R5 |
| equal by definition | `rfl` | R6 |
| a section hypothesis the statement does not mention | the frozen `include h in` | R7 |
| prove `a ≠ b` | `intro h` (goal `False`) | R8 |
| `p ++ q = []` → both empty | `List.append_eq_nil_iff.mp h` | R9 |
| halves of `A ∧ B` | `h.1`, `h.2` | R10 |
| close `False` from `hne : p ≠ []` | `exact hne hp` | R11 |
| a namespaced lemma, one occurrence | `rw [X.lemma a b]` | R12 |
| short name for one tactic | `open X in tac` | R13 |
| see the state | infoview | |
