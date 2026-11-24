# M002 · Peano addition is commutative: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `def` by pattern matching, `induction`, `rfl`,
`rw`, `simp`. **New here:** structural induction on a type you defined yourself, which side of a recursive
definition unfolds by computation, constructor injectivity (`N.succ.injEq`), and stating your own **helper
lemmas** (milestones) when the induction hypothesis alone is not enough. Core Lean only, no Mathlib.

## The objects

- **`N`**: unary naturals, `N.zero` and `N.succ n` ("n + 1"). It is your own type: none of the `Nat` lemmas
  (`Nat.add_comm`, …) and no `omega` apply to it.
- **`add n m`**: "n + m", recursing on the **second** argument: `add n .zero = n`,
  `add n (.succ m) = .succ (add n m)`. Both equations hold by computation (`rfl`). The mirrored facts
  `add .zero n = n` and `add (.succ a) b = .succ (add a b)` are **not** equations of `add`: each needs its
  own induction on `n` resp. `b`.
- **Holes:** `add_assoc : add (add a b) c = add a (add b c)` and `add_comm : add a b = add b a`.
- The guide teaches on a toy type `U` (same shape as `N`) and a toy function `plus2 n m` ("n + 2·m"), which
  recurses the same way as `add`. It is **not** the exercise's function.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means the goal is closed.
- `P` is "the rest of your goal" (`P : U → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders: `(n m a b : U)`, `(f g : U → U → U)`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `N.zero`, `U.zero` | the constructor `zero` |
| `n.succ` | `N.succ n` ("n + 1"). Lean prints a constructor applied to `n` with dot notation |
| `(add n m).succ.succ` | `N.succ (N.succ (add n m))` |
| `.succ m` in source | `N.succ m`; the leading `.` means "the constructor of the expected type" |
| `add (add a b) c` | `(a + b) + c`; the induction runs on `c`, the argument `add` recurses on |
| `case zero`, `case succ` | the goal for the constructor `zero` / `succ` after `induction` |
| `n✝`, `n_ih✝` | inaccessible names made by plain `induction n`; name them with `with \| succ n ih` |

## Why induct on the second argument

`add` unfolds only when its **second** argument is literally `.zero` or `.succ _`. After `induction c`, the
goal for `add_assoc` has `c` replaced by `.zero` / `.succ c` in exactly the second-argument positions, so
every `add … c` unfolds. Inducting on `a` instead leaves `add (.succ a) b`, which no equation of `add`
touches. For `add_comm` either choice puts the inducted variable in a **first**-argument position on one side
(`add b a`), and that side is stuck: this is what the two helper lemmas are for.

---

## Part 1 · `add_assoc`

Statement: `add (add a b) c = add a (add b c)`. Induct on `c`. `zero`: both sides compute to `add a b` (R2).
`succ`: unfold `add` on both sides, peel the outer `succ`, and the rest is `ih` (R3, R4, R5, together: R7).

**R1 · `induction n`** changes the **goal list and the context**: one goal per constructor. In `succ` the
context gains the variable `n✝` and the induction hypothesis `n_ih✝ : P n✝`. With
`induction n with | zero => … | succ n ih => …` they are named `n` and `ih`. Placeholders: `(P : U → Prop) (n : U)`.

| Before | After (case `zero`) | After (case `succ`) |
|---|---|---|
| `n : U ⊢ P n` | `⊢ P U.zero` | `n✝ : U, n_ih✝ : P n✝ ⊢ P n✝.succ` |

**R2 · `rfl`** **closes** an equation whose two sides compute to the same term. `plus2 n .zero` is literally
the first equation of `plus2`. In the exercise: `add (add a b) .zero` and `add a (add b .zero)` both compute to
`add a b`. Placeholders: `(n : U)`.

| Before | After |
|---|---|
| `⊢ plus2 n U.zero = n` | `∅` |

**R3 · `simp only [f]`** changes the **goal**: it rewrites `f` applied to a literal constructor in the
recursion position by the body of that equation. In the exercise: `simp only [add]` turns `add n m.succ` into
`(add n m).succ`. Placeholders: `(n m : U)`.

| Before | After |
|---|---|
| `⊢ P (plus2 n m.succ)` | `⊢ P (plus2 n m).succ.succ` |

**R4 · `U.succ.injEq`** changes the **goal**. Statement: `(U.succ a = U.succ b) = (a = b)`; Lean generates it
for every constructor (as `N.succ.injEq` for `N`), and `simp` applies it by itself. Placeholders: `(a b : U)`.

| Before | After |
|---|---|
| `⊢ a.succ = b.succ` | `⊢ a = b` |

**R5 · `rw [ih]`** with `ih : l = r` changes the **goal**: every `l` becomes `r`; `l` must occur literally.
`rw` then tries `rfl`, so it may close the goal. Placeholders: `(l r : U) (ih : l = r)`.

| Before | After |
|---|---|
| `ih : l = r ⊢ P l.succ` | `ih : l = r ⊢ P r.succ` |

**R7 · `simp [f, ih]`** **closes** an induction step: unfold `f` (R3), peel constructors (R4), rewrite with
`ih` (R5) and with any lemma listed (R6), until both sides agree. Placeholders: `(a m : U)`.

| Before | After |
|---|---|
| `ih : plus2 a m = m ⊢ plus2 a m.succ = m.succ.succ` | `∅` |

---

## Part 2 · `add_comm`

Statement: `add a b = add b a`. Induct on `b`. The left side `add a b` unfolds, the right side `add b a` has
`b` in the first position and is stuck in both cases:

- `zero`: `add a .zero = add .zero a` computes to `a = add .zero a`. Needs the **milestone**
  `zero_add (n : N) : add .zero n = n`.
- `succ`: `add a b.succ = add b.succ a` unfolds on the left to `(add a b).succ`; the right needs the
  **milestone** `succ_add (a b : N) : add (.succ a) b = .succ (add a b)`, after which the goal is `ih` under a
  `succ`.

Prove both milestones first, as `theorem`s of their own between `add` and `add_comm` (outside the spec
regions). Each is an induction on the argument `add` recurses on (the second one: `n` in `zero_add`, `b` in
`succ_add`) with R1, R2, R7, exactly as in Part 1 and W1.

**R6 · `rw [lem]`** with `lem : ∀ x y, f (.succ x) y = g x y` changes the **goal**: `rw` finds the first
instance of the left side, fills in `x`, `y` by matching, and rewrites. A helper lemma is used the same way, by
`rw [succ_add]` or inside `simp [add, succ_add, ih]` (R7). `rw [← lem]` rewrites right to left.
Placeholders: `(f g : U → U → U) (a b : U)`.

| Before | After |
|---|---|
| `⊢ P (f a.succ b)` | `⊢ P (g a b)` |

**W1** proves the toy helper `succ_plus2 : plus2 (.succ a) b = .succ (plus2 a b)` by `induction b`, `rfl` and
`simp [plus2, ih]` (R1, R2, R7). **W2** shows the step it unblocks, for the toy theorem
`plus2 (plus2 a b) c = plus2 (plus2 a c) b` by induction on `c` (here `ih` is that statement at `c`):

```lean-goal
⊢ plus2 (plus2 a b) c.succ = plus2 (plus2 a c.succ) b
⊢ (plus2 (plus2 a b) c).succ.succ = plus2 (plus2 a c).succ.succ b
⊢ (plus2 (plus2 a b) c).succ.succ = (plus2 (plus2 a c) b).succ.succ
```

The lines are: the step; after `simp only [plus2]` (R3; the right side is stuck at a first-argument `succ`);
after `rw [succ_plus2, succ_plus2]` (R6). Then `rw [ih]` (R5) closes it. **W3** is the whole proof in two
lines: `| zero => rfl` and `| succ c ih => simp [plus2, succ_plus2, ih]`.

---

## Traps

- `add .zero n = n` is **not** `rfl`: `add` recurses on its second argument, and `n` is unknown. It needs
  induction (milestone `zero_add`). Same for `add (.succ a) b`.
- Inducting on the first argument (`induction a` in `add_assoc`) leaves `add (.succ a) b`, which `simp [add]`
  cannot unfold.
- A helper lemma must be declared **above** the theorem that uses it, and outside the `BEGIN SPEC`/`END SPEC`
  regions (they are frozen).
- `Nat` lemmas and `omega` do not apply to `N`: it is your own type. Everything follows from the two
  equations of `add` by induction.
- `simp [ih]` with `ih : add a b = add b a` does not loop: `simp` uses such a commutativity-shaped rule only
  when it makes the term smaller in a fixed order. `rw [ih]` rewrites once, wherever `add a b` occurs.
- With `induction … with`, each `| zero => …` / `| succ c ih => …` alternative is the tactic block for its
  goal. A multi-line block goes on the following lines, indented further than the `|`. Without `with`, the
  `succ` variable and hypothesis are inaccessible (`n✝`, `n_ih✝`) and `rw [ih]` has nothing to name.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per constructor, IH named | `induction c with \| zero => … \| succ c ih => …` | R1 |
| close a base case that computes | `rfl` | R2 |
| unfold `add n (.succ m)` / `add n .zero` | `simp only [add]` (or inside `simp [add, …]`) | R3 |
| `x.succ = y.succ → x = y` | applied by `simp` (`N.succ.injEq`) | R4 |
| use the IH | `rw [ih]` or `simp [add, ih]` | R5, R7 |
| `add .zero n = n` | milestone `zero_add`, induction on `n` | R1, R2, R7 |
| `add (.succ a) b = .succ (add a b)` | milestone `succ_add`, induction on `b` | R1, R2, R7 |
| use a milestone | `rw [succ_add]`, `simp [add, zero_add]`, `simp [add, succ_add, ih]` | R6, R7 |
| see the state | infoview | |
