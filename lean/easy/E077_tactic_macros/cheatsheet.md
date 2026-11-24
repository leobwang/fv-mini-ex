# E077 · Tactic macros: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide` (E001), tactic mode and `assumption` (E003), `∧` and
`constructor` (E005), `rfl` (E009), `simp` / `simp_all` (E010), `omega` (E011). **New here:** the
combinator `first | t₁ | t₂`, and Lean's *macro* commands, which give a tactic script a new name:
`` macro "name" : tactic => `(tactic| …) ``, and the two-step form `syntax` + `macro_rules`; tactic
quotations `` `(tactic| …) `` and *hygiene*. No Mathlib.

What a macro is: a rewrite of syntax before anything runs. After
`` macro "crush" : tactic => `(tactic| tac) ``, writing `by crush` is the same as writing `by tac`: Lean
replaces the word and runs `tac` on the goal. A macro proves nothing on its own. Here the three
`by crush` proofs are frozen; you change only what `crush` expands to.

## How to read an entry

Each entry is one tactic or one command. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- "no goals" means the tactic closed the goal.
- `{α : Type}` is any type; `A B : Prop` are any propositions; `x y a b : Nat` any natural numbers.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `macro "crush" : tactic => …` | a command (top level, not inside a proof): declares the tactic `crush` |
| `` `(tactic| t) `` | a quotation: the tactic syntax `t`, as data. It runs only where the macro is used |
| `first \| t₁ \| t₂ \| t₃` | one tactic: try `t₁`; if it fails, try `t₂` on the original goal; and so on |
| `sorry` inside the stub's quotation | `by crush` currently means `by sorry`: the theorems are open (TODO) |
| `h✝` in the context | an inaccessible hypothesis: it exists, but no name you type refers to it (R7) |
| `[] ++ xs` | the empty list appended to `xs` |
| `declaration uses 'sorry'` on `t1` | reported at the theorem, though the `sorry` comes from the macro |

---

## Part 1 · the macro `crush` (checked by `t1`, `t2`, `t3`)

The hole is the body of `macro "crush"`. The frozen theorems need one tactic that closes all three goals:

| Theorem | Goal (context) | Closer |
|---|---|---|
| `t1` | `n + 0 = n` | computes: `+` on `Nat` recurses on its second argument, so `n + 0` reduces to `n` |
| `t2` | `a + 1 ≤ b` with `h : a < b` | linear arithmetic over `Nat` using `h` |
| `t3` | `P ∧ Q` with `hp : P`, `hq : Q` | uses the hypotheses; `rfl` and `omega` both fail |

### The three closers

**R1 · `rfl`** **closes** an equation `l = r` whose sides compute to the same term (definitional equality),
and fails otherwise. `[] ++ xs` reduces to `xs` because `List.append` is defined by recursion on its first
argument. Placeholders: `{α : Type} (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ [] ++ xs = xs` | no goals |

**R2 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `-`, numerals,
numeral `*`, `≤ < = ≠`, `∧ ∨ ¬ →`), using such hypotheses from the context, and fails otherwise (E011).
It fails on `P ∧ Q` for propositions `P Q`. Placeholders: `(x y : Nat) (h : x ≤ y)`.

| Before | After |
|---|---|
| `h : x ≤ y ⊢ x < y + 1` | no goals |

**R3 · `simp_all`** changes the **context and the goal**, and here **closes** it: it simplifies every
hypothesis with the others and the goal with all of them (E010). `hab : A ∧ B` is split into `A` and `B`,
these rewrite the goal's `B` and `A` to `True`, and `True ∧ True` simplifies to `True`. It fails if it
makes no progress. Placeholders: `(A B : Prop) (hab : A ∧ B)`. `constructor <;> assumption` (W1) is another
closer for a conjunction of hypotheses.

| Before | After |
|---|---|
| `hab : A ∧ B ⊢ B ∧ A` | no goals |

### Combining them

**R4 · `first | t₁ | t₂ | t₃`** changes the **goal** as the first alternative that does not fail changes
it. A failing alternative is undone completely, so the next one starts on the original goal. Here `rfl`
fails (the goal is `<`, not `=`) and `omega` closes it. Placeholders: `(x y : Nat) (h : x ≤ y)`.

| Before | After `first \| rfl \| omega` |
|---|---|
| `h : x ≤ y ⊢ x < y + 1` | no goals (by `omega`) |

### Naming the combination

**R5 · `` macro "name" : tactic => `(tactic| tac) ``** is a **command**: it declares a new tactic `name`. In a
proof, `name` changes the **goal** exactly as `tac` would, because Lean substitutes `tac` for it before
running anything. The quotation `` `(tactic| tac) `` holds any tactic you could write after `by`,
`first | …` and `t₁ <;> t₂` included. Placeholders: the name `close_eq`, the script
`first | rfl | omega`.

| Before | After `close_eq` |
|---|---|
| `h : x ≤ y ⊢ x < y + 1` | no goals (as R4) |

**R6 · `syntax "name" : tactic` + `macro_rules`** is the two-step form of R5. `syntax` makes the word parse
as a tactic; each `` macro_rules | `(tactic| name) => `(tactic| tac) `` adds one expansion. When `name` runs,
Lean tries the **most recent** rule first and, if its tactic fails, the previous one. Several rules act
like `first`, in reverse order of declaration. In the guide, `close_two` has rules `rfl`, then `omega`:
`omega` fails on the list equation and `rfl` closes it. Placeholders: `{α : Type} (xs : List α)`.

| Before | After `close_two` |
|---|---|
| `xs : List α ⊢ [] ++ xs = xs` | no goals (by the `rfl` rule) |

**R7 · hygiene** changes the **context** in a way you might not expect. A name written inside a quotation
is fresh: it is never the same as a name in the goal. So `intro h` inside a macro adds a hypothesis that
prints as `h✝` (inaccessible: `exact h` after it fails), and a macro body that writes `hp` does not see the
goal's `hp`. Tactics that search the context (`assumption`, `omega`, `simp_all`) are unaffected.
Placeholders: `(a : Nat)`; the macro `intro_h` expands to `intro h`.

| Before | After `intro_h` | After `omega` |
|---|---|---|
| `a : Nat ⊢ a = 3 → a + 1 = 4` | `h✝ : a = 3 ⊢ a + 1 = 4` | no goals |

### Worked combinations (W1–W3, on goals that are not the exercise's)

**W1 · `split_close` := `constructor <;> assumption`.** `constructor` splits `B ∧ A` into `⊢ B` and `⊢ A`;
`<;>` runs `assumption` on both, and `assumption` finds `hb`, `ha` without naming them (R7).

| Before | After `split_close` |
|---|---|
| `ha : A, hb : B ⊢ B ∧ A` | no goals |

**W2 · `close_any` := `first | assumption | decide | omega`, used on three goals.** Each use runs a
different alternative of R4: `assumption` on a goal that is a hypothesis, `decide` (E001) on a closed
arithmetic fact, `omega` on arithmetic with variables (`decide` fails there: it cannot evaluate `a < b`
for unknown `a`, `b`).

| Before | After `close_any` |
|---|---|
| `hb : B ⊢ B` | no goals (`assumption`) |
| `⊢ 2 + 3 = 5` | no goals (`decide`) |
| `h : b = a + 2 ⊢ a < b` | no goals (`omega`) |

**W3 · `intro_omega` := `(intro h; omega)`.** Parentheses group a sequence into one tactic, so a macro can
expand to several steps.

| Before | After `intro_omega` |
|---|---|
| `a : Nat ⊢ a = 3 → a + 1 = 4` | no goals |

---

## Traps

- Only the macro line is yours. The theorems, `by crush` included, are frozen: you cannot add per-theorem
  proofs, so one expansion must close all three goals.
- Order the alternatives of `first` so each one either **closes** its goal or **fails**. An alternative that
  succeeds but leaves a goal (e.g. `simp` that only simplifies, or `constructor` alone) stops `first`, and
  `by crush` ends with unsolved goals.
- Hygiene (R7): `exact ⟨hp, hq⟩` inside the macro does not refer to `t3`'s `hp`, `hq`. Use a tactic that
  searches the context.
- `t₁ ; t₂` inside a quotation needs parentheses, `(t₁; t₂)` (W3); `first | a | b` needs none.
- The bans remove one-word tactics that close all three goals alone (`grind`, `trivial`, `solve_by_elim`,
  `exact?`, `apply?`, `try?`): the point is to combine tactics.
- The `sorry` warning appears at `t1`, `t2`, `t3`, not at the macro, because that is where the expansion
  runs.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| close a computing equation | `rfl` | R1 |
| close linear `Nat`/`Int` arithmetic | `omega` | R2 |
| close from hypotheses | `simp_all`, or `constructor <;> assumption` for `∧` | R3, W1 |
| try alternatives in order | `first \| t₁ \| t₂ \| t₃` | R4 |
| name a tactic script | `` macro "name" : tactic => `(tactic\| tac) `` | R5 |
| several expansions, newest tried first | `syntax "name" : tactic` + `` macro_rules \| `(tactic\| name) => `(tactic\| tac) `` | R6 |
| use a hypothesis inside a macro | a searching tactic (`assumption`, `simp_all`), never its name | R7 |
| several steps in one expansion | `` `(tactic\| (t₁; t₂)) `` | W3 |
| see the state | infoview | |
