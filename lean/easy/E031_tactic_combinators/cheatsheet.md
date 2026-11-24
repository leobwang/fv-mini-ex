# E031 · Tactic combinators: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E030, in particular `decide` (E001), `exact`/`assumption` (E003), `∧` and
`constructor` (E005), `rcases` on `∨` (E006), `simp` (E010), `omega` (E011) and `have` (E021).
**New here:** *tactic combinators*, tactics that take other tactics as arguments and decide which goals
they run on: `t <;> u`, `all_goals u`, `first | t | u`, `try t`; plus `refine` with `?_` holes to create
several goals at once, and a case split on the finitely many values a variable can take (the `rfl`
pattern of `rcases`, R10).

The proof state holds a **goal list** `G₁ | G₂ | …`; an ordinary tactic works on the first goal only.
A combinator is **one step**: the infoview shows the state before it and after it, never in between.
Part W of the guide unrolls the chains into single steps.

## How to read an entry

Each entry is one tactic or combinator. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P Q : α → Prop` are "the rest of your goal"; `A B C T G : Prop` are arbitrary propositions.
- "no goals" means the step closed every goal it ran on. A list `⊢ A`, `⊢ B` in one cell is a goal list.
- A hypothesis whose statement contains a comma (`h : ∀ (x : α), P x`) is shown in its own code span
  next to the state.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `A ∧ B ∧ C` | `A ∧ (B ∧ C)`: `∧` nests to the right, so Lean drops those parentheses |
| `(P a ∧ P b) ∧ P c ∧ P d` | how Lean prints `(P a ∧ P b) ∧ (P c ∧ P d)` |
| `case refine_1`, `case refine_2`, … | the goals made by the `?_` holes of `refine`, in order |
| `case left`, `case right` | the two goals of `constructor` on `∧`; nested: `left.left`, `left.right`, … |
| `case inl`, `case inr.inl`, `case inr.inr` | the three goals of `rcases` on `X ∨ Y ∨ Z` |
| `this` | the name of a fact added by `have` without a name |
| `n * n` | a product of two variables: outside `omega`'s fragment (linear arithmetic) |

---

## Part 1 · `three_goals`

Statement: from `h : a = b` (natural numbers), prove `a + 0 = b ∧ 0 + a = b ∧ a * 1 = b`. Three goals
of the same kind: split them (R1), then one `simp [h]` (R3) on all of them (R2 or R4).

**R1 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: one goal becomes three. `∧` nests to the right
and the anonymous constructor flattens the nesting, so write one `?_` per conjunct. Each `?_` becomes a new
goal; a plain `_` must be filled by Lean itself and fails here. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C` | `⊢ A`, `⊢ B`, `⊢ C` |

**R2 · `t <;> u`** changes the **goal list**: run `t`, then `u` on *every* goal that `t` produced. All
or nothing: if `u` fails on one of them, the whole step fails. Goals that `u` leaves open stay open.
Placeholders: `{α : Type} (P : α → Prop) (a b : α)`, with `h : ∀ (x : α), P x` closing each goal.

| Before | After `constructor <;> exact h _` |
|---|---|
| `⊢ P a ∧ P b` | no goals |

**R3 · `simp [h]`** with `h : a = b` changes the **goal**: `simp` rewrites with its built-in lemmas
(`Nat.add_zero : n + 0 = n`, `Nat.zero_add : 0 + n = n`, `Nat.mul_one : n * 1 = n`, …) and with `h`, left
to right, and closes the goal when it reaches `True` (for example `b = b`). Placeholders:
`(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : a = b ⊢ P (0 + a * 1)` | `h : a = b ⊢ P b` |

**R4 · `all_goals u`** changes the **goal list**: run `u` on every goal open at that point (not only those
of the previous tactic). Also all or nothing. Use it on its own line, where `<;>` would need one long line.
Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After `constructor` | After `all_goals assumption` |
|---|---|---|
| `ha : A, hb : B ⊢ A ∧ B` | `⊢ A`, `⊢ B` | no goals |

**W1** (R1, then R3 on all goals with R4) on lists: from `h : xs = ys`, prove
`xs ++ [] = ys ∧ [] ++ xs = ys ∧ xs.reverse.reverse = ys`.

| Step | State |
|---|---|
| start | `h : xs = ys ⊢ xs ++ [] = ys ∧ [] ++ xs = ys ∧ xs.reverse.reverse = ys` |
| `refine ⟨?_, ?_, ?_⟩` | `⊢ xs ++ [] = ys`, `⊢ [] ++ xs = ys`, `⊢ xs.reverse.reverse = ys` |
| `all_goals simp [h]` | no goals |

## Part 2 · `nested_and`

Statement: from `hp : p`, `hq : q`, `hr : r`, prove `(p ∧ q) ∧ (r ∧ p)`. Two levels of `∧`, so two
splits (R5, chained with R6), then four goals each closed by some hypothesis (R7).

**R5 · `constructor`** changes the **goal list**: it splits only the **outermost** `∧`. The inner `∧`
needs another `constructor`. Placeholders: `(A B C : Prop) (hab : A ∧ B) (hc : C)`.

| Before | After |
|---|---|
| `⊢ (A ∧ B) ∧ C` | `⊢ A ∧ B`, `⊢ C` |

**R6 · `t <;> u <;> v`** changes the **goal list**: it reads `(t <;> u) <;> v`, so `v` runs on every goal
left after `u` ran on every goal of `t`. Placeholders: `{α : Type} (P : α → Prop) (a b c d : α)`, with
`h : ∀ (x : α), P x`.

| Before | After `constructor <;> constructor <;> exact h _` |
|---|---|
| `⊢ (P a ∧ P b) ∧ P c ∧ P d` | no goals |

**R7 · `assumption`** **closes** the goal when some hypothesis has exactly that type. It searches the whole
context, so the same tactic closes goals that need *different* hypotheses: the one to put after `<;>`.
Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After `constructor` | After `· assumption` (first goal) |
|---|---|---|
| `ha : A, hb : B ⊢ A ∧ B` | `⊢ A`, `⊢ B` | `ha : A, hb : B ⊢ B` |

**W2** unrolls `constructor <;> constructor <;> decide` into single steps (R5, R4, R11):

| Step | State |
|---|---|
| start | `⊢ (0 < 1 ∧ 1 < 2) ∧ 2 < 3 ∧ 3 < 4` |
| `constructor` | `⊢ 0 < 1 ∧ 1 < 2`, `⊢ 2 < 3 ∧ 3 < 4` |
| `all_goals constructor` | `⊢ 0 < 1`, `⊢ 1 < 2`, `⊢ 2 < 3`, `⊢ 3 < 4` |
| `all_goals decide` | no goals |

## Part 3 · `small_square`

Statement: from `h : n < 3`, prove `n * n < 9`. `omega` handles linear arithmetic only, and `n * n` is a
product of two variables. But `n < 3` leaves three values: prove `n = 0 ∨ n = 1 ∨ n = 2` with `omega`
(R8, R9), substitute each value (R10), and compute every case (R11, via R2 or R4).

**R8 · `have : T := by tac`** changes the **context**: it adds the fact under the name `this`; the goal
stays. Placeholders: `(T G : Prop)`. Indent a multi-line `by` block further than `have`.

| Before | After |
|---|---|
| `t : T ⊢ G` | `this : T ⊢ G` |

**R9 · `omega`** **closes** a disjunction of linear facts that follows from the linear hypotheses. Here
`5 ≤ n < 8` leaves three values. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `h1 : 5 ≤ n, h2 : n < 8 ⊢ n = 5 ∨ n = 6 ∨ n = 7` | no goals |

**R10 · `rcases h with rfl | rfl | rfl`** changes the **goal list and the context**: one goal per disjunct
(the pattern `p₁ | p₂ | p₃` splits the right-nested `∨` all at once), and in each the pattern `rfl`
substitutes the value for `n`: `n` leaves the context, and every hypothesis and the goal that mentioned `n`
now mention the number. Placeholders: `(n : Nat) (Q : Nat → Prop) (hq : Q n)`.

| Before | After |
|---|---|
| `hq : Q n, h : n = 5 ∨ n = 6 ∨ n = 7 ⊢ Q n` | `hq : Q 5 ⊢ Q 5`, `hq : Q 6 ⊢ Q 6`, `hq : Q 7 ⊢ Q 7` |

**R11 · `decide`** **closes** a statement about concrete numbers by evaluating it (E001).

| Before | After |
|---|---|
| `⊢ 7 * 7 < 50` | no goals |

**W3** (R8 with R9, R10, then R11 on both goals) on `h : n < 2 ⊢ n * n = n`:

| Step | State |
|---|---|
| start | `h : n < 2 ⊢ n * n = n` |
| `have : n = 0 ∨ n = 1 := by omega` | `this : n = 0 ∨ n = 1 ⊢ n * n = n` |
| `rcases this with rfl \| rfl` | `h : 0 < 2 ⊢ 0 * 0 = 0`, `h : 1 < 2 ⊢ 1 * 1 = 1` |
| `all_goals decide` | no goals |

---

## When the goals need different tactics

Not needed for the exercise, but the natural next step when `<;>` meets goals of different kinds.

**R12 · `first | t | u`** changes the **goal list**: on each goal, try `t`; if it fails, try `u`. After
`<;>` it chooses separately per goal. Put it last in a chain or in parentheses, `(first | t | u)`.
Placeholders: `(A : Prop) (a : Nat) (ha : A)`.

| Before | After `constructor <;> first \| assumption \| omega` |
|---|---|
| `ha : A ⊢ A ∧ a ≤ a + 1` | no goals |

**R13 · `try t`** changes the **goal list**: run `t`; if it fails, do nothing. It never fails, so it keeps
`<;>` from failing when `t` applies to some goals only. Placeholders: `(A B C : Prop)`.

| Before | After `constructor <;> try constructor` |
|---|---|
| `⊢ (A ∧ B) ∧ C` | `⊢ A`, `⊢ B`, `⊢ C` |

(`constructor` splits `A ∧ B` and fails on `C`; without `try`, the whole step would fail.)

---

## Traps

- `t ; u` (or `u` on the next line) runs `u` on the **first** goal only. After a split, use `<;>` or
  `all_goals` (TACTIC_STATES, "Structure").
- `t <;> u` is all or nothing: `u` must succeed on every goal `t` makes. Wrap `u` in `try` (R13) or
  `first` (R12) when it fits only some of them.
- `constructor` splits one level only (R5). For `(p ∧ q) ∧ (r ∧ p)` you need it twice.
- `refine ⟨_, _⟩` with plain `_` asks Lean to guess the proofs and fails; holes that become goals are
  `?_` (R1).
- `omega` fails on `n * n < 9`: the product of two variables is outside linear arithmetic. List the
  values first (R8, R9, R10). `decide` alone also fails: `n` is a variable, not a number.
- After `rcases … with rfl | …`, `n` is gone and `h : n < 3` reads `h : 0 < 3` etc. (W3).
- `first | t | u <;> v` parses as `first | t | (u <;> v)`; write `(first | t | u) <;> v`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B ∧ C` into three goals | `refine ⟨?_, ?_, ?_⟩` | R1 |
| run `u` on every goal of `t` | `t <;> u` | R2 |
| simplify with a hypothesis `h : a = b` | `simp [h]` | R3 |
| run `u` on every open goal | `all_goals u` | R4 |
| split the outermost `∧` | `constructor` | R5 |
| split two levels, then close all | `constructor <;> constructor <;> u` | R6 |
| close a goal that is a hypothesis | `assumption` | R7 |
| add a fact named `this` | `have : T := by tac` | R8 |
| finitely many values from bounds | `omega` proves `n = 0 ∨ n = 1 ∨ …` | R9 |
| substitute each value | `rcases this with rfl \| rfl \| rfl` | R10 |
| compute a concrete statement | `decide` | R11 |
| different closers per goal | `t <;> first \| u \| v` | R12 |
| `u` only where it applies | `t <;> try u` | R13 |
| see the state | infoview | |
