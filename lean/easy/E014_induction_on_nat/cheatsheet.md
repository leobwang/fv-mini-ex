# E014 · Induction on Nat: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E013: `rfl`, `exact`, `simp only [f]` / `simp [f]` (E010), `omega` (E011),
definitions by pattern matching on `0` and `n + 1`. **New here:** proof by induction on a natural number
(`induction n with | zero => … | succ k ih => …`), unfolding a recursive definition one step in the `succ`
case, and the distributive laws `Nat.add_mul`, `Nat.mul_add` to expand products before `omega`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Natural numbers and their induction principle

A value of `Nat` is either `0` or `k + 1` (the successor of some `k : Nat`), and every natural number is
reached from `0` by finitely many `+ 1`. So to prove `P n` for every `n : Nat` it suffices to prove

- `P 0` (case `zero`), and
- `P (k + 1)` for every `k`, assuming `ih : P k` (case `succ`; `ih` is the induction hypothesis).

A function defined by matching on `0` and `n + 1` (`dbl`, `sumOdd`) computes only when its argument
literally has one of those two shapes. After `induction n` the argument is `0` or `k + 1`, so one step of the
definition applies; what remains mentions `f k`, which is exactly what `ih` talks about.

## Reading the goals

| You see | It means |
|---|---|
| `case zero`, `case succ` | the two goals made by `induction n` (R1) |
| `k + 1` | the successor of `k` (the constructor `Nat.succ k`, displayed as `k + 1`) |
| `ih : P k` | the induction hypothesis: the statement for `k` |
| `k + 1 + 1` | `(k + 1) + 1`: `+` groups to the left |
| `∀ (k : Nat), P k → P (k + 1)` | how Lean prints `∀ k, P k → P (k + 1)` with the type filled in |
| `k * 1`, `1 * k` | left as they are by `simp only` unless you give it `Nat.mul_one` / `Nat.one_mul`; `omega` reads them as `k` |

---

## Part 1 · `dbl_eq`

Statement: `dbl n = 2 * n`, where `dbl 0 = 0` and `dbl (n + 1) = dbl n + 2`. Induct on `n`. Case `zero`:
`dbl 0` and `2 * 0` both compute to `0`. Case `succ`: unfold `dbl (k + 1)` to `dbl k + 2`, replace `dbl k` by
`2 * k` with `ih`, and the rest is linear arithmetic.

**R1 · `induction n with | zero => ?_ | succ k ih => ?_`** changes the **goal list and the context**: one goal
becomes the `zero` goal and the `succ` goal. In the `succ` goal, `n` is gone and the context gains `k : Nat`
and `ih : P k`. In the exercise write the tactics directly after each `=>`:
`induction n with | zero => tac₀ | succ k ih => tac₁`. You may reuse the name `n` instead of `k`. Placeholders:
`(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `k : Nat, ih : P k ⊢ P (k + 1)` |

**R2 · `rfl`** **closes** a goal whose two sides compute to the same term. With no variables left (case
`zero`), both sides are closed terms: `trip 0` computes to `0` by the first equation of `trip`, and `3 * 0`
to `0`. `decide` works too.

| Before | After |
|---|---|
| `⊢ trip 0 = 3 * 0` | no goals |

**R3 · `simp only [f]`** changes the **goal**: every `f 0` and `f (k + 1)` is replaced by the right side of
`f`'s matching equation. Here `trip (n + 1) = trip n + 3`. `rw [trip]` does the same for the first match.
`trip k` with unknown `k` is not unfolded. Placeholders: `(k : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (trip (k + 1))` | `⊢ P (trip k + 3)` |

**R4 · `simp only [ih]`** changes the **goal**: wherever the left side of `ih` appears literally, it is
replaced by the right side. Here `ih : trip k = 3 * k`. Combine with R3 in one call: `simp only [trip, ih]`
unfolds first and then rewrites. Placeholders: `(k : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `ih : trip k = 3 * k ⊢ P (trip k + 3)` | `⊢ P (3 * k + 3)` |

**R7 · `omega`** (shown in Part 2) **closes** what is left: `2 * k + 2 = 2 * (k + 1)` is linear, since one
factor of each product is a literal.

---

## Part 2 · `sumOdd_eq`

Statement: `sumOdd n = n * n`, where `sumOdd 0 = 0` and `sumOdd (n + 1) = sumOdd n + (2 * n + 1)`: the sum of
the first `n` odd numbers is `n²`. Induct on `n` (R1); case `zero` is R2. In case `succ`, after unfolding (R3)
and `ih` (R4) the left side is `k * k + (2 * k + 1)` and the right side is `(k + 1) * (k + 1)`. That product
of two non-literals is one opaque atom for `omega`, unrelated to the atom `k * k`, so `omega` fails. Expand it
first with R5 and R6; then both sides are linear in `k` and the single atom `k * k`.

**R5 · `Nat.add_mul`** changes the **goal**. The lemma is `Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c`
(distribute a sum on the left of `*`). Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R6 · `Nat.mul_add`** changes the **goal**. The lemma is `Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c`
(distribute a sum on the right of `*`). Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

Inside `simp only [f, ih, Nat.add_mul, Nat.mul_add]` both lemmas are applied left to right, repeatedly, until
no product has a sum as a factor: `(k + 1) * (k + 1)` becomes `k * k + 1 * k + (k * 1 + 1 * 1)` (the first three summands of the right side in W1).

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `=`, `<`, `≤`).
Any other term counts as one unknown number: here `k * k` is the same atom on both sides. `k * 1` and `1 * k`
count as `k`. Placeholders: `(k : Nat)`.

| Before | After |
|---|---|
| `⊢ k * k + k * 1 + (1 * k + 1) = k * k + 2 * k + 1` | no goals |

**W1 (on `tri`, `tri (n + 1) = tri n + (n + 1)`):** `2 * tri n = n * (n + 1)` by R1, R2 for `zero`, then one
`simp only [tri, Nat.mul_add, Nat.add_mul, ih]` (R3, R6, R5, R4) and R7:

| Before `simp only` | After `simp only` |
|---|---|
| `ih : 2 * tri k = k * (k + 1) ⊢ 2 * tri (k + 1) = (k + 1) * (k + 1 + 1)` | `⊢ k * k + k * 1 + (2 * k + 2 * 1) = k * k + 1 * k + (k * 1 + 1 * 1) + (k * 1 + 1 * 1)` |

Note that `ih` fires only after `Nat.mul_add` has split `2 * (tri k + (k + 1))` into `2 * tri k + …`: the
left side `2 * tri k` of `ih` must appear literally. `ih`'s right side `k * (k + 1)` is then expanded too.
`omega` closes the result.

---

## Traps

- `omega` cannot multiply two unknowns. It treats `(k + 1) * (k + 1)` as one atom and `k * k` as another,
  unrelated one, so it fails on `k * k + (2 * k + 1) = (k + 1) * (k + 1)`. Expand with R5, R6 first.
- `ih` is about `k`, not `k + 1`: unfold the definition (R3) before `ih` can match.
- `simp only [f, ih]` without the distributive lemmas may leave `ih` unused (W1: `2 * (tri k + (k + 1))` does
  not contain `2 * tri k` literally). The linter then warns "This simp argument is unused".
- If `simp only` already closes the goal, a following `omega` fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `P n` for every `n : Nat` | `induction n with \| zero => … \| succ k ih => …` | R1 |
| `zero` case with no variables | `rfl` (or `decide`) | R2 |
| unfold `f (k + 1)` one step | `simp only [f]` (or `rw [f]`) | R3 |
| use the induction hypothesis | `simp only [f, ih]` | R4 |
| `(a + b) * c → a * c + b * c` | `Nat.add_mul` | R5 |
| `a * (b + c) → a * b + a * c` | `Nat.mul_add` | R6 |
| linear arithmetic, `k * k` as an atom | `omega` | R7 |
| see the state | infoview | |
