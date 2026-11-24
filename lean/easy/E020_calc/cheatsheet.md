# E020 · calc: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E019, in particular `exact` (E003), `rw` (E009) and `omega` (E011).
**New here:** `calc`, which writes a proof as a chain `a R₁ b R₂ c …` of steps, each with its own
proof, the way one writes a derivation on paper; how `=`, `≤` and `<` combine along a chain; and the
core distributivity lemmas `Nat.add_mul` and `Nat.mul_add`.

## How to read an entry

Each entry is one tactic, one `calc` form or one lemma. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter, separated by `, `.
- `x y z w : Nat` are arbitrary natural numbers. `P : Nat → Prop` is "the rest of the goal": the step
  changes only the part inside `P (…)`, wherever it sits in a larger goal.
- A hypothesis `h` only finishes the example. "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `calc a R b := p` | the first step: `p` proves `a R b` (`R` is `=`, `≤` or `<`) |
| `_ R c := q` | a later step: `_` is the previous step's right side, so `q` proves `b R c` |
| `x > y`, `x ≥ y` | notation for `y < x`, `y ≤ x` |
| `x < y` on `Nat` | `x + 1 ≤ y` (this is how `omega` reads it) |
| `x * y` | a product of two variables: one unknown ("atom") for `omega` |
| `case calc_1`, `case calc_2`, … | the goals left by steps proved with `?_`, in chain order (R3) |
| `case calc.step` | the goal `calc` adds when the chain ends short of the goal's right side (Traps) |
| `failed to synthesize Trans instance` | two steps whose relations do not combine (e.g. `<` then `>`) |

---

## Part 1 · `calc_lt`

Statement: from `a < b`, `b ≤ c` and `c < d`, conclude `a < d`. One `calc` chain from `a` to `d`, one step
per hypothesis, each step proved by that hypothesis (R1, R2).

**R1 · `calc` with `=` steps** **closes** the goal. Each line is `lhs R rhs := proof`. The first line names
its left side; every later line starts with `_`, the previous right side. The first left side and the last
right side must be the goal's two sides. A step's proof is any term (a hypothesis, `rfl`) or a `by` block.
`calc` is also a term: after `theorem t … :=` you may write `calc …` directly, without `by`.
Placeholders: `(x y z : Nat) (h1 : x = y) (h2 : y = z)`.

| Before | After |
|---|---|
| `h1 : x = y, h2 : y = z ⊢ x = z` | no goals |

**R2 · `calc` mixing `≤` and `<`** **closes** a goal `x < z`. The chain's relation is `<` as soon as one step
is `<`, `≤` when every step is `≤`, and an `=` step keeps the other relation. Lean combines consecutive steps
with a `Trans` instance (a rule "`R₁` then `R₂` gives `R₃`"); core Lean has them for `=`, `≤`, `<` on `Nat`.
Placeholders: `(x y z : Nat) (h1 : x ≤ y) (h2 : y < z)`.

| Before | After |
|---|---|
| `h1 : x ≤ y, h2 : y < z ⊢ x < z` | no goals |

**W1** (R1, R2) as a term: `h1 : x = y`, `h2 : y ≤ z`, `h3 : z < w`, `h4 : w ≤ v` give `x < v` with the
chain `calc x = y := h1` / `_ ≤ z := h2` / `_ < w := h3` / `_ ≤ v := h4`.

## Part 2 · `calc_sq`

Statement: if `a = b + c` and `c = b`, then `a * a = 4 * (b * b)`. Three `=` steps (R1): substitute
(R4) to reach `(b + b) * (b + b)`, expand the product (R5 → R6), collect the `b * b` terms (R7). R3 shows the
goal each step's `by` block starts from.

**R3 · a step proved by `?_`** changes the **goal list**: `?_` postpones that step, and after the `calc` the
step is a goal of its own. It is exactly the goal a `by` block written in that step would start from.
It needs tactic mode: write `:= by calc …` (a term-mode `calc` rejects `?_`, see Traps). With several `?_`
steps the new goals are tagged `case calc_1`, `case calc_2`, … in chain order.
Placeholders: `(x y z : Nat) (h1 : x = y) (h2 : y = z)`.

| Before | After |
|---|---|
| `h1 : x = y ⊢ x = z` | `h1 : x = y ⊢ x = y` |

**R4 · `rw [h1, h2]`** changes the **goal**: the rewrites run left to right, so `h2` sees the result of
`h1`. With `h1 : x = y + z`, `x` becomes `y + z`; then `h2 : z = y` finds a `z`. After the last rewrite
`rw` tries `rfl`, so an equation whose two sides became identical is closed at once. Placeholders:
`(P : Nat → Prop) (x y z : Nat) (h1 : x = y + z) (h2 : z = y)`.

| Before | After `rw [h1]` | After `rw [h2]` |
|---|---|---|
| `⊢ P x` | `⊢ P (y + z)` | `⊢ P (y + y)` |

**R5 · `rw [Nat.add_mul]`** changes the **goal**. The lemma is `Nat.add_mul (n m k : Nat) : (n + m) * k = n * k
+ m * k` (distribute a right factor). Placeholders: `(P : Nat → Prop) (x y z : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((x + y) * z)` | `⊢ P (x * z + y * z)` |

**R6 · `rw [Nat.mul_add]`** changes the **goal**. The lemma is `Nat.mul_add (n m k : Nat) : n * (m + k) = n * m
+ n * k` (distribute a left factor). Placeholders: `(P : Nat → Prop) (x y z : Nat)`.

| Before | After |
|---|---|
| `⊢ P (x * (y + z))` | `⊢ P (x * y + x * z)` |

`rw` rewrites the **first** match of the left side, and every other copy of that same instance, but no
other instance. **W2** on `(q + 1) * (q + 1)`:

| Step | State |
|---|---|
| start | `⊢ (q + 1) * (q + 1) = q * q + q * 1 + 1 * (q + 1)` |
| `rw [Nat.add_mul]` | `⊢ q * (q + 1) + 1 * (q + 1) = q * q + q * 1 + 1 * (q + 1)` |
| `rw [Nat.mul_add]` | no goals (`q * (q + 1)` expanded, `1 * (q + 1)` left alone, then `rfl`) |

**R7 · `omega` with products** **closes** a goal that is linear once each product of variables is read as one
unknown (an *atom*). Atoms are compared as written: `x * y` and `y * x` are two unrelated unknowns, and
`(x + y) * (x + y)` is a single opaque atom, so `omega` cannot expand it (that is R5/R6's job). Placeholders:
`(x y : Nat)`.

| Before | After |
|---|---|
| `⊢ x * y + x * y + x * y = 3 * (x * y)` | no goals |

**W3** (R1, R4, R5, R6, R7): from `h1 : p = q + 1`, prove `p * p = q * q + 2 * q + 1` with the three steps
`p * p = (q + 1) * (q + 1)` by `rw [h1]`, `_ = q * q + q * 1 + 1 * (q + 1)` by `rw [Nat.add_mul, Nat.mul_add]`,
`_ = q * q + 2 * q + 1` by `omega` (`q * 1` and `1 * (q + 1)` are multiplications by a numeral: linear).

---

## Traps

- The first left side must be the goal's left side, literally up to computation: `calc y = …` on a goal
  `x = z` fails with "invalid 'calc' step, left-hand side is y … expected to be x".
- If the chain proves a weaker or shorter statement than the goal, tactic-mode `calc` does not fail at once:
  a chain of two `≤` steps on a goal `x < z` leaves `case calc.step ⊢ z < z`, which is unprovable. Make
  one step `<`.
- Write chains in one direction. `x < y` then `_ > z` has no `Trans` instance ("failed to synthesize
  `Trans` instance"). A hypothesis `h : z > y` *can* prove a step `_ < z`, since `z > y` is `y < z`.
- `omega` before expanding: `(b + b) * (b + b) = 4 * (b * b)` fails, because the left side is one atom.
  Expand with R5, R6 first.
- `?_` as a step proof works only in tactic-mode `calc` (`:= by calc …`). After `theorem … :=` a bare
  `calc` is a term, and `?_` there fails with "don't know how to synthesize placeholder".
- `rw [h2, h1]` (wrong order) fails when the goal has no `c` yet: `rw` errors when the pattern is absent.
- `grind` is banned in this exercise.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a chain of equalities | `calc a = b := p` / `_ = c := q` | R1 |
| a chain mixing `≤`, `<`, `=` | same layout; result is `<` if any step is `<` | R2 |
| see the goal of one step | `_ = c := ?_` (or `by` + infoview) | R3 |
| substitute variables in order | `rw [h1, h2]` | R4 |
| `(n + m) * k → n * k + m * k` | `rw [Nat.add_mul]` | R5 |
| `n * (m + k) → n * m + n * k` | `rw [Nat.mul_add]` | R6 |
| linear arithmetic over product atoms | `omega` | R7 |
| see the state | infoview (cursor after a tactic) | |
