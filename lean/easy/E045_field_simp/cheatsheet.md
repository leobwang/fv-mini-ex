# E045 · field_simp: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular tactic mode, `have` (E021) and the two
directions `.mp`/`.mpr` of an `↔` (E005); `ring` (E034) and `linarith` (E035).
**New here:** division in a Mathlib **field** and the tactic `field_simp`. A field (`[Field α]`) is a
commutative ring in which every `b ≠ 0` has an inverse `b⁻¹`, and `a / b` means `a * b⁻¹`; `ℚ`, `ℝ`, `ℂ` are
fields. Lean makes `/` a total function by setting `b⁻¹ = 0` at `b = 0`, so `a / 0 = 0`. Hence
`a * b / b = a` is false at `b = 0`, and every cancellation needs a proof of `b ≠ 0`.
`field_simp` multiplies out every denominator `d` for which it can prove `d ≠ 0` (from hypotheses in the
context, from numerals such as `2 ≠ 0`, and by simple rewriting such as `x ≠ 1 ⇒ x - 1 ≠ 0`). It then either
closes the goal or leaves an equation with no `/`, which you finish with `ring` or `linarith`. Also new:
the lemma `sub_ne_zero`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter. "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : Prop`, or `P : α → Prop`). A hypothesis `hP` only finishes the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field α]` is a
  requirement on `α` (a *type class*); Lean shows it in the context as `inst✝ : Field α`. Each entry says
  which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means | Type it as |
|---|---|---|
| `ℝ` | the real numbers, a field | `\R` |
| `a / b` | `a * b⁻¹`; equals `0` when `b = 0` | `/` |
| `b ≠ 0` | `¬ (b = 0)`, i.e. `b = 0 → False` | `\ne` |
| `x ^ 2` | `x * x`; the exponent is a natural number | `^` |
| `3` in `a / b = 3` | the real number `3` (a numeral takes the type of the other side) | `3` |
| `inst✝ : Field α` | the instance from `[Field α]`: `α` is a field | |
| `inst✝ : AddGroup α` | `α` has `+`, `-`, `0` with the group laws (every field does) | |
| `b * 3` after `field_simp` | `field_simp` picks its own order of factors; `b * 3` and `3 * b` are different terms | |

---

## Part 1 · `cancel_x`

Statement: for `x : ℝ` with `hx : x ≠ 0`, `(x ^ 2 + x) / x = x + 1`. The only denominator is `x`, and its
side condition `hx` is already in the context. `field_simp` multiplies through by `x` and finishes the
resulting polynomial identity itself (R1).

**R1 · `field_simp`** **closes** the goal: it cancels the denominator `b` using `hb : b ≠ 0` from the
context. Placeholders: `{α : Type} [Field α] (a b : α) (hb : b ≠ 0)`. `[Field α]`: `ℚ`, `ℝ`, `ℂ` qualify.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a * b / b = a` | no goals |

## Part 2 · `diff_of_squares`

Statement: for `x : ℝ` with `hx : x ≠ 1`, `(x ^ 2 - 1) / (x - 1) = x + 1`. The denominator is `x - 1`, but
the context says `x ≠ 1`. State the side condition in the form `field_simp` uses, `x - 1 ≠ 0` (R2). Then
`field_simp` clears the denominator and leaves a polynomial identity (R3), which `ring` closes (R4).

**R2 · `have h : a - b ≠ 0 := sub_ne_zero.mpr hab`** changes the **context**: it adds `h`. The lemma is
`sub_ne_zero : a - b ≠ 0 ↔ a ≠ b`, and `.mpr` uses it right to left: from `a ≠ b` it gives `a - b ≠ 0`.
Placeholders: `{α : Type} [AddGroup α] (a b : α) (hab : a ≠ b)`; every field qualifies.

| Before | After |
|---|---|
| `hab : a ≠ b ⊢ P` | `hab : a ≠ b, h : a - b ≠ 0 ⊢ P` |

**R3 · `field_simp`** changes the **goal**: it multiplies both sides by the denominator `b` (given
`hb : b ≠ 0`) and leaves an equation with no `/`. Placeholders: `{α : Type} [Field α] (a b c : α) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a / b = c` | `hb : b ≠ 0 ⊢ a = b * c` |

**R4 · `ring`** **closes** an identity of commutative rings (E034). Placeholders: `{α : Type} [Field α] (a b : α)`;
every field is a commutative ring.

| Before | After |
|---|---|
| `⊢ (a + b) * (a - b) = a ^ 2 - b ^ 2` | no goals |

**W1 · R2, then R1** on `a / (b - c) * (b - c) = a` with `hbc : b ≠ c`:

| Before | After `have h : b - c ≠ 0 := sub_ne_zero.mpr hbc` | After `field_simp` |
|---|---|---|
| `hbc : b ≠ c ⊢ a / (b - c) * (b - c) = a` | `h : b - c ≠ 0 ⊢ a / (b - c) * (b - c) = a` | no goals |

**W2 · R3, then R4** on adding fractions, with `ha : a ≠ 0`, `hb : b ≠ 0`. `field_simp` cross-multiplies and
cancels the common `a * b`; what is left is a ring identity:

| Before | After `field_simp` | After `ring` |
|---|---|---|
| `⊢ 1 / a + 1 / b = (a + b) / (a * b)` | `⊢ b + a = a + b` | no goals |

## Part 3 · `from_ratio`

Statement: for `a b : ℝ` with `hb : b ≠ 0` and `h : a / b = 3`, `a = 3 * b`. Here the division is in the
**hypothesis**, not the goal: clear it there (R5). Then `h` is a linear equation and the goal follows from it
(R6).

**R5 · `field_simp at h`** changes the **context**: the hypothesis `h` is rewritten with its denominator
cleared; the goal is unchanged. Placeholders: `{α : Type} [Field α] (a b c : α) (hb : b ≠ 0) (h : a / b = c)`.

| Before | After |
|---|---|
| `h : a / b = c ⊢ P a` | `h : a = b * c ⊢ P a` |

**R6 · `linarith`** **closes** a goal that follows from the hypotheses by adding up linear (in)equalities
(E035). `b * 5` is linear (a numeral times a variable, in either order). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a = b * 5 ⊢ a = 5 * b` | no goals |

**W3 · R5, then R6** on `h : (a + 1) / b = 2`, `hb : b ≠ 0`:

| Before | After `field_simp at h` | After `linarith` |
|---|---|---|
| `h : (a + 1) / b = 2 ⊢ a = 2 * b - 1` | `h : a + 1 = b * 2 ⊢ a = 2 * b - 1` | no goals |

---

## Traps

- No side condition, no cancellation: with no hypothesis about `x` at all, `field_simp` leaves
  `(x ^ 2 - 1) / (x - 1)` untouched and does not report an error. Find each denominator's side condition
  before calling it.
- In this Mathlib version `field_simp` derives `d ≠ 0` from simple forms by itself: `x ≠ 1`, `1 ≠ x` and
  `0 < x` all work for the denominators `x - 1` and `x`. So `diff_of_squares` passes even without R2. The
  explicit `have h : d ≠ 0 := …` (R2) still makes the side condition visible, and it is the fix whenever
  `field_simp` leaves a `/` in place.
- `field_simp` chooses the order of factors: after R5 the hypothesis reads `a = b * 3`, so `exact h` does
  not close `a = 3 * b`. Finish with `linarith` (or `rw [h]; ring`).
- `field_simp` on a goal that it can close (R1) leaves nothing; a `ring` after it then fails with
  "no goals". Check the infoview after each tactic.
- `field_simp at h` rewrites only `h`; `field_simp` alone rewrites only the goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| cancel a denominator `d` in the goal, `d ≠ 0` in context | `field_simp` | R1, R3 |
| get `a - b ≠ 0` from `a ≠ b` | `have h : a - b ≠ 0 := sub_ne_zero.mpr hab` | R2 |
| polynomial identity left after `field_simp` | `ring` | R4 |
| clear a denominator in hypothesis `h` | `field_simp at h` | R5 |
| goal follows linearly from hypotheses | `linarith` | R6 |
| `d - e` denominator with only `d ≠ e` known | R2, then `field_simp` | W1 |
| sum of fractions | `field_simp`, then `ring` | W2 |
| ratio given in a hypothesis | `field_simp at h`, then `linarith` | W3 |
| see the state | infoview (cursor after a tactic) | |
