# E044 · gcongr: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `exact`, `exacts`, `∧` and its projections `h.1`, `h.2`,
`<;>`.
**New here:** Mathlib's real numbers `ℝ`; the tactic `gcongr`, which proves `f a ≤ f b` (or `<`) by
reducing it to inequalities between the parts that differ; the tactic `positivity`, which `gcongr` runs on
its side goals.

## How to read an entry

Each entry is one call of a tactic on one goal shape. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `gcongr` closes every goal it can from the context (R3). So that an entry can show the goals it
  produces, the entry's hypothesis is packed into a conjunction `h : A ∧ B`, which `gcongr` does not look
  inside. `exact h.1` then finishes the example. In the exercise the hypotheses are separate, and
  `gcongr` uses them directly.
- Placeholders are written as Lean binders: `(a b c : ℝ)` are reals, `(n : ℕ)` a natural number.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`). Numerals such as `3 : ℝ` are reals too |
| `a ^ 2` | power with a natural-number exponent: `a ^ 2 = a * a` |
| `3 / y` | real division. Lean defines `x / 0 = 0`, so facts about `/` need `0 < y` somewhere |
| `a ≤ b`, `a < b` | order on `ℝ` or `ℕ`; `y > x` is notation for `x < y` |
| `case h₁`, `case hab`, `case h`, … | a goal `gcongr` produced for a differing position (a **main goal**) |
| `case ha`, `case hc`, `case c0`, `case b0`, … | a condition the monotonicity lemma needs (a **side goal**, usually `0 ≤ _` or `0 < _`) |
| `no goals` | `gcongr` closed everything from the context |

The case names come from the hypothesis names of the Mathlib lemma `gcongr` applied. They carry no meaning
beyond "main" or "side"; read the goal itself.

## How `gcongr` works

`gcongr` ("generalized congruence") takes a goal `lhs ≤ rhs` or `lhs < rhs` whose two sides have the **same
shape** and differ only in some positions. It peels the shared shape off one layer at a time, using the
monotonicity lemmas Mathlib tags `@[gcongr]` (adding the same `c` preserves `≤`; `t ↦ t ^ n` is monotone
on `t ≥ 0`; `t ↦ k / t` is antitone on `t > 0`). It stops at the differing positions. Then:

1. every **main goal** (the differing parts, compared in the right direction) and every **side goal** is
   tried against the hypotheses in context (R3);
2. side goals are also tried with `positivity` (R6);
3. whatever is still open is left to you, in order.

---

## Part 1 · `add_mono_sq`

Statement: from `a ≤ b` and `0 ≤ a`, conclude `a ^ 2 + c ≤ b ^ 2 + c`. Two layers differ: the outer `+ c`
is shared (R1), the inner `_ ^ 2` is shared (R2), and at the bottom `a` faces `b`.

**R1 · `gcongr` on a shared summand** changes the **goal**: `_ + c` (or `c + _`) on both sides is dropped.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a + c ≤ b + c` | `⊢ a ≤ b` |
| `⊢ c + a ≤ c + b` | `⊢ a ≤ b` |

**R2 · `gcongr` on a shared power** changes the **goal list**: `a ^ n ≤ b ^ n` becomes the side goal
`0 ≤ a` and the main goal `a ≤ b`. The side goal is needed because `t ↦ t ^ n` is monotone only on `t ≥ 0`:
`-2 ≤ 1` but `(-2) ^ 2 > 1 ^ 2`. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `h : 0 ≤ a ∧ a ≤ b ⊢ a ^ n ≤ b ^ n` | `⊢ 0 ≤ a`, `⊢ a ≤ b` |

**R3 · `gcongr` closing goals from the context** changes the **goal list**: each produced goal that a
hypothesis proves is closed. A strict `h : a < b` also proves a non-strict `a ≤ b`. Placeholders:
`(a b : ℝ) (n : ℕ)`. With `ha : 0 ≤ a` and `h : a < b` in context, R2's two goals both disappear:

| Before | After |
|---|---|
| `ha : 0 ≤ a, h : a < b ⊢ a ^ n ≤ b ^ n` | no goals |

In `add_mono_sq` all of R1, R2, R3 happen inside one `gcongr` call.

## Part 2 · `cube_mono`

Statement: from `0 ≤ x` and `x ≤ y`, conclude `x ^ 3 ≤ y ^ 3`. One shared layer, `_ ^ 3`: R2 with `n = 3`.
Its side goal `0 ≤ x` and main goal `x ≤ y` are both hypotheses (R3).

## Part 3 · `mul_mono_nat`

Statement: in `ℕ`, from `a ≤ b` and `c ≤ d`, conclude `a * c + 5 ≤ b * d + 5`. The outer `+ 5` is shared
(R1); under it, `a * c` faces `b * d` and **both** factors differ (R4).

**R4 · `gcongr` on a product in `ℕ`** changes the **goal list**: one main goal per differing factor.
Multiplication preserves `≤` only for non-negative factors, but in `ℕ` every number is `≥ 0`, so those side
goals are closed automatically. In `ℝ` they stay (W2). Placeholders: `(a b c d : ℕ)`.

| Before | After |
|---|---|
| `h : a ≤ b ∧ c ≤ d ⊢ a * c ≤ b * d` | `⊢ a ≤ b`, `⊢ c ≤ d` |

**W2 · the same shape in `ℝ`.** With `h1 : a ≤ b` and `h2 : c ≤ d` in context the main goals close (R3),
but two side goals are left:

```lean-goal
⊢ 0 ≤ c
⊢ 0 ≤ b
```

## Part 4 · `recip_anti`

Statement: from `0 < x` and `x < y`, conclude `3 / y < 3 / x`. The numerator `3` is shared and the
denominators differ, **in the opposite order**: a larger denominator gives a smaller quotient.

**R5 · `gcongr` on a shared numerator** changes the **goal list**: `k / y < k / x` becomes the side goals
`0 < k`, `0 < x` and the main goal `x < y`. Note the flip: the goal has `y` on the left, the main goal has
`x` on the left. Placeholders: `(k x y : ℝ)`.

| Before | After |
|---|---|
| `h : 0 < k ∧ 0 < x ∧ x < y ⊢ k / y < k / x` | `⊢ 0 < k`, `⊢ 0 < x`, `⊢ x < y` |

**R6 · `positivity`** changes the **goal list**: it closes a goal `0 < e` or `0 ≤ e` by looking at the shape of `e`: positive numerals,
squares, sums and products of non-negative things. It does not read hypotheses, so it cannot prove `0 < x`
for a variable `x`. `gcongr` runs it on every side goal, which is why with a numeral numerator such as `3`
the side goal `0 < 3` never appears. Examples it closes: `(0 : ℝ) < 2`, `0 < x ^ 2 + 1`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < x ^ 2 + 1` | no goals |

**W4.** `1 / y < 1 / x` from `hx : 0 < x` and `h : x < y`: R5 produces `0 < 1`, `0 < x`, `x < y`; R6 closes
the first, R3 the other two.

---

## Traps

- The main goal must be as strict as the goal. `gcongr` on `2 * x + 1 < 2 * y + 1` leaves `x < y`; a
  hypothesis `x ≤ y` cannot close it (W3 shows the strict version that works).
- Division flips the direction (R5): for `k / y < k / x` you need `x < y`, not `y < x`.
- Side goals about **variables** (`0 ≤ a`, `0 < x`) are not proved by `positivity`. They must be in the
  context, or you prove them after `gcongr`, in the order the goals appear.
- `gcongr` matches the two sides position by position. On `a ^ 2 + c ≤ c + b ^ 2` it pairs `a ^ 2` with `c`
  and `c` with `b ^ 2`, leaving two unprovable goals `a ^ 2 ≤ c` and `c ≤ b ^ 2`. Put both sides in the
  same order first (for example with `rw [add_comm]`).
- `gcongr` leaving goals is not failure: read the infoview and close them with `exact`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a + c ≤ b + c` from `a ≤ b` | `gcongr` | R1 |
| `a ^ n ≤ b ^ n` from `0 ≤ a`, `a ≤ b` | `gcongr` (side goal `0 ≤ a`) | R2 |
| goals that are already hypotheses | closed by `gcongr` itself | R3 |
| `a * c ≤ b * d` in `ℕ` from `a ≤ b`, `c ≤ d` | `gcongr` | R4 |
| `a * c ≤ b * d` in `ℝ` | `gcongr`, plus `0 ≤ c`, `0 ≤ b` | W2 |
| `k / y < k / x` from `0 < k`, `0 < x`, `x < y` | `gcongr` (main goal flipped) | R5 |
| `0 < e` / `0 ≤ e` for a numeral or a square | `positivity` | R6 |
| leftover goals after `gcongr` | `exact h`, `exacts [h₁, h₂]` | |
| see the state | infoview | |
