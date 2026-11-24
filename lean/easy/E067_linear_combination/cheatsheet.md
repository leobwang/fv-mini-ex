# E067 · linear_combination: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): hypotheses, `exact`, equations `a = b`.
**New here:** Mathlib's real numbers `ℝ` and complex numbers `ℂ`; the tactic `linear_combination`, which
proves an equation from a combination of hypotheses you name; the tactic `ring` it calls; the type classes
`CommRing`, `Field`, `CharZero` the entries are stated for.

## How to read an entry

Each entry is one tactic call or one form of coefficient. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter; no entry
  changes them.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

**The idea.** Read an equation `l = r` as the claim "`l - r` is `0`". Proofs of equations combine like those
expressions: for `h₁ : l₁ = r₁`, `h₂ : l₂ = r₂` and terms `c₁, c₂`, the expression `c₁ * h₁ + c₂ * h₂` stands
for the equation `c₁ * l₁ + c₂ * l₂ = c₁ * r₁ + c₂ * r₂`; `-`, `/ c` and `c * h` work the same way. For a goal
`a = b`, `linear_combination e` (with `e` standing for `l = r`) proves the goal if

$$ (a - b) - (l - r) = 0 $$

holds as a polynomial identity, which it hands to `ring`. Your job is to find the coefficients: write the
goal's difference `a - b` as a sum of multiples of the hypotheses' differences `lᵢ - rᵢ`.

**`ring`** (TACTIC_STATES, "Closing") proves an equation that holds in every commutative ring by expanding
both sides into polynomials. It uses no hypotheses. In a field of characteristic 0 (`ℝ`, `ℂ`) it also
handles division by numerals: `a / 2 + a / 2 = a`.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | `Real`, Mathlib's real numbers |
| `ℂ` | `Complex`, Mathlib's complex numbers. `ℂ` has no order `≤`, so `linarith` cannot work there |
| `5`, `-1`, `1 / 2` in `ℝ` or `ℂ` | numerals of that type; `1 / 2` is real division, not `ℕ` division |
| `a ^ 2` | `a * a`; the exponent is a natural number |
| `inst✝ : CommRing α` | an unnamed type-class hypothesis, from a bracket `[CommRing α]` |
| `CommRing α` | `α` has `+`, `-`, `*`, `0`, `1` with the usual laws, `*` commutative (`ℤ`, `ℝ`, `ℂ`) |
| `Field α` | a `CommRing` with division `/` by nonzero elements (`ℚ`, `ℝ`, `ℂ`; not `ℤ`) |
| `CharZero α` | `1 + 1 + ⋯ + 1 ≠ 0`, so numerals such as `2` are nonzero (`ℝ`, `ℂ`) |
| a goal such as `2 - y = 0` under `ring failed` | the leftover `(a - b) - (l - r)` after `ring` normalised it; it is `0` only for the right coefficients |
| `case a` | the label of the goal `linear_combination (norm := skip)` leaves; ignore it |
| `a + r - (b + l) = 0` | the identity `linear_combination` checks: `(a - b) - (l - r) = 0` rearranged (R2) |

---

## Part 1 · `lc_linear`

Statement: over `ℝ`, from `x + y = 5` and `x - y = 1`, conclude `x = 3`. The goal's difference is `x - 3`;
the hypotheses' differences are `x + y - 5` and `x - y - 1`.

**R1 · `linear_combination h`** changes the **goal list**: it closes the goal `a = b` when `a - b` equals
`l - r` by `ring` (`h : l = r`), and fails with "ring failed" otherwise. Placeholders:
`{α : Type} [CommRing α] (a b c : α)`, `(h : a + c = b)`. Here `a - (b - c)` and `(a + c) - b` are the same
polynomial, so the coefficient is 1.

| Before | After |
|---|---|
| `h : a + c = b ⊢ a = b - c` | no goals |

**R2 · `linear_combination (norm := skip) e`** changes the **goal**: it does not call `ring`, and leaves the
identity it would check. For a goal `a = b` and `e` standing for `l = r` that identity is printed as
`a + r - (b + l) = 0`. Finish with `ring`. Use it to see why a coefficient choice fails; remove
`(norm := skip)` and the `ring` in the final proof. Placeholders: as R1.

| Before | After `linear_combination (norm := skip) h` |
|---|---|
| `h : a + c = b ⊢ a = b - c` | `⊢ a + b - (b - c + (a + c)) = 0` |

**R3 · `h₁ + h₂`** (a coefficient form, written after `linear_combination`) changes the **goal** it checks:
it adds two equations, `l₁ + l₂ = r₁ + r₂`; `h₁ - h₂` subtracts them.
Placeholders: `{α : Type} [CommRing α] (a b c d : α)`, `(h₁ : a + b = c) (h₂ : a - b = d)`. The `b` cancels:
`(a + b - c) + (a - b - d) = 2 * a - (c + d)`.

| Before | After `linear_combination (norm := skip) h₁ + h₂` |
|---|---|
| `⊢ 2 * a = c + d` | `⊢ 2 * a + (c + d) - (c + d + (a + b + (a - b))) = 0` |

**R4 · `e / 2`** (a coefficient form) changes the **goal** it checks: it divides an equation by a numeral,
`l / 2 = r / 2`. Placeholders:
`{α : Type} [Field α] [CharZero α] (a c : α)`, `(h : 2 * a = c)`. `Field` gives `/`, `CharZero` gives
`2 ≠ 0`, so `ring` can simplify `2 * a / 2` to `a`; `ℝ` and `ℂ` qualify. Parenthesize a sum before dividing:
`(h₁ + h₂) / 2`, since `h₁ + h₂ / 2` halves only `h₂`.

| Before | After `linear_combination (norm := skip) h / 2` |
|---|---|
| `h : 2 * a = c ⊢ a = c / 2` | `⊢ a + c / 2 - (c / 2 + 2 * a / 2) = 0` |

**W1: a linear system over `ℝ`** (not the exercise's). From `2x + y = 7` and `x - y = -1`, conclude `x = 2`:
`(2x + y - 7) + (x - y + 1) = 3x - 6 = 3 (x - 2)`, so the combination is `(h₁ + h₂) / 3` (R3, then R4):

```lean-goal
⊢ x = 2
⊢ x + (7 + -1) / 3 - (2 + (2 * x + y + (x - y)) / 3) = 0
```

---

## Part 2 · `lc_square`

Statement: over `ℝ`, from `a + b = 3` and `a * b = 2`, conclude `a ^ 2 + b ^ 2 = 5`. The goal is quadratic,
the first hypothesis linear: you need a coefficient that is itself a term.

**R5 · `t * h`** (a coefficient form) changes the **goal** it checks: it multiplies an equation by any
expression `t`, `t * l = t * r`.
Placeholders: `{α : Type} [CommRing α] (a b : α)`, `(h : a = b)`. To find `t`, factor the goal's difference
by the hypothesis' difference: `a ^ 2 - b ^ 2 = (a + b) * (a - b)`, so `t = a + b`.

| Before | After `linear_combination (norm := skip) (a + b) * h` |
|---|---|
| `h : a = b ⊢ a ^ 2 = b ^ 2` | `⊢ a ^ 2 + (a + b) * b - (b ^ 2 + (a + b) * a) = 0` |

**R6 · `h₁ - t * h₂`** (a coefficient form) changes the **goal** it checks: it subtracts a multiple of a
second equation to cancel what the first leaves over. Placeholders: `{α : Type} [CommRing α] (a b c d : α)`, `(h₁ : a * b = c) (h₂ : a = d)`. With
`h₁` alone the leftover is `d * b - a * b = -b * (a - d)`, and `b * h₂` stands for `b * a = b * d`.

| Before | After `linear_combination (norm := skip) h₁ - b * h₂` |
|---|---|
| `⊢ d * b = c` | `⊢ d * b + (c + b * a) - (c + (a * b + b * d)) = 0` |

**W2: a quadratic identity** (not the exercise's). From `a - b = 1` and `a * b = 6`, conclude
`a ^ 2 + b ^ 2 = 13`. Split the goal's difference into a square part and a product part:
`a² + b² - 13 = ((a - b)² - 1) + 2 (a b - 6)`, and `(a - b)² - 1 = (a - b + 1)(a - b - 1)`. So the
combination is `(a - b + 1) * h + 2 * h₂` (R5, R3).

```lean-goal
⊢ a ^ 2 + b ^ 2 = 13
```

---

## Part 3 · `lc_complex`

Statement: over `ℂ`, from `x * y = 1` and `x = 2`, conclude `y = 1 / 2`. `ℂ` has no `≤`, so `linarith` does
not apply; `linear_combination` needs only a field. The goal's difference is `y - 1 / 2`.

No new entries: halve the first hypothesis (R4), then cancel the leftover with a term multiple of the second
(R6, whose `t` is a term as in R5). Trying the first half alone shows the leftover in `ring`'s normal form
(see Traps):

```
error: ring failed, ring expressions not equal
⊢ y + y * x * (-1 / 2) = 0
```

Read it as `y - (y / 2) * x`: find `t` with `t * (x - 2)` equal to it, and subtract `t * h2`.

**W3: over `ℂ`** (not the exercise's). From `z * w = 3` and `w = 3`, conclude `z = 1`. `h₁ / 3` stands for
`z w / 3 = 1`, which leaves `z - z w / 3 = -(z / 3)(w - 3)` over; subtract `z / 3 * h₂`. The combination is
`h₁ / 3 - z / 3 * h₂`.

```lean-goal
⊢ z = 1
```

---

## Traps

- `ring` alone is allowed but cannot use hypotheses; `linear_combination` is how they enter. `ring` on the
  goal `x = 3` fails, since `x = 3` is not a polynomial identity.
- A wrong coefficient fails with `ring failed`, and the goal shown is the **leftover** in normal form, which
  tells you what is still missing. With only `h1` in Part 1:
  ```
  error: ring failed, ring expressions not equal
  ⊢ 2 - y = 0
  ```
  `y` is left over, so add a multiple of the hypothesis that contains `-y`. Likewise `linear_combination h`
  on `a ^ 2 = b ^ 2` leaves `-a + a ^ 2 + b - b ^ 2 = 0`: the coefficient must be a term (R5), not `1`.
- `h₁ + h₂ / 2` is `h₁ + (h₂ / 2)`. Write `(h₁ + h₂) / 2`.
- `linarith` is banned here and fails on `ℂ` anyway: `ℂ` has no `≤`, so it finds no usable facts
  (`linarith failed to find a contradiction`).
- When `ring` fails (for example after R2 with wrong coefficients) Lean suggests `Try this: ring_nf`.
  `ring_nf` is banned here; fix the coefficients instead.
- This exercise bans `rw`, `subst`, `simp`, `norm_num`, `field_simp`, `ring_nf` and `linarith`: do not
  substitute `x = 2` into the goal; put `h2` into the combination with a coefficient instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| goal `a = b` from `h : l = r` with `a - b ≡ l - r` | `linear_combination h` | R1 |
| see the identity it checks | `linear_combination (norm := skip) e`, then `ring` | R2 |
| add / subtract equations | `h₁ + h₂` / `h₁ - h₂` | R3 |
| divide an equation by a numeral (`ℝ`, `ℂ`) | `e / 2`, `(h₁ + h₂) / 2` | R4 |
| multiply an equation by a term | `(a + b) * h`, `y / 2 * h` | R5 |
| cancel a leftover with a second equation | `h₁ - t * h₂` | R6 |
| check the arithmetic: `(a - b) - Σ cᵢ (lᵢ - rᵢ) = 0` | by hand, or R2 | R2 |
| see the state | infoview | |
