# E068 · nlinarith with hints: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have` (E021), `exact`, implicit arguments (E023).
**New here:** Mathlib's real numbers `ℝ` with `≤`, `<`, `^`; the decision procedures `linarith` and
`nlinarith`; three lemmas that build nonnegativity proofs (`add_nonneg`, `sq_nonneg`, `mul_nonneg`) used as
hints.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P : Prop` is "the rest of your goal". A hypothesis `g` in an example only finishes it: it shows what the
  context became.
- Placeholders are written as Lean binders: `(u v : ℝ)` are real numbers, `(hu : 0 ≤ u)` a proof that `u` is
  nonnegative. The lemmas hold in any ordered ring (`ℤ`, `ℚ`, `ℝ`); the guide states them over `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (an ordered field) |
| `a ^ 2` | `a * a`: `^` with a natural-number exponent (`Monoid.npow`), not a real power |
| `2 * a * b` | `(2 * a) * b`: `*` groups to the left; numerals such as `2` are real numbers here |
| `0 ≤ (a - b) ^ 2` | the type of `sq_nonneg (a - b)`: a proof term, usable as a hint |
| `a✝ : y < x` | in an error message: the negated goal that `linarith`/`nlinarith` assumed (`a✝` is an unnamed hypothesis) |
| goal `False` | in an error message: the contradiction `linarith` tried and failed to derive |
| `linarith failed to find a contradiction` | no nonnegative combination of the listed facts gives `0 < 0`: add (better) hints |

### How `nlinarith` works (the model to keep in mind)

To prove `L ≤ R`, `nlinarith` assumes the negation `R < L` and collects a list of facts `pᵢ ≥ 0` / `pᵢ > 0`:
the hypotheses, the negated goal and your hints. It adds the product of every **pair** of facts and `0 ≤ e ^ 2` for each square `e ^ 2` / `e * e` appearing in
them, expands every
term into monomials (`x ^ 2 * y`, `x * y`, …) and then `linarith` treats each monomial as an unknown and
searches for nonnegative coefficients `cᵢ` with `Σ cᵢ pᵢ` identically equal to a negative constant (a
contradiction). So a proof exists when `R - L` is a nonnegative combination of the facts and their pairwise
products. Recipe for hints: write `R - L` as a sum of terms `(nonnegative factor) × (square)` and pass one
proof term per summand.

---

## Part 1 · `nl_sq`

Statement: for reals `a, b` with `0 ≤ b` and `a ^ 2 ≤ b ^ 2`, `a ≤ b`. No hint needed: the products of the
hypotheses with the negated goal `b < a` already give the certificate.

**R1 · `linarith`** **closes** a goal that follows **linearly** from the hypotheses. It negates the goal and
finds nonnegative coefficients that sum the facts to `0 < 0` (here `1·h1 + 2·h2 + 1·(6 < x)`). Nonlinear
monomials are unknowns to it: it does not know `x ^ 2 ≥ 0` or relate `x ^ 2` to `x`. Placeholders:
`(x y : ℝ) (h1 : x ≤ 2 * y) (h2 : y ≤ 3)`.

| Before | After |
|---|---|
| `h1 : x ≤ 2 * y, h2 : y ≤ 3 ⊢ x ≤ 6` | no goals |

**R2 · `nlinarith`** **closes** a polynomial (in)equality over an ordered field. It negates the goal, multiplies
every pair of facts in its list (and adds `0 ≤ e ^ 2` for each square `e ^ 2` or `e * e` it sees), then runs R1 on the expanded result. In the example the
products `0 ≤ x * (y - x)` (from `hx`, `hxy`) and `0 ≤ (y - x) ^ 2` (from `hxy` twice) give
`y ^ 2 - x ^ 2 = (y - x) ^ 2 + 2 * x * (y - x) ≥ 0`. Placeholders: `(x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x, hxy : x ≤ y ⊢ x ^ 2 ≤ y ^ 2` | no goals |

---

## Part 2 · `nl_sym`

Statement: for `x, y ≥ 0`, `x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 + y ^ 3`. Plain `nlinarith` fails (degree 3; the
needed product has three factors). Factor `rhs - lhs = (x + y) * (x - y) ^ 2` (check it with `ring`, W1) and
pass the proof of `0 ≤ (x + y) * (x - y) ^ 2`, built from R3, R4, R5.

**R3 · `add_nonneg`** changes the **context** (used with `have`). Statement:
`add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b`, with `{a b}` implicit (read off the two proofs). Placeholders:
`(u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (P : Prop)`.

| Before | After `have h := add_nonneg hu hv` |
|---|---|
| `⊢ P` | `h : 0 ≤ u + v ⊢ P` |

**R4 · `sq_nonneg`** changes the **context**. Statement: `sq_nonneg (a : α) : 0 ≤ a ^ 2`, with `a` **explicit**:
you pass the expression to square, any expression. Placeholders: `(u v : ℝ) (P : Prop)`.

| Before | After `have h := sq_nonneg (u - v)` |
|---|---|
| `⊢ P` | `h : 0 ≤ (u - v) ^ 2 ⊢ P` |

**R5 · `mul_nonneg`** changes the **context**. Statement: `mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`, `{a b}`
implicit. Its arguments may be terms themselves: `mul_nonneg (add_nonneg hu hv) (sq_nonneg w)` proves
`0 ≤ (u + v) * w ^ 2`. Placeholders: `(u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (P : Prop)`.

| Before | After `have h := mul_nonneg hu hv` |
|---|---|
| `⊢ P` | `h : 0 ≤ u * v ⊢ P` |

**R6 · `nlinarith [t₁, …, tₙ]`** **closes** the goal with the proof terms `tᵢ` added to the fact list of R2
(they also enter the pairwise products). Each `tᵢ` is a **proof**, not a statement. Placeholders: `(a b : ℝ)`;
here `(a + b) ^ 2 - 4 * a * b = (a - b) ^ 2`.

| Before | After `nlinarith [sq_nonneg (a - b)]` |
|---|---|
| `⊢ 4 * a * b ≤ (a + b) ^ 2` | no goals |

### Worked combinations (W1–W3, not the exercise's inequalities)

**W1: check a factorisation with `ring`** (TACTIC_STATES, "Closing"). `ring` closes

```lean-goal
⊢ x ^ 3 + x * y ^ 2 - 2 * x ^ 2 * y = x * (x - y) ^ 2
```

**W2: factor × square.** With `hx : 0 ≤ x`, `nlinarith [mul_nonneg hx (sq_nonneg (x - y))]` (R4 in R5, R6)
closes the goal below. `y` needs no sign: only the factor outside the square does.

```lean-goal
⊢ 2 * x ^ 2 * y ≤ x ^ 3 + x * y ^ 2
```

**W3: the factor is a sum.** `rhs - lhs = (u + v) * (z - 1) ^ 2`, so
`nlinarith [mul_nonneg (add_nonneg hu hv) (sq_nonneg (z - 1))]` (R3 and R4 in R5, R6) closes

```lean-goal
⊢ 2 * z * (u + v) ≤ (u + v) * (z ^ 2 + 1)
```

---

## Part 3 · `nl_three`

Statement: `a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2` for all reals. Plain `nlinarith` fails: with no
hypotheses its list holds only the negated goal and `0 ≤ a ^ 2`, `0 ≤ b ^ 2`, `0 ≤ c ^ 2` (the squares it
sees), and the squares of differences are missing. Use
`2 * (rhs - lhs) = (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2`: one `sq_nonneg` hint (R4) per square, then R6.
The factor `2` does not matter: `linarith` picks the coefficients.

**W4: a sum of squares, one hint per square.** `a ^ 2 + b ^ 2 + 2 - 2 * (a + b) = (a - 1) ^ 2 + (b - 1) ^ 2`,
so `nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]` closes

```lean-goal
⊢ 2 * (a + b) ≤ a ^ 2 + b ^ 2 + 2
```

**W5: hints in the context instead.** `have h1 := sq_nonneg (a - 1)` and `have h2 := sq_nonneg (b - 1)`
(R4), then plain `nlinarith` (R2) reads them as hypotheses:

| Before | After both `have`s |
|---|---|
| `⊢ 2 * (a + b) ≤ a ^ 2 + b ^ 2 + 2` | `h1 : 0 ≤ (a - 1) ^ 2, h2 : 0 ≤ (b - 1) ^ 2 ⊢ 2 * (a + b) ≤ a ^ 2 + b ^ 2 + 2` |

---

## Traps

- A hint is a **proof term**: `nlinarith [sq_nonneg (a - b)]`, not `nlinarith [0 ≤ (a - b) ^ 2]`. The latter is a
  statement, not a proof: no error points at it, it is simply useless, and you get `linarith failed to find a
  contradiction`.
- `nlinarith` multiplies only **pairs**. A certificate needing a product of three facts (like
  `(x + y) * (x - y) ^ 2`) must be handed over whole, built with `mul_nonneg`.
- `mul_nonneg` needs **both** factors nonnegative: for `0 ≤ (x + y) * (x - y) ^ 2` the first argument is a
  proof of `0 ≤ x + y` (from `hx`, `hy` by `add_nonneg`), the second `sq_nonneg (x - y)`.
- `sq_nonneg` takes the expression, `mul_nonneg`/`add_nonneg` take proofs: `sq_nonneg (x - y)` but
  `add_nonneg hx hy`.
- When `nlinarith` fails, the message lists its context: the line `a✝ : … < …` is the negated goal. Compute
  `rhs - lhs` by hand and factor it; `ring` checks the factorisation (W1).
- Several shortcuts (`gcongr`, `polyrith`, the `pow_le_pow_…`/`le_of_sq_le_sq` lemmas, `exact?`) are BANNED in
  this exercise: the point is to find the hints yourself.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| linear goal from hypotheses | `linarith` | R1 |
| polynomial goal, hypotheses suffice | `nlinarith` | R2 |
| `0 ≤ a + b` from `ha`, `hb` | `add_nonneg ha hb` | R3 |
| `0 ≤ e ^ 2` for any `e` | `sq_nonneg e` | R4 |
| `0 ≤ a * b` from `ha`, `hb` | `mul_nonneg ha hb` | R5 |
| polynomial goal with hints | `nlinarith [t₁, t₂]` | R6 |
| find the hints | factor `rhs - lhs` into `Σ (factor ≥ 0) * (square)` | W1–W4 |
| check a factorisation | `ring` | W1 |
| `0 ≤ c * e ^ 2` with `hc : 0 ≤ c` | `mul_nonneg hc (sq_nonneg e)` | W2 |
| `0 ≤ (u + v) * e ^ 2` | `mul_nonneg (add_nonneg hu hv) (sq_nonneg e)` | W3 |
| hints as hypotheses | `have h := sq_nonneg e`, then `nlinarith` | W5 |
| see the state | infoview | |
