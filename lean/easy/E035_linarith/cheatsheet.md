# E035 · linarith: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular tactic mode, `have` and `exact`; E034
(`import Mathlib`, the number types `ℕ ℤ ℚ ℝ`, `ring`).
**New here:** the tactic `linarith` and the lemma `sq_nonneg`. `linarith` proves a goal `s < t`, `s ≤ t`,
`s = t` (also `≥`, `>`, or `False`) that is a **linear** consequence of the hypotheses `s = t`, `s ≤ t`,
`s < t` in the context, over an **ordered field** such as `ℚ` or `ℝ`. *Linear*: each side is a sum of
unknowns times numerals plus a numeral. Method: it adds the negated goal (`¬ (s < t)` is `t ≤ s`) to the
hypotheses and searches for nonnegative rational coefficients `cᵢ` such that `Σ cᵢ · (hypᵢ)` is `0 < 0` or
`0 ≤ c` with `c < 0`, a contradiction. It closes the goal or fails with "linarith failed to find a
contradiction"; it never leaves a changed goal.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter. "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : Prop`); `g` only finishes the example.
- Placeholders are Lean binders. `{α : Type}` is any type. The brackets
  `[Field α] [LinearOrder α] [IsStrictOrderedRing α]` together say "`α` is an ordered field": `+ - * /`
  with the field laws (`Field`), a total order `≤` (`LinearOrder`), and the order respects `+` and `*` by
  positives (`IsStrictOrderedRing`). `ℚ` and `ℝ` qualify. Lean shows them in the context as
  `inst✝² : Field α`, `inst✝¹ : LinearOrder α`, `inst✝ : IsStrictOrderedRing α`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `x y : ℝ` | real numbers (`\R`); an ordered field |
| `x < y`, `x ≤ y` | strict and non-strict order (`\le` types `≤`) |
| `a ≥ b`, `a > b` | `b ≤ a`, `b < a`; `linarith` reads both forms |
| `2 * c - a` | `(2 * c) - a`: `*` binds tighter than `-`; numeral times unknown, linear |
| `y / 2` | `y` divided by the numeral `2`, linear (coefficient `1/2`) |
| `x ^ 2` | `x * x`; exponent a natural-number numeral. Not linear: `linarith` treats it as one unknown |
| `4 * x * y` | `(4 * x) * y`: `*` groups to the left; the monomial `x * y` with coefficient `4` |
| `-(2 * a * b)` | negation; `s - -t` is how Lean prints `s - (-t)` |
| `sq_nonneg e` | a **proof** of `0 ≤ e ^ 2`, not a statement |
| `inst✝ : IsStrictOrderedRing α` | the instance from a bracket `[IsStrictOrderedRing α]` |
| `a✝ : (x + y) ^ 2 < 4 * x * y` in an error | when `linarith` fails it prints its state: `a✝` (an unnamed hypothesis) is the negated goal it added, and the goal is `False` |

---

## Part 1 · `solve_two`

Statement: for `x y : ℝ` with `h1 : x + y = 10` and `h2 : x - y = 2`, `x = 6`. Adding the equations gives
`2x = 12`. Both hypotheses are linear equations, so `linarith` finds the combination itself (R1).

**R1 · `linarith` with an `=` goal** **closes** the goal. `linarith` collects the context hypotheses
itself; you never name them. An `=` goal becomes two goals `≤` and `≥`, each proved as below. Placeholders:
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α)`.

| Before | After |
|---|---|
| `h1 : 2 * a + b = 7, h2 : b = 3 ⊢ a = 2` | no goals |

## Part 2 · `chain_pos`

Statement: for `a b c : ℝ` with `h1 : a < b`, `h2 : b ≤ c`, `h3 : 0 < a`, `0 < 2 * c - a`. A chain of
`<` and `≤` (R2) and a numeral coefficient in the goal (R3); everything is linear, one `linarith`. To see why
it holds: `2c - a ≥ 2b - a > 2a - a = a > 0`.

**R2 · `linarith` with a `<` goal** **closes** the goal from a chain of `<` and `≤`. Negated goal `c ≤ a`,
plus `h1`, plus `h2`, sums to `a < a`. One strict step anywhere makes the conclusion strict.
Placeholders: `(a b c : α)` in an ordered field `α`.

| Before | After |
|---|---|
| `h1 : a < b, h2 : b ≤ c ⊢ a < c` | no goals |

**R3 · `linarith` with numeral coefficients and `-`** **closes** the goal. Hypotheses are scaled by
positive rationals (here `1 · h1 + 2 · h2`); coefficients `/ 2` are fine. Placeholders: `(a b : α)`.

| Before | After |
|---|---|
| `h1 : 0 ≤ a, h2 : a < b ⊢ 0 < 3 * b - (a + b)` | no goals |

**W4 · several steps, a coefficient `/ 2`:** `x ≤ y / 2 < z / 2 ≤ z`.

| Before | After |
|---|---|
| `h1 : x ≤ y / 2, h2 : y < z, h3 : 0 ≤ z ⊢ x < z` | no goals |

## Part 3 · `sq_bound`

Statement: for `x y : ℝ`, `4 * x * y ≤ (x + y) ^ 2`. This is **not** linear and there are no hypotheses, so
`linarith` alone fails. After expanding (R6) it is linear in the monomials `x ^ 2`, `x * y`, `y ^ 2`; what is
missing is one fact about them. `(x + y) ^ 2 - 4 * x * y` is a perfect square; compute it (W1), then add
`0 ≤ (that square)` with `sq_nonneg` (R4) inside `linarith [ ]` (R5).

**R4 · `sq_nonneg`** changes the **context** when used in `have`. The lemma is
`sq_nonneg (a : α) : 0 ≤ a ^ 2`, for `α` an ordered ring such as `ℤ`, `ℚ`, `ℝ` (its own brackets are longer;
an ordered field meets them). The argument is explicit: pass any expression to be squared.
Placeholders: `(a b : α)`.

| Before | After `have h := sq_nonneg (a - b)` |
|---|---|
| `g : 0 ≤ (a - b) ^ 2 → P ⊢ P` | `h : 0 ≤ (a - b) ^ 2 ⊢ P` |

**R5 · `linarith [t]`** **closes** the goal, using the fact proved by `t` as if it were a hypothesis. The
context is not changed. `t` must be a proof term (`sq_nonneg c`), not a statement (`0 ≤ c ^ 2`). Several
terms: `linarith [t₁, t₂]`. Placeholders: `(a b c : α)`.

| Before | After `linarith [sq_nonneg c]` |
|---|---|
| `h : a ≤ b ⊢ a ≤ b + c ^ 2` | no goals |

**R6 · `linarith` multiplies out products** and **closes** the goal. Before searching, it expands every
product and power of sums into monomials (`a ^ 2`, `a * b`, `a`, `1`) and treats each monomial as one
unknown; `a * b` and `b * a` are the same monomial. So `h : 0 ≤ (a - 1) ^ 2` is read as
`0 ≤ a ^ 2 - 2 * a + 1`, and the goal below is linear in the unknowns `a ^ 2` and `a`. Placeholders: `(a : α)`.

| Before | After |
|---|---|
| `h : 0 ≤ (a - 1) ^ 2 ⊢ 2 * a ≤ a ^ 2 + 1` | no goals |

**W1 · finding the square.** Write `rhs - lhs`, guess the square, check the guess with `ring` (E034: it
**closes** an equation that holds in every commutative ring, by multiplying out both sides). For
`-(2 * a * b) ≤ a ^ 2 + b ^ 2`:

| Before | After `ring` |
|---|---|
| `⊢ a ^ 2 + b ^ 2 - -(2 * a * b) = (a + b) ^ 2` | no goals |

**W2 · the square as a hint** (R4 inside R5, expanded as in R6):

| Before | After `linarith [sq_nonneg (a + b)]` |
|---|---|
| `⊢ -(2 * a * b) ≤ a ^ 2 + b ^ 2` | no goals |

**W3 · the same, with the fact put in the context first** (R4, then R6):

| Before | After `have h := sq_nonneg (a + b)` | After `linarith` |
|---|---|---|
| `⊢ -(2 * a * b) ≤ a ^ 2 + b ^ 2` | `h : 0 ≤ (a + b) ^ 2 ⊢ -(2 * a * b) ≤ a ^ 2 + b ^ 2` | no goals |

---

## Traps

- `linarith` never multiplies two hypotheses together or squares anything by itself. If the goal needs a
  nonlinear fact (`0 ≤ s ^ 2`, `0 ≤ a * b`), give it as a hint (R5) or use `nlinarith` (E068), which tries
  products of pairs.
- A hint is a proof term: `linarith [sq_nonneg (x - y)]`, not `linarith [0 ≤ (x - y) ^ 2]`.
- `linarith` does not use `≠` hypotheses: `h : x ≠ y` with `x ≤ y` does not give `x < y`. (A `≠` *goal* is
  fine: for `x ≠ y` it assumes `x = y` and looks for a contradiction, so `h : x < y` closes it.)
- Monomials are opaque: `linarith` knows nothing relating `x ^ 2` and `x`, or `x * y` and `x`, beyond what the
  hypotheses and hints say. Division by a variable, `√x`, function applications are opaque unknowns too.
- It is complete only over ordered fields (`ℚ`, `ℝ`). On `ℕ` and `ℤ` it runs but can miss proofs that need
  integrality (`2 * x = 7 → False`), and `ℕ` subtraction truncates: use `omega` (E011) there.
- `linarith` proves comparisons only. For an identity with no hypotheses, `ring` (E034) is the tool.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `=` goal from linear equations in the context | `linarith` | R1 |
| `<` / `≤` goal from a chain of `<`, `≤` | `linarith` | R2, W4 |
| numeral coefficients, `-`, `/ 2` | `linarith` | R3 |
| the fact `0 ≤ e ^ 2` | `sq_nonneg e` (a proof term) | R4 |
| put it in the context | `have h := sq_nonneg e` | R4 |
| use extra facts without `have` | `linarith [t₁, t₂]` | R5 |
| nonlinear goal, linear in the monomials | add the right square, `linarith` expands it | R6, W2, W3 |
| find the square | compute `rhs - lhs`, check with `ring` | W1 |
| needs products of hypotheses | `nlinarith` (E068) | |
| linear facts on `ℕ`/`ℤ` | `omega` (E011) | |
| see the state | infoview (cursor after a tactic) | |
