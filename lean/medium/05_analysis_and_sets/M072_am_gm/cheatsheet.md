# M072 · AM-GM for two reals: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the square
root `Real.sqrt`, and the arithmetic automation `nlinarith` and `positivity`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
gives the lemma's statement, lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`). Numerals such as `2` in a real goal are reals |
| `x ^ 2` | `x` to the natural-number power `2` (`Monoid.npow`), not `x * x` as text |
| `2 * a * b` | `(2 * a) * b`: `*` groups to the left |
| `(a + b) / 2` | real division (`a / b = a * b⁻¹`; Mathlib sets `x / 0 = 0`) |
| `√x` | `Real.sqrt x`, how the infoview prints it. Defined for every real: `√x = 0` when `x < 0` |
| `P √(x ^ 2)` | `P (√(x ^ 2))`: the infoview drops the parentheses around a `√` argument |
| `x ≤ y` | the order on `ℝ`; `0 ≤ x` is "x is nonnegative" |

---

## Part 1 · `two_mul_le`

Statement: for all reals `a, b`, `2ab ≤ a² + b²`. It is `0 ≤ (a − b)² = a² − 2ab + b²` rearranged.

**R1 · `sq_nonneg e`** changes the **context** when used as `have h := sq_nonneg e`: it adds the fact that a
square is nonnegative. The lemma is `sq_nonneg (a : R) : 0 ≤ a ^ 2`, for any linearly ordered ring `R`
(`ℝ`, `ℚ`, `ℤ` qualify). Placeholders: `(e : ℝ)`, any real expression such as `x - 1`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ e ^ 2 ⊢ G` |

**R2 · `nlinarith [t₁, …, tₙ]`** **closes** the goal, or fails. It is `linarith` (a decision procedure for
linear (in)equalities over ordered fields, which treats each monomial such as `a * b` or `a ^ 2` as an
unknown) with a preprocessing step: it adds each proof term `tᵢ` as a hypothesis, multiplies pairs of
hypotheses together, and expands everything into monomials. You must supply the right square: it does not
guess `sq_nonneg (a - b)` by itself. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `x : ℝ ⊢ 0 ≤ x ^ 2 - 6 * x + 10` | `∅` (with `[sq_nonneg (x - 3)]`: the goal is that square plus `1`) |

**W1.** Several hints at once: `x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2` closes with
`nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]`: twice the gap is the sum of the three
squares.

| Before | After |
|---|---|
| `x y z : ℝ ⊢ x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2` | `∅` |

---

## Part 2 · `amgm_sq`

Statement: for all reals `a, b`, `ab ≤ ((a + b)/2)²`, the squared form of AM-GM. Again
`((a + b)/2)² − ab = (a − b)²/4`. Same entries as Part 1: R1 for the square, R2 to close.

---

## Part 3 · `amgm`

Statement: for `0 ≤ a` and `0 ≤ b`, `√(ab) ≤ (a + b)/2`. Plan: write the right side as a square root,
`(a + b)/2 = √(((a + b)/2)²)` (true because `(a + b)/2 ≥ 0`), then use that `√` is monotone together with
Part 2.

**R3 · `rw [show s = t from proof]`** changes the **goal**: `show s = t from proof` is a one-off equation
term, and `rw` replaces **every** occurrence of `s` in the goal by `t`. Placeholders: `(s t : ℝ)`,
`proof : s = t`.

| Before | After |
|---|---|
| `⊢ P s` | `⊢ P t` |

**R4 · `Real.sqrt_sq`** changes the **goal**. The lemma is `Real.sqrt_sq {x : ℝ} (h : 0 ≤ x) : √(x ^ 2) = x`.
Without `0 ≤ x` it is false (`√((-1)²) = 1`). Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P √(x ^ 2)` | `⊢ P x` |

**R5 · `hst.symm`** changes the **context** when used as `have h := hst.symm`. `Eq.symm : s = t → t = s`, and
`hst.symm` is dot notation for `Eq.symm hst`. Use it to turn `√(x ^ 2) = x` from R4 into `x = √(x ^ 2)`.
Placeholders: `{α : Type} (s t : α) (hst : s = t)`.

| Before | After |
|---|---|
| `hst : s = t ⊢ G` | `hst : s = t, h : t = s ⊢ G` |

**R6 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) by walking the syntax of `e`:
numerals, squares, sums, products and quotients of nonnegative parts, and variables `x` for which a
hypothesis `0 ≤ x` or `0 < x` is in the context. It fails on subtraction. Typical use: the side condition
of R4, `Real.sqrt_sq (by positivity)`. Placeholders: `(x y : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ 0 ≤ (x + y ^ 2) / 3` | `∅` |

**W3.** R4 with its side condition proved by R6 inside the brackets: `rw [Real.sqrt_sq (by positivity)]`.

| Before | After |
|---|---|
| `⊢ P √(((x + y ^ 2) / 3) ^ 2)` | `⊢ P ((x + y ^ 2) / 3)` |

**R7 · `Real.sqrt_le_sqrt`** changes the **goal** when applied: the lemma is
`Real.sqrt_le_sqrt {x y : ℝ} (h : x ≤ y) : √x ≤ √y` (`√` is monotone). `apply` it to reduce a comparison
of roots to a comparison of their arguments, or give it the proof directly: `exact Real.sqrt_le_sqrt h`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ √x ≤ √y` | `⊢ x ≤ y` |

**W2: bound a root by a variable.** Goal `√u ≤ v` with `hv : 0 ≤ v` and `huv : u ≤ v ^ 2`. Rewrite `v` as a root
with R3, whose proof is R4 flipped by R5, `(Real.sqrt_sq hv).symm`; then R7 with `huv`.

| Before | After |
|---|---|
| `hv : 0 ≤ v, huv : u ≤ v ^ 2 ⊢ √u ≤ v` | `⊢ √u ≤ √(v ^ 2)` |

A theorem proved earlier in the file is used like a library lemma: `amgm_sq a b` is a proof of
`a * b ≤ ((a + b) / 2) ^ 2`.

---

## Traps

- `nlinarith` with no hint fails on these goals: the whole proof is choosing the square to pass
  (`sq_nonneg (a - b)`).
- `rw [show s = t from …]` rewrites **every** `s` in the goal. If `s` occurs twice (say `√(x - 1) ≤ x` with
  `s := x`), both copies change, and the goal becomes `√(√(x ^ 2) - 1) ≤ √(x ^ 2)`. In Part 3 the expression
  `(a + b) / 2` occurs once, so this is safe.
- When the right side of `show s = t` contains `s` itself (`x = √(x ^ 2)`), `rw` still rewrites only the
  occurrences in the current goal, once; it does not loop.
- `Real.sqrt_sq` needs `0 ≤ x`. For `(a + b) / 2` that follows from `ha` and `hb`, which is why `amgm` has them;
  `positivity` finds them in the context.
- `√x` is `0` for `x < 0`, so lemmas about `√` often carry a sign hypothesis; read the statement with `#check`.
- `x ^ 2` and `x * x` are different text: `rw` with a lemma about `x ^ 2` does not fire on `x * x`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a square is `≥ 0` | `sq_nonneg e : 0 ≤ e ^ 2` | R1 |
| polynomial inequality from a square | `nlinarith [sq_nonneg (e)]` | R2 |
| replace `s` by `t` once, with a proof | `rw [show s = t from proof]` | R3 |
| `√(x ^ 2) → x` (needs `0 ≤ x`) | `rw [Real.sqrt_sq hx]` | R4 |
| flip an equation | `h.symm` | R5 |
| prove `0 ≤ e` | `positivity` (or `(by positivity)` as an argument) | R6 |
| `√x ≤ √y` from `x ≤ y` | `apply Real.sqrt_le_sqrt` / `exact Real.sqrt_le_sqrt h` | R7 |
| use an earlier theorem | `exact amgm_sq a b` (any theorem name with its arguments) | |
| see the state | infoview | |
