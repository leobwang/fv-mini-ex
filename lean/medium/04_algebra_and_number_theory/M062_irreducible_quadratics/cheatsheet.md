# M062 · Irreducible quadratics: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's polynomials (`ℚ[X]`, `eval`,
`IsRoot`, `degree` / `natDegree`), `Irreducible`, the tactics `compute_degree!`, `positivity`,
`nlinarith`, and `Complex.I`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`/`have`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{R : Type}` is any type. A bracket such as `[Semiring R]` is a
  requirement on `R` (a *type class*). Each entry says which familiar types meet it.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℚ[X]`, `ℂ[X]`, `R[X]` | `Polynomial ℚ` etc.: polynomials in one variable `X` with coefficients in ℚ (notation from `open Polynomial`) |
| `X` | the polynomial variable `Polynomial.X`. `X ^ 2 + 1` is a polynomial, not a number |
| `1`, `2` inside a polynomial | constant polynomials (numerals are cast automatically) |
| `eval x p` | the value $p(x)$ of `p` at the number `x` (`Polynomial.eval`; note the argument order: point first) |
| `p.IsRoot x` | `x` is a root: by definition `eval x p = 0` (`Polynomial.IsRoot`) |
| `Irreducible p` | `p` is not a unit (over a field: not a nonzero constant), and `p = a * b → IsUnit a ∨ IsUnit b`. Over a field: no factorization into two non-constant polynomials |
| `IsUnit a` | `a` has a multiplicative inverse. In `K[X]`, `K` a field, the units are the nonzero constants |
| `p.natDegree` | the degree as a natural number `ℕ`; the zero polynomial gets `0` |
| `p.degree` | the degree in `WithBot ℕ` = `ℕ ∪ {⊥}`; the zero polynomial gets `⊥` ("minus infinity"). `2 = 1` in a hypothesis about `degree` is an equation in `WithBot ℕ` |
| `Finset.Icc a b` | the finite set $\{a, a+1, …, b\}$ of naturals (closed interval) |
| `Complex.I` | the imaginary unit $i$, with $i^2 = -1$ |
| `¬A` | `A → False`. `¬` binds weaker than `=`: `¬x ^ 2 + 1 = 0` is `¬(x ^ 2 + 1 = 0)`, i.e. `x ^ 2 + 1 ≠ 0` |
| `case hdeg`, `case hnot` | the two goals R2 leaves: the degree goal and the no-root goal |

---

## Part 1 · `irreducible_X_sq_add_one`

Statement: `X² + 1` is irreducible in `ℚ[X]`. Mathematically: a degree-2 polynomial over a field that
factors has a linear factor, hence a root; `x² + 1 > 0` for every rational `x`.

### Degree goal + no-root goal

**R1 · `compute_degree!`** **closes** a goal `p.natDegree = n` or `p.degree = n` for an explicitly written
polynomial `p`: it computes the degree and proves the leading coefficient is nonzero. Use it inside
`have hdeg : p.natDegree = n := by compute_degree!` (`have`: TACTIC_STATES, "Adding facts"); `rw [hdeg]`
then replaces the degree by the numeral.

| Before | After |
|---|---|
| `⊢ (X ^ 3 + X).natDegree = 3` | no goals |
| `⊢ (X ^ 3 + X).degree = 3` | no goals |

**R2 · `apply irreducible_of_degree_le_three_of_not_isRoot`** changes the **goal list**: `Irreducible p`
becomes two goals. The lemma (`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`) is
`p.natDegree ∈ Finset.Icc 1 3 → (∀ x, ¬ p.IsRoot x) → Irreducible p`. Placeholders:
`{K : Type} [Field K] (p : K[X])`; `ℚ`, `ℝ`, `ℂ` are fields, `ℤ` is not.

| Before | After |
|---|---|
| `⊢ Irreducible p` | `⊢ p.natDegree ∈ Finset.Icc 1 3`, `⊢ ∀ (x : K), ¬p.IsRoot x` |

**R3 · `decide`** **closes** `n ∈ Finset.Icc a b` for numerals: membership in a concrete finite set of
naturals is decidable, and Lean just computes it.

| Before | After |
|---|---|
| `⊢ 3 ∈ Finset.Icc 1 5` | no goals |

### Evaluating the polynomial at `x`

After `intro x` the no-root goal is `¬ p.IsRoot x`. R4–R8 turn it into a statement about numbers; give
them all to one `simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]`.

**R4 · `simp only [IsRoot]`** changes the **goal**: it unfolds `IsRoot`. (`rw [IsRoot.def]` does the same;
`IsRoot.def : p.IsRoot a ↔ eval a p = 0`.) Placeholders: `{R : Type} [Semiring R] (p : R[X]) (x : R)`; a
semiring has `+`, `*`, `0`, `1` (`ℕ`, `ℚ`, `ℂ` all qualify).

| Before | After |
|---|---|
| `⊢ ¬p.IsRoot x` | `⊢ ¬eval x p = 0` |

**R5 · `eval_add`** changes the **goal**: `eval x (p + q) = eval x p + eval x q`. Placeholders:
`{R : Type} [Semiring R] (p q : R[X]) (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x (p + q))` | `⊢ P (eval x p + eval x q)` |

**R6 · `eval_pow`** changes the **goal**: `eval x (p ^ n) = eval x p ^ n`. Placeholders:
`{R : Type} [CommSemiring R] (p : R[X]) (x : R) (n : ℕ)` (commutative `*`; `ℚ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (eval x (p ^ n))` | `⊢ P (eval x p ^ n)` |

**R7 · `eval_X`** changes the **goal**: `eval x X = x`. Placeholders: `{R : Type} [Semiring R] (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x X)` | `⊢ P x` |

**R8 · `eval_one`** changes the **goal**: `eval x 1 = 1` (the constant polynomial `1`). Placeholders:
`{R : Type} [Semiring R] (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x 1)` | `⊢ P 1` |

**R9 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `¬ e = 0` (i.e. `e ≠ 0`) when `e` is built so that
it is visibly positive: even powers, sums of nonnegative terms with a positive constant, positive numerals.
It reasons on the shape of `e` only; it never splits on the sign of a variable. Placeholders:
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α)`, an ordered field (`ℚ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ ¬a ^ 2 + b ^ 2 + 2 = 0` | no goals |

### Worked combinations (W1, W2, on other polynomials)

**W1: the degree goal.** `have hdeg : (X ^ 3 + X : ℚ[X]).natDegree = 3 := by compute_degree!` (R1), then
`rw [hdeg]`, then `decide` (R3):

```lean-goal
⊢ (X ^ 3 + X).natDegree ∈ Finset.Icc 1 3
⊢ 3 ∈ Finset.Icc 1 3
```

**W2: the no-root goal** for `X ^ 4 + 1`. `intro x`, the `simp only` of R4–R8, then `positivity` (R9):

```lean-goal
⊢ ∀ (x : ℚ), ¬(X ^ 4 + 1).IsRoot x
⊢ ¬(X ^ 4 + 1).IsRoot x
⊢ ¬x ^ 4 + 1 = 0
```

---

## Part 2 · `irreducible_X_sq_add_X_add_one`

Statement: `X² + X + 1` is irreducible in `ℚ[X]`. Same plan as Part 1 (R1, R2, R3, R4–R8). The no-root goal
ends as `¬ x ^ 2 + x + 1 = 0`, and `positivity` fails on it: the term `x` alone can be negative. Complete
the square: $x^2 + x + 1 = (x + \tfrac12)^2 + \tfrac34 > 0$.

**R10 · `sq_nonneg`** changes the **context** (with `have`): `sq_nonneg a : 0 ≤ a ^ 2`. Usually you do not
`have` it but pass it to `nlinarith` (R11). Placeholders: an ordered field `α` as in R9, `(a b : α)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ (a + b) ^ 2 ⊢ G` |

**R11 · `nlinarith [t₁, …]`** **closes** a polynomial equation, inequality, or `¬ e = 0` over an ordered
field, using the hypotheses and the extra facts `tᵢ`. It multiplies pairs of facts and then runs linear
arithmetic (`linarith`), so it needs the right square as a hint: for `a² - 2a + 2 = (a - 1)² + 1`, the hint
is `sq_nonneg (a - 1)`. Placeholders: an ordered field `α` as in R9, `(a : α)`.

| Before | After |
|---|---|
| `⊢ ¬a ^ 2 - 2 * a + 2 = 0` | no goals |

**W3.** `¬ a ^ 2 - a + 1 = 0` over ℚ: `a² - a + 1 = (a - ½)² + ¾`, so `nlinarith [sq_nonneg (a - 1 / 2)]`.

---

## Part 3 · `not_irreducible_over_C`

Statement: `X² + 1` is **not** irreducible in `ℂ[X]`. Argument: suppose it is. It has the root `i`, and an
irreducible polynomial with a root `a` is (up to a constant) `X - a`, so its degree is 1. But its degree is 2.

**R12 · `intro h` on `¬ A`** changes the **context and goal**: `¬ A` is `A → False`, so `intro` assumes `A`.
Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R13 · `Complex.I_sq`** changes the **goal**: `Complex.I ^ 2 = -1`. `simp` knows it, so
`have hroot : p.IsRoot Complex.I := by simp` works for a polynomial whose value at `i` simplifies to `0`
(simp unfolds `IsRoot` and applies R5–R8 by itself).

| Before | After |
|---|---|
| `⊢ P (Complex.I ^ 2)` | `⊢ P (-1)` |

**R14 · `degree_eq_one_of_irreducible_of_root`** changes the **context**:
`Polynomial.degree_eq_one_of_irreducible_of_root : Irreducible p → p.IsRoot x → p.degree = 1`, used as
`have h1 := degree_eq_one_of_irreducible_of_root hp hr`. Note it concludes about `degree`, not
`natDegree`. Placeholders: `{R : Type} [CommRing R] [IsDomain R] (p : R[X]) (a : R)`; an integral domain
(no zero divisors): every field, and `ℤ`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : p.degree = 1 ⊢ G` |

**R15 · `rw [h] at h1`** changes the **context**: it rewrites the hypothesis `h1` instead of the goal.
Placeholders: `{α : Type} (a b c : α) (h : a = b)`.

| Before | After |
|---|---|
| `h1 : a = c ⊢ b = c` | `h1 : b = c ⊢ b = c` |

**R16 · `absurd`** **closes** any goal: `absurd : a → ¬ a → b`. Write `exact absurd ha hn`, or
`exact absurd ha (by tac)` to prove the negation on the spot. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `ha : A, hn : ¬A ⊢ B` | no goals |

**R17 · `decide`** **closes** `¬ m = n` for distinct numerals in `WithBot ℕ`, the type of `degree`. (In `ℕ`
`decide` works too; in `ℚ`, `ℝ`, `ℂ` use `norm_num`.)

| Before | After |
|---|---|
| `⊢ ¬3 = 1` | no goals |

**W4: `X ^ 4 - 1` is not irreducible over ℂ.** `intro h` (R12), `hroot` at `Complex.I` by `simp` (R13,
`i⁴ = 1`), `h1` from R14, `hdeg : … .degree = 4` by R1, `rw [hdeg] at h1` (R15), then
`exact absurd h1 (by decide)` (R16, R17):

| Before | After |
|---|---|
| `⊢ ¬Irreducible (X ^ 4 - 1)` | `h : Irreducible (X ^ 4 - 1) ⊢ False` |
| `h1 : (X ^ 4 - 1).degree = 1 ⊢ False` | `h1 : 4 = 1 ⊢ False` |

---

## Traps

- `degree` lives in `WithBot ℕ`, `natDegree` in `ℕ`. R2 wants `natDegree`, R14 gives `degree`: prove the
  `hdeg` that matches (`compute_degree!` does both). `rw [hdeg]` fails if the kinds differ.
- `positivity` fails on `x ^ 2 + x + 1` (the lone `x` has no known sign). Complete the square for `nlinarith`
  (R10, R11).
- `nlinarith` without the right hint usually fails: give it `sq_nonneg (x + c)` with the `c` from completing
  the square.
- `eval_one` handles only the constant `1`. A constant such as `3` in `X ^ 2 + 3` evaluates by `eval_ofNat`
  (or just `simp`); a `simp only [...]` list without it leaves `eval x 3`.
- `eval x p` takes the point first. `IsRoot` is a definition, so `simp only [IsRoot]` (or `IsRoot.def`) must
  unfold it before the `eval_…` lemmas can fire.
- The polynomial in a `have` needs its type: `(X ^ 2 + 1 : ℂ[X])`. Without it Lean cannot tell which ring
  `X` lives in.
- `t1 ; t2` runs `t2` on the first goal only. After R2, handle the two goals with `·` bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| degree of an explicit polynomial | `have hdeg : p.natDegree = 2 := by compute_degree!` (or `.degree`) | R1 |
| irreducible over a field, degree 2 or 3 | `apply irreducible_of_degree_le_three_of_not_isRoot` | R2 |
| `2 ∈ Finset.Icc 1 3` | `rw [hdeg]; decide` | R3 |
| evaluate `p` at `x` | `simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]` | R4–R8 |
| visibly positive `≠ 0` | `positivity` | R9 |
| not visibly positive | `nlinarith [sq_nonneg (x + c)]` | R10, R11 |
| prove `¬ A` | `intro h` (goal `False`) | R12 |
| `i ^ 2 = -1` | `Complex.I_sq` (in `simp`) | R13 |
| irreducible + root → degree 1 | `have h1 := degree_eq_one_of_irreducible_of_root h hroot` | R14 |
| rewrite a hypothesis | `rw [hdeg] at h1` | R15 |
| `h1 : 2 = 1` in `WithBot ℕ` | `exact absurd h1 (by decide)` | R16, R17 |
| see the state | infoview | |
