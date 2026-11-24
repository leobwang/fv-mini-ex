# M187 · Derivative of physicists' Hermite polynomials: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `simp`, `simp only`, `ring`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), including `induction` on `ℕ`. **New here:** Mathlib's
polynomials (`ℤ[X]`, `X`, `C`, the formal `derivative` and its rules), the ℕ-scalar action `k • p`, casts
`↑n` of natural numbers into polynomials, and physlib's `physHermite`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{R : Type}` is any type. A bracket such as `[Semiring R]` is a
  requirement on `R` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℤ[X]`, `R[X]` | `Polynomial ℤ`, `Polynomial R`: polynomials in one variable with coefficients in `ℤ` (in `R`). A polynomial is a formal object, not a function |
| `X` | the variable, itself a polynomial |
| `C a` | the constant polynomial `a` (`C : R → R[X]`); `C 1 = 1` (R3) |
| `2`, `1`, `0` in a polynomial goal | constant polynomials (`2 : ℤ[X]`) |
| `physHermite n` | the physicists' Hermite polynomial `Hₙ : ℤ[X]`, defined by `H₀ = C 1` and `Hₙ₊₁ = 2X·Hₙ − Hₙ'` (R3, R4) |
| `derivative p` | the formal derivative `p'`: it acts on coefficients, `(Σ aₖXᵏ)' = Σ k·aₖXᵏ⁻¹`; no limits involved |
| `derivative (derivative p)` | `p''` |
| `k • p` with `k : ℕ` | `p + ⋯ + p` (`k` copies), the ℕ-scalar action; R11 turns it into `↑k * p` |
| `2 • X` | `(2 : ℕ) • X`, i.e. `X + X`; after R11 and R12 it is `2 * X` |
| `2 * (n + 1) • p` | `2 * ((n + 1) • p)`: `•` binds tighter than `*`; `2 : ℤ[X]`, `n + 1 : ℕ` |
| `↑n` | the natural number `n` cast to the constant polynomial `n` (`Nat.cast`) |
| `↑2` | the natural number `2` cast; R12 rewrites it to the numeral `2 : ℤ[X]` |
| `OfNat.ofNat n` | how a lemma statement writes "the numeral `n`" (`2`, `3`, …) |
| `n✝`, `a✝` | inaccessible names: `induction` without `with` made them (R1) |
| `inst✝ : Semiring R` | an unnamed type-class assumption from a `[…]` binder |
| `case zero`, `case succ` | the goals for the base case `n = 0` and for the induction step |
| `physHermite (n + 1 + 1)` | `Hₙ₊₂`: the statement at `n + 1` before any simplification |

---

## Part 1 · `hermite_derivative`

Statement: for every `n : ℕ`, `derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n`, that is
`H'ₙ₊₁ = 2(n + 1)·Hₙ`. This is the ladder relation: on the oscillator eigenfunctions (Hermite polynomial
times a Gaussian) the lowering (annihilation) operator acts by it.

Plan: induction on `n` (R1). Zero case `H₁' = 2·H₀`: `simp` with R2. Step: unfold `Hₙ₊₂` once (R4), apply
the derivative rules (R6, R5), use `ih` for `H'ₙ₊₁`, unfold `Hₙ₊₁` (R4 again), let `simp` evaluate the
leftover derivatives and casts (R7–R13), finish with `ring` (R14).

### Induction

**R1 · `induction n`** changes the **goal list and the context**: one goal for `0`, one for `n + 1`. In `succ`
the context gains the variable `n✝` and the induction hypothesis `a✝ : P n✝`. With
`induction n with | zero => … | succ n ih => …` they are named `n` and `ih`, and each alternative is a tactic
block for that goal. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After (case `zero`) | After (case `succ`) |
|---|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0` | `n✝ : ℕ, a✝ : P n✝ ⊢ P (n✝ + 1)` |

In the exercise the `zero` goal still shows `physHermite (0 + 1)` and `(0 + 1) •`; `simp` normalises `0 + 1`
to `1` and `1 • p` to `p`. The `succ` goal mentions `physHermite (n + 1 + 1)` and `ih` is the statement at `n`.

### The Hermite polynomials (physlib)

**R2 · `physHermite_one`** changes the **goal**. The lemma is `physHermite 1 = 2 * X`. It is tagged `@[simp]` (in the set of lemmas `simp` uses unasked), so
plain `simp` already uses it; `simp [physHermite_one]` names it explicitly. No placeholders.

| Before | After |
|---|---|
| `⊢ P (physHermite 1)` | `⊢ P (2 * X)` |

**R3 · `physHermite_zero`, then `C_1`** change the **goal**. The lemmas are `physHermite 0 = C 1` and
`C_1 : C 1 = 1`. `simp` uses `physHermite_zero` by itself and reaches `1` from `C 1` with its own
lemmas (`simp?` lists `eq_intCast`, `Int.cast_one` instead of `C_1`). No placeholders.

| Before | After `rw [physHermite_zero]` | After `rw [C_1]` |
|---|---|---|
| `⊢ P (physHermite 0)` | `⊢ P (C 1)` | `⊢ P 1` |

**R4 · `rw [physHermite_succ m]`** changes the **goal**. The lemma is
`physHermite_succ : ∀ n, physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)`: one step of
the recursion. With the argument `m` it rewrites exactly `physHermite (m + 1)` (every copy). Placeholders:
`(m : ℕ)`. In the step you use it twice: `m := n + 1` (the left side `Hₙ₊₂`) and later `m := n`.

| Before | After |
|---|---|
| `⊢ P (physHermite (m + 1))` | `⊢ P (2 • X * physHermite m - derivative (physHermite m))` |

### Differentiating

`derivative : R[X] → R[X]` is linear and obeys the Leibniz rule. `simp` applies R5 and R7–R10 by itself; R5
and R6 you name in `rw` so that `ih` can be used (its left side `derivative (physHermite (n + 1))` must appear).

**R5 · `derivative_mul`** changes the **goal**. The lemma is
`derivative (f * g) = derivative f * g + f * derivative g`. Placeholders: `{R : Type} [Semiring R] (f g : R[X])`
(R has `+`, `*`, `0`, `1`; `ℕ`, `ℤ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (derivative (f * g))` | `⊢ P (derivative f * g + f * derivative g)` |

**R6 · `derivative_sub`** changes the **goal**. The lemma is `derivative (f - g) = derivative f - derivative g`.
Placeholders: `{R : Type} [Ring R] (f g : R[X])` (a semiring with subtraction: `ℤ`, `ℝ`; not `ℕ`).

| Before | After |
|---|---|
| `⊢ P (derivative (f - g))` | `⊢ P (derivative f - derivative g)` |

**R7 · `derivative_X`** changes the **goal**: `derivative X = 1`. Placeholders: `{R : Type} [Semiring R]`.

| Before | After |
|---|---|
| `⊢ P (derivative X)` | `⊢ P 1` |

**R8 · `derivative_ofNat`** changes the **goal**: the derivative of a numeral `≥ 2` is `0`,
`derivative (OfNat.ofNat n) = 0`. Placeholders: `{R : Type} [Semiring R]`.

| Before | After |
|---|---|
| `⊢ P (derivative 2)` | `⊢ P 0` |

**R9 · `derivative_natCast`, `derivative_one`** change the **goal**: `derivative ↑n = 0` and
`derivative 1 = 0` (constants differentiate to `0`). Placeholders: `{R : Type} [Semiring R] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (derivative ↑n)` | `⊢ P 0` |
| `⊢ P (derivative 1)` | `⊢ P 0` |

**R10 · `derivative_add`** changes the **goal**. The lemma is `derivative (f + g) = derivative f + derivative g`.
`simp` needs it for `derivative ((↑n + 1) * p)`, which R5 splits into `derivative (↑n + 1) * p + …`.
Placeholders: `{R : Type} [Semiring R] (f g : R[X])`.

| Before | After |
|---|---|
| `⊢ P (derivative (f + g))` | `⊢ P (derivative f + derivative g)` |

### Natural-number scalars and casts

**R11 · `nsmul_eq_mul`** changes the **goal**. The lemma is `k • a = ↑k * a` for `k : ℕ`: the repeated sum
becomes a product with the cast `↑k`. `simp` applies it, so `2 • X` and `(n + 1) • p` turn into products.
Placeholders: `{α : Type} [NonAssocSemiring α] (k : ℕ) (a : α)` (`+`, `*`, `0`, `1` without needing
associativity of `*`; every polynomial ring `R[X]` over a semiring qualifies).

| Before | After |
|---|---|
| `⊢ P (k • a)` | `⊢ P (↑k * a)` |

**R12 · `Nat.cast_ofNat`** changes the **goal**: a cast numeral `↑2` becomes the numeral `2` of the target
type, `↑(OfNat.ofNat n) = OfNat.ofNat n`. Placeholders: `{R : Type} [Semiring R]`.

| Before | After |
|---|---|
| `⊢ P (↑2 * X)` | `⊢ P (2 * X)` |

**R13 · `Nat.cast_add`, `Nat.cast_one`** change the **goal**: the cast moves inside sums,
`↑(m + k) = ↑m + ↑k` and `↑1 = 1`. `simp` and `push_cast` apply both. Placeholders:
`{R : Type} [Semiring R] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(n + 1)` | `⊢ P (↑n + 1)` |

### Closing

**R14 · `ring`** **closes** an identity that holds in every commutative ring, here `ℤ[X]`. It treats `X`, `↑n`,
`physHermite n` and `derivative (physHermite n)` as unknowns: it does not know the Hermite recursion or any rule
for `derivative`. So run `simp` first (R7–R13) and `ring` last: to `ring`, `derivative (f * g)` is just one more
unknown, unrelated to `derivative f` and `derivative g`.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: `rw [ih]` rewrites every copy, also inside a second derivative.** With `ih : derivative f = q`, the
goal's `derivative (derivative f)` becomes `derivative q`. In the exercise this turns `Hₙ₊₁''` into
`(2(n + 1)·Hₙ)'` at the same time as `Hₙ₊₁'` into `2(n + 1)·Hₙ`.

| Before | After |
|---|---|
| `ih : derivative f = q ⊢ P (X * derivative f - derivative (derivative f))` | `⊢ P (X * q - derivative q)` |

**W2: what `simp` does to the leftover derivatives.** One `simp only` with R5, R7–R13 and the bookkeeping
lemmas `zero_mul`, `mul_one`, `zero_add`, `add_zero` closes

```lean-goal
⊢ derivative (2 • X) * q - derivative ((n + 1) • q) = 2 * q - (↑n + 1) * derivative q
```

Plain `simp` does the same; `simp?` prints the lemma list it used.

**W3: the whole pattern on `Xpow n = Xⁿ`** (defined by `Xpow 0 = 1`, `Xpow (n + 1) = X * Xpow n`), proving
`derivative (Xpow (n + 1)) = (n + 1) • Xpow n`: `induction n with`; zero by `simp [Xpow]`; step by
`rw [Xpow_succ (n + 1), derivative_mul, ih, Xpow_succ n]`, then `simp`, then `ring`.

---

## Traps

- Give `physHermite_succ` its argument. `rw [physHermite_succ]` rewrites the first `physHermite (_ + 1)` it
  meets, which may not be the one you mean.
- Order matters: `rw [ih]` before `rw [physHermite_succ n]`. Unfolding `physHermite (n + 1)` first destroys
  `derivative (physHermite (n + 1))`, the left side of `ih`, and `rw [ih]` then fails.
- `2 * (n + 1) • p` is `2 * ((n + 1) • p)`, a polynomial `2` times an ℕ-scalar multiple. Do not read it as
  `(2 * (n + 1)) • p`.
- `ring` knows nothing about `derivative`: `simp` before `ring`.
- When you write a cast yourself in a `have`, give the type: `(n : ℤ[X])`. A bare `↑n` with nothing fixing
  the target type fails to elaborate.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on `n`, name the step's data | `induction n with`, alternatives `zero`, `succ n ih` | R1 |
| `H₁` | `physHermite_one : physHermite 1 = 2 * X` | R2 |
| `H₀` | `physHermite_zero : physHermite 0 = C 1`, `C_1` (simp does it) | R3 |
| unfold `Hₘ₊₁` once | `rw [physHermite_succ m]` | R4 |
| derivative of a product / difference / sum | `derivative_mul` / `derivative_sub` / `derivative_add` | R5, R6, R10 |
| derivative of `X`, numerals, casts, `1` | `derivative_X`, `derivative_ofNat`, `derivative_natCast`, `derivative_one` (simp) | R7, R8, R9 |
| `k • p → ↑k * p` | `nsmul_eq_mul` (simp) | R11 |
| `↑2 → 2`, `↑(n + 1) → ↑n + 1` | `Nat.cast_ofNat`, `Nat.cast_add`, `Nat.cast_one` (simp, push_cast) | R12, R13 |
| use the hypothesis everywhere | `rw [ih]` | W1 |
| polynomial identity left over | `simp` then `ring` | W2, R14 |
| see the state | infoview | |
