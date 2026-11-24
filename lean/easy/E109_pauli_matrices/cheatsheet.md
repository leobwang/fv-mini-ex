# E109 · Pauli matrices: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's 2×2 matrices written as literals
`!![…]`, products of literals, the identity matrix `1`, negation `-M` and scalar multiplication `k • M` of
literals, and the complex unit `I` with `I * I = -1`. All four parts are closed by one `simp` call each;
the entries below show the steps that call takes, one at a time.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid α]` is
  a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℂ` | the complex numbers (Mathlib's `Complex`) |
| `I` | `Complex.I`, the imaginary unit $i$; `open Complex` (in the spec) lets you drop the prefix |
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 matrices with complex entries. Rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` (`;` separates rows) |
| `M * N` | the matrix product $MN$, $(MN)_{ik} = \sum_j M_{ij} N_{jk}$ |
| `1` (a matrix) | the identity matrix; Lean does **not** display it as `!![1, 0; 0, 1]` (R3) |
| `-M` | every entry of `M` negated |
| `k • M` | the scalar `k` times every entry of `M` (`•` is scalar multiplication, typed `\smul`) |
| `-1` (a matrix) | minus the identity, `-(1 : Matrix …)` |

---

## Part 1 · `X_sq`

Statement: `X * X = 1` with `X = !![0, 1; 1, 0]`: the bit flip squares to the identity.

**R1 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. Placeholders: `D`
defined by `def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]`. `simp [X, …]` does the same for `X`.

| Before | After |
|---|---|
| `⊢ P D` | `⊢ P !![1, 2; 3, 4]` |

**R2 · `rw [Matrix.mul_fin_two]`** changes the **goal**: the product of two literals becomes one literal whose
entries are row-times-column sums. The lemma is
`Matrix.mul_fin_two : !![a, b; c, d] * !![p, q; r, s] = !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]`.
Placeholders: `{α : Type} [AddCommMonoid α] [Mul α]` (α has a commutative `+` with `0`, and a `*`; `ℕ`, `ℝ`, `ℂ`
qualify), `(a b c d p q r s : α)`. `simp` computes the same product by itself, so you need not name it.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] * !![p, q; r, s])` | `⊢ P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]` |

**R3 · `rw [Matrix.one_fin_two]`** changes the **goal**: the identity matrix `1` becomes the literal
`!![1, 0; 0, 1]`. The lemma is `Matrix.one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]`.
Placeholders: `{α : Type} [Zero α] [One α]` (α has `0` and `1`; every number type qualifies). `simp` never
applies it by itself, so put it in the `simp` set whenever a `1` (or `-1`) matrix sits on one side.

| Before | After |
|---|---|
| `⊢ P 1` | `⊢ P !![1, 0; 0, 1]` |

**R7 · entry arithmetic, by `simp`** changes the **goal**: `simp` cleans each entry with `zero_mul`, `mul_zero`,
`one_mul`, `mul_one`, `add_zero`, `zero_add`, `mul_neg`, `neg_neg`, …. Placeholders: `(a b c : ℂ)`,
`(P : ℂ → ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (0 * a + 1 * b) (c * -1 + 0)` | `⊢ P b (-c)` |

**R8 · equation of two literals, by `simp`** changes the **goal**: `!![…] = !![…]` becomes one equation per
entry, and every entry equation that is `x = x` disappears. When both literals have become identical, the goal
is closed. Placeholders: `{α : Type} (a b c d p q r s : α)`.

| Before | After |
|---|---|
| `⊢ !![a, b; c, d] = !![p, q; r, s]` | `⊢ (a = p ∧ b = q) ∧ c = r ∧ d = s` |

---

## Part 2 · `Y_sq`

Statement: `Y * Y = 1` with `Y = !![0, -I; I, 0]`. The same steps as Part 1 (R1, R2, R3, R7, R8); the entries
now contain `I * I` and minus signs.

**R4 · `Complex.I_mul_I`** changes the **goal**. The lemma is `Complex.I_mul_I : I * I = -1`, i.e. $i^2 = -1$.
`simp` applies it by itself. Placeholders: `(P : ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (I * I)` | `⊢ P (-1)` |

The entry `(0, 0)` of `Y * Y` is `0 * 0 + -I * I`: `simp` moves the sign out of the product, applies R4 to
get `-(-1)`, and `neg_neg : -(-x) = x` gives `1`.

**W2: the phase gate `S = !![1, 0; 0, I]`, one step at a time.** R1, R2, then one `simp` for R4, R7, R8:

```lean-goal
⊢ S * S = !![1, 0; 0, -1]
⊢ !![1, 0; 0, I] * !![1, 0; 0, I] = !![1, 0; 0, -1]
⊢ !![1 * 1 + 0 * 0, 1 * 0 + 0 * I; 0 * 1 + I * 0, 0 * 0 + I * I] = !![1, 0; 0, -1]
```

---

## Part 3 · `Z_mul_X`

Statement: `Z * X = -(X * Z)` with `Z = !![1, 0; 0, -1]`: `Z` and `X` anticommute. Both sides are products
(R2); the right side is then a negated literal.

**R5 · negating a literal, by `simp`** changes the **goal**: `-!![a, b; c, d]` becomes `!![-a, -b; -c, -d]`.
`simp` uses `Matrix.neg_of` and `Matrix.neg_cons` for this; you never name them. Placeholders:
`{α : Type} [Neg α] (a b c d : α)` (α has a unary `-`; `ℤ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (-!![a, b; c, d])` | `⊢ P !![-a, -b; -c, -d]` |

**W3: anticommutation of `C = !![1, 1; 1, -1]` and `E = !![0, 1; -1, 0]`.** R1 for both names, R2 for both
products, then one `simp` for R5, R7, R8:

```lean-goal
⊢ C * E = -(E * C)
⊢ !![1, 1; 1, -1] * !![0, 1; -1, 0] = -(!![0, 1; -1, 0] * !![1, 1; 1, -1])
⊢ !![1 * 0 + 1 * -1, 1 * 1 + 1 * 0; 1 * 0 + -1 * -1, 1 * 1 + -1 * 0] = -!![0 * 1 + 1 * 1, 0 * 1 + 1 * -1; -1 * 1 + 0 * 1, -1 * 1 + 0 * -1]
```

---

## Part 4 · `X_mul_Y`

Statement: `X * Y = I • Z`: the product of two Pauli matrices is `i` times the third. The right side is a
scalar times a named matrix, so unfold all three names (R1).

**R6 · scaling a literal, by `simp`** changes the **goal**: `k • !![a, b; c, d]` becomes
`!![k * a, k * b; k * c, k * d]`. `simp` uses `Matrix.smul_of`, `Matrix.smul_cons` and `smul_eq_mul` (which
turns `k • x` for numbers into `k * x`). Placeholders: `{α : Type} [Mul α] (k a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (k • !![a, b; c, d])` | `⊢ P !![k * a, k * b; k * c, k * d]` |

**W4.** `I • S = !![I, 0; 0, -1]` is closed by `simp [S]`: R1, R6, then R4 (`I * I`), R7, R8.

---

## Traps

- **`1` is not a literal.** `simp [D]` computes the left side to `!![1, 0; 0, 1]` and then stops, because it
  never rewrites the matrix `1` on the right. W1 shows it: for `A = !![0, I; I, 0]`, `simp [A]` leaves

  ```lean-goal
  ⊢ !![-1, 0; 0, -1] = -1
  ```

  and only after R3 does `simp` finish:

  ```lean-goal
  ⊢ !![-1, 0; 0, -1] = -!![1, 0; 0, 1]
  ```

  Put `Matrix.one_fin_two` in the `simp` set from the start (`simp [A, Matrix.one_fin_two]`).
- **`simp` only unfolds the names you give it.** In Part 4 the right side `I • Z` stays `I • Z` unless `Z` is
  in the set: `simp [X, Y]` is not enough.
- If `simp` "made no progress" on a goal such as `!![1, 0; 0, 1] = 1`, the missing piece is R3, not more
  arithmetic.
- `decide` and `rfl` do not compute with `ℂ`: a complex number is a pair of reals, a real is an equivalence class
  of Cauchy sequences, and equality of those is not decided by unfolding. Use `simp`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `X`, `Y`, `Z` | `simp [X, Y, Z]` (only the names that occur) | R1 |
| product of two literals | automatic in `simp`, or `rw [Matrix.mul_fin_two]` | R2 |
| identity `1` → `!![1, 0; 0, 1]` | add `Matrix.one_fin_two` to the `simp` set | R3 |
| `I * I = -1` | automatic in `simp` (`Complex.I_mul_I`) | R4 |
| `-!![…]`, `k • !![…]` entrywise | automatic in `simp` | R5, R6 |
| `0 * a + 1 * b` → `b` | automatic in `simp` | R7 |
| compare two literals | automatic in `simp` | R8 |
| see each step | `simp only [D]`, then `rw [Matrix.mul_fin_two]`, then `simp` | W2, W3 |
| see the state | infoview | |
