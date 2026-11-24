# E074 · Matrix notation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's `Matrix` type, the literals
`!![…]` (matrix) and `![…]` (vector), determinant, transpose, matrix–vector and matrix–matrix products,
scalar multiplication `•`, the identity matrix `1`, and proving a matrix equation entry by entry.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing R]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℝ` | 2×2 matrices with real entries. Rows and columns are indexed by `Fin 2 = {0, 1}`. A matrix *is* a function `Fin 2 → Fin 2 → ℝ` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` (`;` separates rows) |
| `![a, b]` | the vector `(a, b)`, a function `Fin 2 → α` |
| `M i j` | the entry of `M` in row `i`, column `j`, counted from 0 |
| `M.det` | `Matrix.det M`, the determinant |
| `Mᵀ` | `Matrix.transpose M`: `Mᵀ i j = M j i`. Typed `\^T`; needs `open Matrix` |
| `M *ᵥ v` | `Matrix.mulVec M v`, matrix times column vector. Typed `*\_v`; needs `open Matrix` |
| `v ⬝ᵥ w` | `dotProduct v w = ∑ i, v i * w i` |
| `∑ i, f i` | the sum of `f i` over every `i` of the index type (here `Fin 2`) |
| `c • M` | scalar `c` times every entry of `M` (`•` is "smul", scalar multiplication; typed `\smul`) |
| `1` (a matrix) | the identity matrix: `1 i i = 1`, `1 i j = 0` for `i ≠ j` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases`: `⟨0, ⋯⟩` is the element of `Fin 2` with value `0`, and `⋯` is its hidden proof that `0 < 2` |
| `-(b * c)`, `a * d + -(b * c)` | how `simp` writes subtraction it produced from `+` and `-`; `ring` treats it as `a * d - b * c` |
| `case «0».«1»` | the goal for entry (0, 1) after `fin_cases i <;> fin_cases j` |

---

## Part 1 · `A_entry`

Statement: `A 0 1 = 2`, the entry in row 0, column 1 of `A = !![1, 2; 3, 4]`.

**R1 · `rfl`** **closes** the goal: an entry of a literal matrix is computed by unfolding definitions, and `A`
itself unfolds too. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ !![a, b; c, d] 1 0 = c` | no goals |

`rfl` only unfolds; it does no real-number arithmetic. `(1 : ℝ) + 2 = 3` is **not** closed by `rfl` (Traps).

---

## Part 2 · `A_det`

Statement: `A.det = -2`. Unfold `A`, expand the 2×2 determinant formula, read the entries, compute.

**R2 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. Placeholders: `D`
defined by `def D : Matrix (Fin 2) (Fin 2) ℝ := !![5, 6; 7, 8]`. `simp [A, …]` does the same for `A`.

| Before | After |
|---|---|
| `⊢ P D` | `⊢ P !![5, 6; 7, 8]` |

**R3 · `Matrix.det_fin_two`** changes the **goal**. The lemma is
`Matrix.det_fin_two (M : Matrix (Fin 2) (Fin 2) R) : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0`, the formula
$\det M = M_{00}M_{11} - M_{01}M_{10}$. Placeholders: `{R : Type} [CommRing R]` (R has `+`, `-`, a commutative
`*`, `0`, `1`; `ℤ`, `ℝ`, `ℂ` qualify, `ℕ` does not), `(M : Matrix (Fin 2) (Fin 2) R)`.

| Before | After |
|---|---|
| `⊢ P M.det` | `⊢ P (M 0 0 * M 1 1 - M 0 1 * M 1 0)` |

**R4 · entry of a literal, by `simp`** changes the **goal**. `simp` uses `Matrix.of_apply` and
`Matrix.cons_val_zero`, `Matrix.cons_val_one`, … for this; you never name them. Placeholders:
`{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 0 1)` | `⊢ P b` |

**R5 · `norm_num`** **closes** a goal made only of numerals (`+`, `-`, `*`, `/` on numbers, in `ℝ` too).
`simp` sometimes stops at such a goal; `norm_num` finishes it.

| Before | After |
|---|---|
| `⊢ 5 * 8 - 6 * 7 = -2` | no goals |

**W1.** `B = !![2, 1; 7, 5]`. `simp [B, Matrix.det_fin_two]` does R2, R3 and R4 in one call and stops at the
arithmetic; `norm_num` (R5) closes it:

```lean-goal
⊢ B.det = 3
⊢ 2 * 5 - 7 = 3
```

---

## Part 3 · `A_transpose`

Statement: `Aᵀ = !![1, 3; 2, 4]`, an equation of matrices. Reduce it to 4 entries, then compute each.

**R6 · `ext i j`** changes the **goal and the context**. It applies `Matrix.ext`: two matrices are equal when
every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R7 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context, and there is one goal
for each value `0, 1`. Placeholders: `(P : Fin 2 → Prop) (i : Fin 2)`. `fin_cases i <;> fin_cases j` gives all
four entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

**R8 · `Matrix.transpose_apply`** changes the **goal**: the lemma is `Mᵀ i j = M j i`. It holds by
definition, so `rfl` (R1) applies it by itself on concrete entries; you only need it with `rw`/`simp` when
the entries are not literals. Placeholders: `{α : Type} (M : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (Mᵀ i j)` | `⊢ P (M j i)` |

**W2.** `Bᵀ = !![2, 7; 1, 5]`: after `ext i j` (R6) and `fin_cases i <;> fin_cases j` (R7) there are four goals,
the first being

```lean-goal
⊢ Bᵀ ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨0, ⋯⟩) = !![2, 7; 1, 5] ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨0, ⋯⟩)
```

and `all_goals rfl` (R1) closes all four: no arithmetic is needed, only reading entries.

---

## Part 4 · `A_mulVec`

Statement: `A *ᵥ ![1, 1] = ![3, 7]`, an equation of vectors. Reduce it to 2 entries; each entry is a dot
product of a row of `A` with `![1, 1]`, which you expand into two terms and compute.

**R9 · `ext i`** changes the **goal and the context**. For vectors `Fin 2 → α` it applies `funext`: two
functions are equal when they agree at every input. Placeholders: `{α : Type} (v w : Fin 2 → α)`.

| Before | After |
|---|---|
| `⊢ v = w` | `i : Fin 2 ⊢ v i = w i` |

**R10 · `Matrix.mulVec`** changes the **goal**: unfolding the definition, entry `i` of `M *ᵥ v` is the dot
product of row `i` of `M` (the function `fun j => M i j`) with `v`. Placeholders:
`{α : Type} [NonUnitalNonAssocSemiring α]` (α has `+` and `*` with `0`, `*` distributing over `+`; `ℕ`, `ℤ`,
`ℝ` qualify), `(M : Matrix (Fin 2) (Fin 2) α) (v : Fin 2 → α) (i : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` |

**R11 · `dotProduct`** changes the **goal**: unfolding it, $v \cdot w = \sum_i v_i w_i$. Placeholders:
`{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a commutative `+` with `0`; `ℕ`, `ℝ` qualify),
`(v w : Fin 2 → α)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R12 · `Fin.sum_univ_two`** changes the **goal**: the lemma is `∑ i, f i = f 0 + f 1` for `f : Fin 2 → β`, a
sum over `Fin 2` written out as two terms. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R13 · entry of a vector literal, by `simp`** changes the **goal**. `simp` uses `Matrix.cons_val_zero`,
`Matrix.cons_val_one`, … as in R4. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b] 1)` | `⊢ P b` |

**W3.** `B *ᵥ ![1, 2] = ![4, 17]`. After `ext i` (R9) and `fin_cases i` (R7), the first goal is

```lean-goal
⊢ (B *ᵥ ![1, 2]) ((fun i => i) ⟨0, ⋯⟩) = ![4, 17] ((fun i => i) ⟨0, ⋯⟩)
```

`simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]` does R2, R10–R13 and stops at the arithmetic;
`norm_num` (R5) closes it:

```lean-goal
⊢ 2 + 2 = 4
⊢ 7 + 5 * 2 = 17
```

---

## Part 5 · `adjugate_two`

Statement: for all real `a b c d`, `!![a, b; c, d] * !![d, -b; -c, a] = (a * d - b * c) • 1`: a matrix times
its adjugate is its determinant times the identity. Reduce to 4 entries; expand each product entry into a
sum of two terms; the right side is an entry of a scaled identity; finish with algebra.

**R14 · `Matrix.mul_apply`** changes the **goal**: an entry of a product is a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (as in R11),
`(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R15 · `Matrix.smul_apply`, then `smul_eq_mul`** changes the **goal**: an entry of `c • M` is `c • M i j`
(scalar times a number), and `smul_eq_mul` turns that `•` into `*`. `simp` applies both by itself.
Placeholders: `{α : Type} [Mul α] (c : α) (M : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2)`.

| Before | After `rw [Matrix.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • M) i j)` | `⊢ P (c • M i j)` | `⊢ P (c * M i j)` |

**R16 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix
are `1` on the diagonal and `0` off it. `simp` applies them by itself. Placeholders:
`(1 : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R17 · `ring`** **closes** an equation that holds in every commutative ring, with variables. It does not
use hypotheses. Use it after `simp` when the entry goal has letters, where `norm_num` may fail.

| Before | After |
|---|---|
| `⊢ x * w + y * -z = x * w - y * z` | no goals |

**W4.** `!![x, 0; 0, y] * !![y, 0; 0, x] = (x * y) • 1`: R6, R7, then
`simp [Matrix.mul_apply, Fin.sum_univ_two]` (R14, R12; R4, R15, R16 happen inside `simp`). `simp` closes the
three entries that are `0 = 0` or trivial and leaves

```lean-goal
⊢ y * x = x * y
```

which `ring` (R17) closes. Use `<;>` or `all_goals` so the finishing tactic runs on whatever is left.

---

## Traps

- `rfl` does not do arithmetic in `ℝ`: real numbers are not computed by unfolding, so `(1 : ℝ) * 1 + 2 * 1 = 3`
  needs `norm_num`. `rfl` is fine for *reading* entries (R1, Parts 1 and 3); use `simp` + `norm_num` when the
  entry is a sum or product of numbers (Parts 2 and 4). `decide` does not work on `ℝ` either.
- `ext i j` is for matrices, `ext i` for vectors (`Fin 2 → ℝ`, including `A *ᵥ v` and `![…]`).
- `t1 ; t2` and a new line run `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.
- If `simp` already closed a goal, a following `norm_num` on its own line fails with "no goals". Inside
  `<;>` or `all_goals` it simply has nothing to do.
- Without `Matrix.mulVec`, `dotProduct`, `Fin.sum_univ_two` (or `Matrix.mul_apply`, `Fin.sum_univ_two`) in
  the `simp` set, `simp` leaves `*ᵥ` or a `∑` unexpanded and `norm_num`/`ring` then fail.
- `ᵀ` and `*ᵥ` are notations from `open Matrix`; the problem opens it inside its spec region.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| read an entry of a literal | `rfl` | R1 |
| unfold `A` | `simp [A, …]` | R2 |
| 2×2 determinant | `simp [A, Matrix.det_fin_two]` | R3, R4 |
| numeric goal | `norm_num` | R5 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R6, R7 |
| `Mᵀ i j = M j i` | by `rfl`, or `Matrix.transpose_apply` | R8 |
| vector equation → 2 entries | `ext i; fin_cases i` | R9, R7 |
| entry of `M *ᵥ v` | `simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]` | R10–R13 |
| entry of `M * N` | `simp [Matrix.mul_apply, Fin.sum_univ_two]` | R14, R12 |
| entry of `c • 1` | `simp` (automatic) | R15, R16 |
| algebra with variables | `ring` | R17 |
| run on every goal | `<;>`, `all_goals` | TACTIC_STATES |
| see the state | infoview | |
