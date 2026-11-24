# E110 · The unitary group: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices over `ℂ`, the conjugate
transpose `Mᴴ` and `star`, the unitary group `Matrix.unitaryGroup` as a `Submonoid`, and proving a 2×2
matrix equation entry by entry.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a whole goal the step leaves untouched.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 matrices with complex entries. Rows and columns are indexed by `Fin 2 = {0, 1}`; a matrix *is* a function `Fin 2 → Fin 2 → ℂ` |
| `Matrix n n ℂ` with `[Fintype n] [DecidableEq n]` | square matrices indexed by any finite type `n` whose elements can be compared for equality (needed to define the identity `1` and finite sums) |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` (`;` separates rows) |
| `![a, b]` | the vector `(a, b)`, a function `Fin 2 → α` |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `M * N` (matrices) | the matrix product, $(MN)_{ik} = \sum_j M_{ij} N_{jk}$ (R6) |
| `∑ j, f j` | `Finset.sum Finset.univ f`: the sum of `f j` over all `j` of the (finite) index type (R6, R7) |
| `1` (a matrix) | the identity matrix: `1 i i = 1`, `1 i j = 0` for `i ≠ j` |
| `star z` (`z : ℂ`) | the complex conjugate $\bar z$. After `simp` it prints as `(starRingEnd ℂ) z` |
| `star M` (a matrix) | the conjugate transpose of `M`, the same thing as `Mᴴ` (R2) |
| `Mᴴ` | `Matrix.conjTranspose M`: `Mᴴ i j = star (M j i)`. Typed `\^H`; prints this way under `open Matrix` |
| `unitaryGroup n ℂ` | `Matrix.unitaryGroup n ℂ`: the set of `U` with `U * star U = 1`, packaged as a `Submonoid (Matrix n n ℂ)` |
| `Submonoid M` | a subset of a monoid `M` (a type with an associative `*` and a unit `1`) that contains `1` and is closed under `*`; `x ∈ S` is membership |
| `I` | `Complex.I`, the imaginary unit $i$ (shown bare under `open Complex`; used in Part W) |
| `inst✝ : Fintype n` | an unnamed instance hypothesis: the `[Fintype n]` binder of the statement |
| `case a` | a goal created by `apply` for an unnamed premise of the lemma (R12) |
| `e.mp`, `e.mpr` (`e : P ↔ Q`) | the two directions of an iff: `e.mp : P → Q`, `e.mpr : Q → P` (R14) |
| `v ᵥ* M` | `Matrix.vecMul v M`, row vector `v` times matrix `M` (W2) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case «0».«1»` | the goal for entry (0, 1) |

---

## Part 1 · `X_unitary`

Statement: `X ∈ Matrix.unitaryGroup (Fin 2) ℂ` for Pauli `X = !![0, 1; 1, 0]`, i.e. $X X^\dagger = 1$
($X^\dagger$ is the conjugate transpose). Turn the membership into an equation, split it into four entries,
and let `simp` compute each entry.

### Unitary membership → a matrix equation

**R1 · `rw [Matrix.mem_unitaryGroup_iff]`** changes the **goal**: membership becomes an equation. The lemma
is `Matrix.mem_unitaryGroup_iff : A ∈ unitaryGroup n α ↔ A * star A = 1`. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ M ∈ unitaryGroup (Fin 2) ℂ` | `⊢ M * star M = 1` |

**R2 · `rw [Matrix.star_eq_conjTranspose]`** changes the **goal**: `star M` is written as the conjugate
transpose `Mᴴ`, which has an entry lemma (R8). The lemma is `star M = Mᴴ`. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star M)` | `⊢ P Mᴴ` |

### Matrix equation → entries

**R3 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when
every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R4 · `fin_cases i`** changes the **goal list and the context**. `i` leaves the context, and there is one
goal for each value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`. `fin_cases i <;> fin_cases j` gives all four
entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

### Evaluating an entry

One `simp [X, Matrix.mul_apply, Fin.sum_univ_two]` does R5–R11 on every entry. R5–R7 are the ones you must
name: `X` (a definition `simp` does not unfold on its own) and the two product lemmas (without them `simp`
stops at `v ᵥ* Mᴴ`, W2). R8–R11 are simp lemmas that `simp` applies by itself.

**R5 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. Placeholders: `D`
defined by `def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]`.

| Before | After |
|---|---|
| `⊢ P D` | `⊢ P !![1, 2; 3, 4]` |

**R6 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a
commutative `+` with `0`, as `ℂ` does), `(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R7 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms,
$\sum_{i \in \{0,1\}} f(i) = f(0) + f(1)$. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R8 · `Matrix.conjTranspose_apply`** changes the **goal**: entry `(i, j)` of `Mᴴ` becomes the conjugate of
entry `(j, i)`. The lemma is `Mᴴ i j = star (M j i)`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (Mᴴ i j)` | `⊢ P (star (M j i))` |

**R9 · entry of a literal** changes the **goal**. `simp` uses `Matrix.of_apply` and `Matrix.cons_val_…` for
this; you never name them. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 0 1)` | `⊢ P b` |

**R10 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix
`1` become `1` on the diagonal and `0` elsewhere. Placeholders: `(1 : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R11 · `rw [star_neg, star_one]`** changes the **goal**: the conjugate of an integer numeral is the numeral.
The lemmas are `star_neg : star (-a) = -star a`, `star_one : star 1 = 1`, `star_zero : star 0 = 0`.
Placeholders: none beyond `P : ℂ → Prop`. These are why `X`, `Z` (integer entries) need no conjugation work.

| Before | After |
|---|---|
| `⊢ P (star (-1))` | `⊢ P (-1)` |

**W1 (on the phase gate `S = !![1, 0; 0, I]`, not the exercise's).** R1, R2 in one `rw`, then R3, R4,
then `simp [S, Matrix.mul_apply, Fin.sum_univ_two]` closes all four entries:

```lean-goal
⊢ S ∈ unitaryGroup (Fin 2) ℂ
⊢ S * Sᴴ = 1
⊢ (S * Sᴴ) i j = 1 i j
```

**W2: plain `simp [S]` gets stuck.** Without R6, R7 `simp` rewrites the product row by row into
`Matrix.vecMul` and cannot open `Mᴴ` from there:

```lean-goal
⊢ (![1, 0] ᵥ* !![1, 0; 0, I]ᴴ) 0 = 1
⊢ (![0, I] ᵥ* !![1, 0; 0, I]ᴴ) 1 = 1
```

`simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]` rescues it after the fact; naming R6, R7 from the
start avoids it.

---

## Part 2 · `Z_unitary`

Statement: `Z ∈ Matrix.unitaryGroup (Fin 2) ℂ` for Pauli `Z = !![1, 0; 0, -1]`. The same entries as Part 1:
R1, R2, R3, R4, then `simp` with `Z` and R6, R7. The entry `star (-1)` is handled by R11.

---

## Part 3 · `XZ_unitary`

Statement: `X * Z ∈ Matrix.unitaryGroup (Fin 2) ℂ`. No matrix computation: the unitary group is a
`Submonoid`, so it is closed under `*`, and Parts 1–2 are the two memberships.

**R12 · `Submonoid.mul_mem`** changes the **goal list**. The lemma is
`Submonoid.mul_mem (S : Submonoid M) : x ∈ S → y ∈ S → x * y ∈ S`. `apply` turns the goal into the two
memberships; as a term, `Submonoid.mul_mem _ hx hy` proves it directly (`_` lets Lean find `S` from the goal).
Placeholders: `{M : Type} [Monoid M] (S : Submonoid M) (x y : M)`. `Matrix n n ℂ` is a monoid under matrix `*`,
and `Matrix.unitaryGroup n ℂ : Submonoid (Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ x * y ∈ S` | `⊢ x ∈ S`, `⊢ y ∈ S` |

**W3.** `Submonoid.mul_mem _ (Submonoid.mul_mem _ hS hS) hS : S * S * S ∈ unitaryGroup (Fin 2) ℂ`:
nest R12 for longer circuits (`*` groups to the left).

---

## Part 4 · `conjTranspose_mul_self`

Statement: for any finite index type `n` and `U : Matrix n n ℂ`, `U ∈ unitaryGroup n ℂ → Uᴴ * U = 1`
($U^\dagger U = 1$). The size is unknown, so no `ext`/`fin_cases`: rewrite `Uᴴ` back into `star U` and use the
other characterization of the unitary group.

**R13 · `rw [← Matrix.star_eq_conjTranspose]`** changes the **goal**: R2 right to left, `Mᴴ` becomes
`star M`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)` (any square index type works the same way).

| Before | After |
|---|---|
| `⊢ P Mᴴ` | `⊢ P (star M)` |

**R14 · `Matrix.mem_unitaryGroup_iff'`, used with `.mp`** changes the **context** (with `have`) or closes the
goal (with `exact`). The lemma is `A ∈ unitaryGroup m α ↔ star A * A = 1`, the "left inverse" form of R1. For
an iff `e : P ↔ Q`, `e.mp : P → Q` and `e.mpr : Q → P`. Placeholders:
`{m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : A ∈ unitaryGroup m ℂ)`, `G : Prop`.

| Before | After `have h := Matrix.mem_unitaryGroup_iff'.mp hA` |
|---|---|
| `⊢ G` | `h : star A * A = 1 ⊢ G` |

---

## Traps

- `simp` does not compute `!![…]ᴴ` as a literal. If the entry goals still show `ᵥ*` or `ᴴ`, you forgot
  `Matrix.mul_apply` and `Fin.sum_univ_two` (W2).
- `simp [X]` needs the name `X`: a `def` is not unfolded by `simp` unless you list it (R5).
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals` (TACTIC_STATES).
- `star U` and `Uᴴ` are equal *by definition* but are not the same text. `exact` compares up to definitions,
  so `exact Matrix.mem_unitaryGroup_iff'.mp hU` is accepted even before R13; `rw [h]` and `simp [h]` match
  text, so with `h : star U * U = 1` they fail on a goal that says `Uᴴ * U` until you apply R13.
- `Submonoid.mul_mem` takes the submonoid explicitly: write `Submonoid.mul_mem _ hx hy`, not
  `Submonoid.mul_mem hx hy`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unitary → equation `U * Uᴴ = 1` | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` | R1, R2 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R3, R4 |
| evaluate the entries | `simp [name, Matrix.mul_apply, Fin.sum_univ_two]` | R5–R11 |
| `Mᴴ i j` | `Matrix.conjTranspose_apply` (simp does it) | R8 |
| conjugate of a numeral | `star_neg`, `star_one`, `star_zero` (simp does it) | R11 |
| product of unitaries | `Submonoid.mul_mem _ hx hy` | R12 |
| `Mᴴ → star M` | `rw [← Matrix.star_eq_conjTranspose]` | R13 |
| unitary → `star U * U = 1` | `Matrix.mem_unitaryGroup_iff'.mp hU` | R14 |
| `simp` stuck at `v ᵥ* M` | `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]` | W2 |
| see the state | infoview | |
