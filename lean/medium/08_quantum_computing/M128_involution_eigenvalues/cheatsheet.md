# M128 · Eigenvalues of involutions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw`, `rw … at h`, `have`, `exact`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (matrices over `ℂ`, `star`, `Mᴴ`, unitary group)
helps but is not needed. **New here:** Mathlib's matrix-times-vector `*ᵥ`, scalar action `•` on vectors,
the dot product `⬝ᵥ` and the inner product `star v ⬝ᵥ w`, `Matrix.IsHermitian`, the lemmas `smul_eq_zero`
and `mul_eq_zero`, and the tactics `rcases … with h1 | h2`, `left`/`right`, `linear_combination`, `simpa`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Ring R]` is a
  requirement on `R` (a *type class*). Each entry says which familiar types meet it.
- `rw [lemma] at h` does to hypothesis `h` what `rw [lemma]` does to the goal; the entries R1, R2 show it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

Throughout, `n : Type` with `[Fintype n]` (finitely many elements, so sums over `n` exist) and
`[DecidableEq n]` (equality of indices can be tested, needed for the identity matrix `1`). Think
`n = Fin d` for a `d`-level system.

| You see | It means |
|---|---|
| `Matrix n n ℂ` | `n × n` complex matrices; `U i j` is the entry in row `i`, column `j` |
| `n → ℂ` | a column vector `v` with entries `v i`; `0` is the zero vector |
| `U *ᵥ v` | `Matrix.mulVec`: matrix times column vector, $(Uv)_i = \sum_j U_{ij} v_j$ |
| `U *ᵥ V *ᵥ v` | `U *ᵥ (V *ᵥ v)`: `*ᵥ` groups to the right |
| `(U * V) *ᵥ v` | the matrix product `U * V`, then applied to `v` |
| `μ • v` | scalar `μ : ℂ` times every entry of `v` |
| `μ • U *ᵥ v` | `μ • (U *ᵥ v)`, not `(μ • U) *ᵥ v` (they are equal, but `rw` sees different terms) |
| `U *ᵥ μ • v` | `U *ᵥ (μ • v)`: `•` and `*ᵥ` have the same precedence and group to the right |
| `u ⬝ᵥ w` | `dotProduct`: $\sum_i u_i w_i$, **no** conjugation |
| `star v` | the entrywise complex conjugate of the vector `v` |
| `star v ⬝ᵥ w` | the inner product $\langle v, w\rangle = \sum_i \overline{v_i}\, w_i$ |
| `u ⬝ᵥ A *ᵥ w` | `u ⬝ᵥ (A *ᵥ w)` |
| `u ᵥ* A` | `Matrix.vecMul`: row vector times matrix, $(uA)_j = \sum_i u_i A_{ij}$ |
| `u ᵥ* A ⬝ᵥ w` | `(u ᵥ* A) ⬝ᵥ w` |
| `2 * star v ⬝ᵥ w` | `2 * (star v ⬝ᵥ w)`: `⬝ᵥ` binds tighter than `*` |
| `-(star v ⬝ᵥ w)` | minus the complex number `star v ⬝ᵥ w`; `-w` is the vector with entries `-(w i)` |
| `star U`, `Uᴴ` | the conjugate transpose $U^\dagger$: `Uᴴ i j = conj (U j i)` |
| `U.IsHermitian` | `Matrix.IsHermitian U`, by definition `Uᴴ = U` |
| `unitaryGroup n ℂ` | the unitary matrices: `U ∈ unitaryGroup n ℂ ↔ U * star U = 1` |
| `1` (a matrix) | the identity matrix |
| `v ≠ 0` | `¬(v = 0)`: `v` is not the zero vector |
| `case inl`, `case inr` | the left / right case of an `∨` after `rcases` (`inl.inl` after a second split) |
| `inst✝ : Fintype n` | an unnamed instance argument of the theorem; you never refer to it |
| `this : …` | the fact added by a `have : …` with no name |

---

## Part 1 · `herm_unitary_sq`

Statement: a Hermitian (`Uᴴ = U`) unitary (`U U† = 1`) matrix squares to the identity, `U * U = 1`. The
whole proof rewrites the hypothesis `hU` until it *is* the goal.

**R1 · `rw [Matrix.mem_unitaryGroup_iff] at hM`** changes the **context**: membership in the unitary group
becomes the equation it means. Lemma: `A ∈ unitaryGroup n α ↔ A * star A = 1` (`rw` can use an `↔`).
Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `hM : M ∈ unitaryGroup n ℂ ⊢ G` | `hM : M * star M = 1 ⊢ G` |

**R2 · `rw [Matrix.star_eq_conjTranspose] at hM`** changes the **context** (or, without `at`, the goal):
`star M` is written as the conjugate transpose `Mᴴ`. Lemma: `star M = Mᴴ`. Placeholders:
`(M : Matrix n n ℂ)`, `(Q : Matrix n n ℂ → Prop)`.

| Before | After |
|---|---|
| `hM : Q (star M) ⊢ G` | `hM : Q Mᴴ ⊢ G` |

**R3 · `rw [hA.eq]`** changes the **goal** (or, with `at h`, a hypothesis). For `hA : A.IsHermitian`, the term
`hA.eq` (short for `Matrix.IsHermitian.eq hA`) is the equation `Aᴴ = A`. Placeholders:
`(A : Matrix n n ℂ) (hA : A.IsHermitian)`. Used again in Part 3.

| Before | After |
|---|---|
| `⊢ Q Aᴴ` | `⊢ Q A` |

---

## Part 2 · `involution_eigenvalues`

Statement: if `U * U = 1` and `v ≠ 0` is an eigenvector, `U *ᵥ v = μ • v`, then `μ = 1 ∨ μ = -1`. Math:
$v = U^2 v = \mu^2 v$, so $(\mu^2 - 1) v = 0$; since $v \ne 0$, $\mu^2 = 1$, i.e. $(\mu-1)(\mu+1) = 0$.

### Matrix times vector

**R4 · `rw [Matrix.mulVec_mulVec]`** changes the **goal**: applying `N` then `M` is applying `M * N`. Lemma:
`M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`. Placeholders: `{n : Type} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ)`.
`rw [← Matrix.mulVec_mulVec]` goes the other way (W1).

| Before | After |
|---|---|
| `⊢ P (M *ᵥ N *ᵥ v)` | `⊢ P ((M * N) *ᵥ v)` |

**R5 · `rw [Matrix.one_mulVec]`** changes the **goal**: the identity matrix does nothing. Lemma:
`1 *ᵥ v = v`. Placeholders: `[Fintype n] [DecidableEq n] (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (1 *ᵥ v)` | `⊢ P v` |

**R6 · `rw [Matrix.mulVec_smul]`** changes the **goal**: a scalar factor comes out of a matrix-vector
product. Lemma: `M *ᵥ (b • v) = b • (M *ᵥ v)`, printed `M *ᵥ b • v = b • M *ᵥ v`. Placeholders:
`(M : Matrix n n ℂ) (b : ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ b • v)` | `⊢ P (b • M *ᵥ v)` |

### Scalars acting on vectors

For R7–R9 take `R = ℂ` (the scalars) and `V = n → ℂ` (the vectors); those meet every bracket below.

**R7 · `rw [smul_smul]`** changes the **goal**: two scalings become one. Lemma: `a • b • x = (a * b) • x`
(`•` groups to the right). Placeholders: `{R V : Type} [Monoid R] [MulAction R V] (a b : R) (x : V)`.

| Before | After |
|---|---|
| `⊢ P (a • b • x)` | `⊢ P ((a * b) • x)` |

**R8 · `rw [sub_smul]`** changes the **goal**: distributes a difference of scalars. Lemma:
`(r - s) • x = r • x - s • x`. Placeholders: `[Ring R] [AddCommGroup V] [Module R V] (r s : R) (x : V)`
(`Module R V`: `V` is a vector space over `R`).

| Before | After |
|---|---|
| `⊢ P ((r - s) • x)` | `⊢ P (r • x - s • x)` |

**R9 · `rw [one_smul]`** changes the **goal**. Lemma: `1 • x = x`. Placeholders:
`[Monoid R] [MulAction R V] (x : V)`.

| Before | After |
|---|---|
| `⊢ P (1 • x)` | `⊢ P x` |

**R10 · `rw [sub_self]`** changes the **goal**. Lemma: `a - a = 0`. Placeholders: `{V : Type} [AddGroup V]
(a : V)`; vectors `n → ℂ` qualify. If the goal becomes `0 = 0`, `rw` closes it itself (it tries `rfl`).

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

### Products that vanish, and case splits

**R11 · `smul_eq_zero.mp hx`** changes the **context** (via `have` or `rcases`). Lemma:
`r • x = 0 ↔ r = 0 ∨ x = 0` (true over a field such as `ℂ`); `.mp` is the `→` direction. Placeholders:
`(r : ℂ) (x : n → ℂ) (hx : r • x = 0)`.

| Before | After `have h2 := smul_eq_zero.mp hx` |
|---|---|
| `hx : r • x = 0 ⊢ G` | `h2 : r = 0 ∨ x = 0 ⊢ G` |

**R12 · `rcases hAB with h1 | h2`** changes the **goal list and the context**: one goal per side of an `∨`,
each with that side as a hypothesis (`hAB` itself is gone). `rcases e with h1 | h2` also works on a term `e`
such as `smul_eq_zero.mp hx`, so R11 and R12 combine in one line. Placeholders: `(A B G : Prop) (hAB : A ∨ B)`.

| Before | After |
|---|---|
| `hAB : A ∨ B ⊢ G` | `h1 : A ⊢ G` (case `inl`), `h2 : B ⊢ G` (case `inr`) |

Work on the two goals with `·` (TACTIC_STATES, "Structure").

**R13 · `linear_combination e`** **closes** an equation `a = b` in a commutative ring when
`(a - b) - (lhs_e - rhs_e)` is `0` by `ring`; `e` is a hypothesis, or `c * h`, `-h`, `h1 + h2`. Use it to
factor (`μ * μ - 1 = 0` ⟹ `(μ - 1) * (μ + 1) = 0`) and to solve a linear equation (`μ - 1 = 0` ⟹ `μ = 1`).
Placeholders: `{α : Type} [CommRing α] (a b : α)`; `ℂ` qualifies.

| Before | After |
|---|---|
| `h : a * a - b * b = 0 ⊢ (a - b) * (a + b) = 0` | no goals |

**R14 · `mul_eq_zero.mp hab`** changes the **context**. Lemma: `a * b = 0 ↔ a = 0 ∨ b = 0` (no zero
divisors; `ℂ`, `ℝ`, `ℤ` qualify). Placeholders: `(a b : ℂ) (hab : a * b = 0)`. Split the result with R12.

| Before | After `have h2 := mul_eq_zero.mp hab` |
|---|---|
| `hab : a * b = 0 ⊢ G` | `h2 : a = 0 ∨ b = 0 ⊢ G` |

**R15 · `left` / `right`** change the **goal**: to prove `A ∨ B`, commit to one side. Placeholders:
`(A B : Prop)`.

| Before | After `left` | After `right` |
|---|---|---|
| `⊢ A ∨ B` | `⊢ A` | `⊢ B` |

**R16 · `exact absurd ha hna`** **closes** any goal from a contradiction. `absurd : a → ¬a → b`.
`v ≠ 0` is `¬(v = 0)`, so in the `v = 0` case `exact absurd h hv` finishes. Placeholders:
`(A G : Prop) (ha : A) (hna : ¬A)`.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ G` | no goals |

### Worked combinations (W1, W3)

**W1: an eigenvector of `M` is an eigenvector of `M * M`.** `h : M *ᵥ v = c • v`. Apply R4 backwards,
`rw [h]`, R6, `rw [h]`, R7; the last `rw` closes `(c * c) • v = (c * c) • v`:

```lean-goal
⊢ (M * M) *ᵥ v = (c * c) • v
⊢ M *ᵥ M *ᵥ v = (c * c) • v
⊢ M *ᵥ c • v = (c * c) • v
⊢ c • M *ᵥ v = (c * c) • v
⊢ c • c • v = (c * c) • v
```

`rw [h]` rewrites the first `M *ᵥ v` it finds, here the inner one; after R6 a new `M *ᵥ v` appears and the
second `rw [h]` takes it.

**W3: an idempotent scalar, `z * z = z`, is `0` or `1`.** Factor with R13
(`h2 : z * (z - 1) = 0 := by linear_combination h`), split with R14 + R12, then R15 in each case and R13
for `z - 1 = 0 ⟹ z = 1`:

```lean-goal
⊢ z = 0 ∨ z = 1
```

---

## Part 3 · `eigvec_orth`

Statement: for Hermitian `U`, a `+1` eigenvector `v` and a `-1` eigenvector `w` are orthogonal:
`star v ⬝ᵥ w = 0`, i.e. $\langle v, w\rangle = 0$. Math: $\langle v, Uw\rangle = \langle U^\dagger v, w\rangle
= \langle Uv, w\rangle$; the left side is $-\langle v, w\rangle$ (by `hw`), the right side is
$\langle v, w\rangle$ (by `hv`), so $2\langle v, w\rangle = 0$.

**R17 · `rw [Matrix.star_mulVec]`** changes the **goal**: conjugating a column vector `M v` gives the row
vector $\bar v M^\dagger$. Lemma: `star (M *ᵥ v) = star v ᵥ* Mᴴ`. Placeholders:
`[Fintype n] (M : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R18 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**: a matrix moves from the right factor of a dot
product to the left one, $u \cdot (Aw) = (uA) \cdot w$. Lemma: `u ⬝ᵥ (A *ᵥ w) = (u ᵥ* A) ⬝ᵥ w`. Placeholders:
`(u w : n → ℂ) (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ A *ᵥ w)` | `⊢ P (u ᵥ* A ⬝ᵥ w)` |

**R19 · `rw [dotProduct_neg]`** changes the **goal**. Lemma: `u ⬝ᵥ -w = -(u ⬝ᵥ w)`. Placeholders:
`(u w : n → ℂ)`. Unlike R17 and R18, this lemma lives in the root namespace: write `dotProduct_neg`.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ -w)` | `⊢ P (-(u ⬝ᵥ w))` |

**R20 · `simpa using e`** **closes** the goal: it runs `simp` on both `e` and the goal and then uses `e`.
`simp` rewrites `3 * x = 0` to `x = 0` in `ℂ` (by `mul_eq_zero` and `3 ≠ 0`). Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `h : 3 * x = 0 ⊢ x = 0` | no goals |

R3 is used here too, on the right side of the fact in step 1 of the skeleton; R13 is used with the coefficient
`-1` (`linear_combination -h`).

### Worked combinations (W2, W4)

**W2: the adjoint moves across the inner product** (any `M`, no Hermitian needed):
`star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w)`. R17 rewrites the left side, R18 the right side, and the two
sides become the same term:

```lean-goal
⊢ star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w
⊢ star v ᵥ* Mᴴ ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w
```

**W4: from `h : x = 3 * x` to `x = 0`.** `x - 3x = -2x`, so `2 * x = 0` is `-1` times `h`:
`have h2 : (2 : ℂ) * x = 0 := by linear_combination -h` (R13), then `simpa using h2` (R20):

```lean-goal
⊢ x = 0
```

---

## Traps

- `try?` is banned here: it would find Part 1's three-rewrite unwrapping for you. Do it by hand with
  R1, R2, R3.
- Printing hides parentheses: `b • M *ᵥ v` is `b • (M *ᵥ v)`, `U *ᵥ μ • v` is `U *ᵥ (μ • v)`,
  `u ⬝ᵥ A *ᵥ w` is `u ⬝ᵥ (A *ᵥ w)` and `2 * star v ⬝ᵥ w` is `2 * (star v ⬝ᵥ w)`. When you
  write a `have`, put the parentheses in; Lean drops them when it prints.
- `u ⬝ᵥ w` has no conjugate. The inner product is `star v ⬝ᵥ w`; R17 is how `star` gets past `*ᵥ`.
- `rw [h]` rewrites every copy of the left side of `h` that it sees in one pass, starting from the first
  match. In `U *ᵥ U *ᵥ v` only the inner `U *ᵥ v` matches `h : U *ᵥ v = μ • v`; rewrite again after R6.
- `rw [hU]` with `hU : U * U = 1` needs `U * U` literally: get it with R4 first.
- `have h2 : (μ * μ - 1) • v = 0` needs the parentheses: `•` binds tighter than `-`, so `μ * μ - 1 • v`
  is `μ * μ - (1 • v)`, a scalar minus a vector (a type error).
- `linear_combination` proves equalities only, and needs the right coefficient: `-h`, not `h`, when the sign
  is flipped (W4). If it fails, it shows the `ring` goal it could not close.
- In `have : 2 * (star v ⬝ᵥ w) = 0` the numeral `2` gets the type `ℂ` from `star v ⬝ᵥ w`. A statement
  made of numerals only (`2 * 1 = 2`) is read in `ℕ`; write `(2 : ℂ)` there.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unitary → equation, in a hypothesis | `rw [Matrix.mem_unitaryGroup_iff] at hU` | R1 |
| `star M` → `Mᴴ` | `rw [Matrix.star_eq_conjTranspose]` | R2 |
| Hermitian: `Uᴴ` → `U` | `rw [hH.eq]` | R3 |
| `M *ᵥ (N *ᵥ v)` ↔ `(M * N) *ᵥ v` | `rw [Matrix.mulVec_mulVec]` / `rw [← Matrix.mulVec_mulVec]` | R4 |
| `1 *ᵥ v` → `v` | `rw [Matrix.one_mulVec]` | R5 |
| scalar out of `M *ᵥ (b • v)` | `rw [Matrix.mulVec_smul]` | R6 |
| `a • b • x` → `(a * b) • x` | `rw [smul_smul]` | R7 |
| `(r - s) • x`, `1 • x`, `a - a` | `rw [sub_smul]`, `rw [one_smul]`, `rw [sub_self]` | R8–R10 |
| `r • x = 0` → `r = 0 ∨ x = 0` | `smul_eq_zero.mp h` | R11 |
| `a * b = 0` → `a = 0 ∨ b = 0` | `mul_eq_zero.mp h` | R14 |
| case split on `A ∨ B` | `rcases h with h1 \| h2` | R12 |
| prove `A ∨ B` | `left` / `right` | R15 |
| ring consequence of hypotheses | `linear_combination h`, `linear_combination -h` | R13 |
| `h : A`, `hn : ¬A` (or `≠`) | `exact absurd h hn` | R16 |
| `star (M *ᵥ v)` → `star v ᵥ* Mᴴ` | `rw [Matrix.star_mulVec]` | R17 |
| `u ⬝ᵥ (A *ᵥ w)` → `(u ᵥ* A) ⬝ᵥ w` | `rw [Matrix.dotProduct_mulVec]` | R18 |
| `u ⬝ᵥ -w` → `-(u ⬝ᵥ w)` | `rw [dotProduct_neg]` | R19 |
| `c * x = 0` with numeral `c ≠ 0` → `x = 0` | `simpa using h` | R20 |
| see the state | infoview | |
