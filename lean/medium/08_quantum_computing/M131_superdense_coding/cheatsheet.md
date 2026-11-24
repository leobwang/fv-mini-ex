# M131 · Superdense coding: four orthonormal messages: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw`, `simp`, `fin_cases`, `<;>`, `ring`, `norm_num`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices and vectors (`Matrix`,
`*ᵥ`, `ᵥ*`, `⬝ᵥ`, `ᴴ`, `trace`), the Kronecker product `⊗ₖ`, finite sums `∑`, complex conjugation
`star`, real numbers and `Real.sqrt` cast into `ℂ`, and physlib's maximally entangled state `Ket.MES`.

**The physics.** Let `d` be a finite index type with `n = Fintype.card d` elements (n ≥ 1). The maximally
entangled state on `d × d` is $\Phi = n^{-1/2}\sum_{i} |i, i\rangle$, i.e. amplitude
$\Phi(i, j) = n^{-1/2}$ if $i = j$ and $0$ otherwise. Alice holds the first factor and applies a matrix
$P$; the result is $(P \otimes 1)\Phi$. The inner product is $\langle v, w\rangle = \sum_x \overline{v_x}\, w_x$.
The exercise shows $\langle (P\otimes 1)\Phi, (Q\otimes 1)\Phi\rangle = \operatorname{tr}(P^\dagger Q)/n$
($P^\dagger$ = conjugate transpose), via the milestone
$\langle \Phi, (A \otimes B)\Phi\rangle = \frac1n \sum_{i,j} A_{ij} B_{ij}$. For one qubit (`d = Fin 2`,
$n = 2$) with $X = \begin{psmallmatrix}0&1\\1&0\end{psmallmatrix}$,
$Z = \begin{psmallmatrix}1&0\\0&-1\end{psmallmatrix}$, the four encodings $Z^{b_1}X^{b_2}$,
$b_1, b_2 \in \{0, 1\}$, satisfy $\operatorname{tr}(E_b^\dagger E_c) = 2\,\delta_{bc}$, so the four received
states are orthonormal and Bob can tell them apart: two classical bits through one qubit.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), gives the lemma's statement, lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype ι]` is a requirement
  on the type (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix d d ℂ` | complex matrices with rows and columns indexed by the type `d`; `M i j` is an entry |
| `[Fintype d]` | `d` is finite, so `∑ i, f i` over all of `d` makes sense (`Fin 2`, `Fin 2 × Fin 2` qualify) |
| `[DecidableEq d]` | `i = j` can be tested, needed for `if i = j then … else …` and for the identity `1` |
| `[Nonempty d]` | `d` has an element, so `n ≥ 1` and `1/√n` is meaningful |
| `Fintype.card d` | the number of elements `n` of `d`, a natural number |
| `noncomputable def` | a definition Lean cannot compile to code (it uses `Real.sqrt`); proofs about it work as usual |
| `Ket.MES d` | physlib's maximally entangled state Φ, of type `Ket (d × d)` (a unit vector) |
| `(Ket.MES d).vec` | its amplitude function `d × d → ℂ`; `.vec (i, j)` is Φ(i, j) (R1) |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: sum over every element of the index type; `Finset.univ` is "all of it" |
| `x_1`, `x✝` | names Lean invents for bound variables / unnamed hypotheses; you cannot type `x✝` |
| `v ⬝ᵥ w` | `dotProduct v w = ∑ i, v i * w i` (no conjugation) |
| `star v`, `star z` | entrywise complex conjugate of a vector / conjugate of a number |
| `star v ⬝ᵥ w` | the inner product ⟨v, w⟩ |
| `M *ᵥ v` | matrix times column vector, `(M *ᵥ v) i = ∑ j, M i j * v j` |
| `v ᵥ* M` | row vector times matrix, `(v ᵥ* M) j = ∑ i, v i * M i j` |
| `a ᵥ* B ⬝ᵥ c *ᵥ e` | `⬝ᵥ` binds weaker: `(a ᵥ* B) ⬝ᵥ (c *ᵥ e)` |
| `Mᴴ` | conjugate transpose: `Mᴴ i j = star (M j i)` |
| `A ⊗ₖ B` (needs `open scoped Kronecker`) | the Kronecker product `A ⊗ B`, a `Matrix (d × d) (d × d) ℂ`; rows and columns are indexed by pairs |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how `A ⊗ₖ B` prints: the Kronecker product, `(A ⊗ₖ B) (i, j) (k, l) = A i k * B j l` |
| `M.trace` | `Matrix.trace M = ∑ i, M i i` |
| `z⁻¹` | the inverse `1 / z` (`0⁻¹ = 0` in Lean) |
| `√x`, `↑x` | `Real.sqrt x` (a real), and a cast into the bigger type (ℕ → ℝ, ℝ → ℂ, `Fin 2` → ℕ) |
| `(↑√↑(Fintype.card d))⁻¹` | `((√(n : ℝ) : ℂ))⁻¹`, the complex number `1/√n` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z` |
| `1 i j` | entry of the identity matrix (R28) |
| `!![a, b; c, d]` | the 2×2 matrix with rows `a b` and `c d` |
| `b.1`, `b.2` for `b : Fin 2 × Fin 2` | the two bits of the message (`Prod.fst`, `Prod.snd`) |
| `M ^ k` (`k : ℕ`) | the matrix power `M * ⋯ * M`; `M ^ 0 = 1` |
| `↑b` for `b : Fin 2` | `Fin.val b`, the bit as a natural number `0` or `1`; `M ^ ↑b` is `1` or `M` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case «0».«1».«0».«1»` | the goal for `b₁ = 0, b₂ = 1, c₁ = 0, c₂ = 1` |

---

## Part 1 · `mes_expect` (MILESTONE)

Statement: for all `A B : Matrix d d ℂ`,
`star Φ ⬝ᵥ ((A ⊗ₖ B) *ᵥ Φ) = (n : ℂ)⁻¹ * ∑ i, ∑ j, A i j * B i j`. Prove it first; Part 2 ends with
`rw [mes_expect]`. It is not frozen: you may change or delete it. Two helper lemmas of your own make it
short: `MES_apply` (R1) and the `√n` fact (R2–R6).

### The amplitude of Φ and the `√n` factor

**R1 · `simp [Ket.MES]`** changes the **goal**: it unfolds physlib's definition
`vec := fun (i, j) ↦ if i = j then 1 / Real.sqrt (Fintype.card d) else 0` and rewrites `1 / x` as `x⁻¹`.
Placeholders: `{d : Type} [Fintype d] [Nonempty d] [DecidableEq d] (i j : d)`. State it once as your own lemma
(`MES_apply`) and use it with `simp only`, so the big `simp only` in step 3 does not have to unfold `Ket.MES`.

| Before | After |
|---|---|
| `⊢ P ((Ket.MES d).vec (i, j))` | `⊢ P (if i = j then (↑√↑(Fintype.card d))⁻¹ else 0)` |

**R2 · `rw [← mul_inv]`** changes the **goal**. `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`; `←` uses it right to left.
Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)` (commutative `*` with `⁻¹`; `ℂ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R3 · `rw [← Complex.ofReal_mul]`** changes the **goal**. `Complex.ofReal_mul : ↑(x * y) = ↑x * ↑y`
(cast ℝ → ℂ); right to left it moves `*` inside the cast, so a real lemma (R4) can fire.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R4 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. `Real.mul_self_sqrt : 0 ≤ x → √x * √x = x`, so
the goal is rewritten and a side goal `0 ≤ x` is added. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R5 · `Nat.cast_nonneg`** closes R4's side goal when `x = ↑n` is a cast natural:
`Nat.cast_nonneg (n : ℕ) : 0 ≤ (n : α)` in any ordered semiring `α` (`ℝ` qualifies). Pass it inline:
`rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (√↑n * √↑n)` | `⊢ P ↑n` |

**R6 · `rw [Complex.ofReal_natCast]`** changes the **goal**: `((n : ℝ) : ℂ) = (n : ℂ)`, a natural cast to ℝ
then to ℂ is the direct cast. `simp` applies it by itself. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑↑n` | `⊢ P ↑n` |

So the helper `(↑√↑n)⁻¹ * (↑√↑n)⁻¹ = (↑n : ℂ)⁻¹` is R2 → R3 → R4 with R5 → R6 (or `simp`).

### Everything to sums

`simp only [l₁, l₂, …]` applies the listed lemmas everywhere and repeatedly, so one `simp only` can do
R7–R15 together. Step through them one by one first.

**R7 · `dotProduct`** (unfold with `simp only [dotProduct]`) changes the **goal**:
`v ⬝ᵥ w = ∑ i, v i * w i`. Placeholders: `{ι : Type} [Fintype ι] (v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R8 · `Matrix.mulVec`** (`simp only [mulVec]`) changes the **goal**: entry `i` of `M *ᵥ v` is row `i` dotted
with `v`. Follow it with R7 again. Placeholders: `(M : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` |

**R9 · `Fintype.sum_prod_type`** changes the **goal**: `∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)`; a sum over
pairs becomes a double sum. Placeholders: `{α β : Type} [Fintype α] [Fintype β] (f : α × β → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R10 · `Matrix.kroneckerMap_apply`** changes the **goal**: an entry of the Kronecker product,
`(A ⊗ₖ B) (i, j) (k, l) = A i k * B j l`. Use `simp only`, which also beta-reduces the printed
`fun x1 x2 => x1 * x2`. Placeholders: `(A : Matrix α α ℂ) (B : Matrix β β ℂ) (i k : α) (j l : β)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (i, j) (k, l))` | `⊢ P (A i k * B j l)` |

**R11 · `Pi.star_apply`** changes the **goal**: `(star v) i = star (v i)`; conjugating a vector is
entrywise. Placeholders: `(v : ι → ℂ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (star v i)` | `⊢ P (star (v i))` |

### Collapsing the indicators

**R12 · `apply_ite star`, then `star_zero`** change the **goal**. `apply_ite f : f (if c then a else b) =
if c then f a else f b` for any function `f`; `star_zero : star 0 = 0`. Placeholders:
`(c : Prop) [Decidable c] (a : ℂ)`.

| Before | After `rw [apply_ite star]` | After `rw [star_zero]` |
|---|---|---|
| `⊢ P (star (if c then a else 0))` | `⊢ P (if c then star a else star 0)` | `⊢ P (if c then star a else 0)` |

**R13 · `mul_ite`, then `mul_zero`** change the **goal**. `mul_ite : a * (if c then b else e) =
if c then a * b else a * e`; `mul_zero : a * 0 = 0`. Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After `rw [mul_ite]` | After `rw [mul_zero]` |
|---|---|---|
| `⊢ P (a * if c then b else 0)` | `⊢ P (if c then a * b else a * 0)` | `⊢ P (if c then a * b else 0)` |

**R14 · `ite_mul`, then `zero_mul`** are the mirror image, for a factor on the right:
`(if c then a else e) * b = if c then a * b else e * b`, `0 * b = 0`.

| Before | After `rw [ite_mul]` | After `rw [zero_mul]` |
|---|---|---|
| `⊢ P ((if c then a else 0) * b)` | `⊢ P (if c then a * b else 0 * b)` | `⊢ P (if c then a * b else 0)` |

**R15 · `Finset.sum_ite_eq`, then `Finset.mem_univ`, `if_true`** change the **goal**: a sum of an indicator
keeps one term. `Finset.sum_ite_eq : ∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0`;
`Finset.mem_univ : i ∈ Finset.univ` is true and `if_true` drops the `if`. Placeholders:
`{ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ℂ)`.

| Before | After `simp only [Finset.sum_ite_eq]` | After `simp only [Finset.mem_univ, if_true]` |
|---|---|---|
| `⊢ P (∑ j, if i = j then f j else 0)` | `⊢ P (if i ∈ Finset.univ then f i else 0)` | `⊢ P (f i)` |

In the milestone both indicators have this orientation (`x = x_1`, bound variable on the right), so
`Finset.sum_ite_eq` is the right one; for `j = i` use `Finset.sum_ite_eq'`.

### The conjugate of a real scalar, then summand by summand

After R7–R15 one `star (↑√↑n)⁻¹` is left. R16 → R17 → R18 remove it.

**R16 · `rw [Complex.star_def]`** changes the **goal**: on `ℂ`, `star z` is `(starRingEnd ℂ) z`, the form the
conjugation lemmas are stated in. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star z)` | `⊢ P ((starRingEnd ℂ) z)` |

**R17 · `rw [map_inv₀]`** changes the **goal**: `f a⁻¹ = (f a)⁻¹` for a map `f` that preserves `*` and `1`
between fields (a *monoid-with-zero homomorphism*); conjugation is one. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) z⁻¹)` | `⊢ P ((starRingEnd ℂ) z)⁻¹` |

**R18 · `rw [Complex.conj_ofReal]`** changes the **goal**: the conjugate of a real cast is itself,
`conj ↑r = ↑r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R19 · `rw [Finset.mul_sum]`** changes the **goal**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Use it on both
sides so the two sides have the same double-sum shape. Placeholders: `(a : ℂ) (f : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R20 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**.
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` says the index sets agree,
and the `?_` is the summand goal. Nest it (`… fun i _ => Finset.sum_congr rfl fun j _ => ?_`) for a double sum.
Placeholders: `(f g : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

The summand goal then has `(↑√↑n)⁻¹` twice on the left and `(↑n)⁻¹` on the right: `rw [← h]` with your `√n`
helper `h` turns the right side into the `√` product, and `ring` closes (it treats `(↑√↑n)⁻¹` as an unknown).

---

## Part 2 · `sdc_overlap`

Statement: `star ((P ⊗ₖ 1) *ᵥ Φ) ⬝ᵥ ((Q ⊗ₖ 1) *ᵥ Φ) = (n : ℂ)⁻¹ * (Pᴴ * Q).trace`. A chain of `rw`s turns the
left side into `star Φ ⬝ᵥ (((Pᴴ * Q) ⊗ₖ 1) *ᵥ Φ)`, which is the milestone with `A = Pᴴ * Q`, `B = 1`.

### Moving `P ⊗ 1` across the inner product

**R21 · `rw [Matrix.star_mulVec]`** changes the **goal**: `star (M *ᵥ v) = star v ᵥ* Mᴴ`; the conjugate of a
column `M v` is the row `v̄ Mᴴ`. Placeholders: `{ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R22 · `rw [← Matrix.dotProduct_mulVec]`** changes the **goal**:
`Matrix.dotProduct_mulVec : v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w`; right to left it moves `A` from the row onto the
column. Placeholders: `(A : Matrix ι ι ℂ) (v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* A ⬝ᵥ w)` | `⊢ P (v ⬝ᵥ A *ᵥ w)` |

**R23 · `rw [Matrix.mulVec_mulVec]`** changes the **goal**: `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`.
Placeholders: `(M N : Matrix ι ι ℂ) (v : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ N *ᵥ v)` | `⊢ P ((M * N) *ᵥ v)` |

### Merging the Kronecker products

**R24 · `rw [Matrix.conjTranspose_kronecker]`** changes the **goal**: `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`.
Placeholders: `{α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B)ᴴ` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) Aᴴ Bᴴ)` |

**R25 · `rw [Matrix.conjTranspose_one]`** changes the **goal**: `1ᴴ = 1`. Placeholders:
`{β : Type} [DecidableEq β]`, the identity `(1 : Matrix β β ℂ)`.

| Before | After |
|---|---|
| `⊢ P 1ᴴ` | `⊢ P 1` |

**R26 · `rw [← Matrix.mul_kronecker_mul]`** changes the **goal**.
`Matrix.mul_kronecker_mul : (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'` (the mixed-product rule); right to left
it merges a product of two Kronecker products. Placeholders:
`[Fintype α] [Fintype β] (A B : Matrix α α ℂ) (A' B' : Matrix β β ℂ)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A A' * kroneckerMap (fun x1 x2 => x1 * x2) B B')` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) (A * B) (A' * B'))` |

**R27 · `rw [one_mul]`** changes the **goal**: `one_mul : 1 * a = a`, here on identity matrices.

| Before | After |
|---|---|
| `⊢ P (1 * 1)` | `⊢ P 1` |

Then `rw [mes_expect]` (Part 1) leaves `n⁻¹ * ∑ i, ∑ j, (Pᴴ * Q) i j * 1 i j = n⁻¹ * (Pᴴ * Q).trace`.

### Closing: identity entries and the trace

**R28 · `rw [Matrix.one_apply]`** changes the **goal**: `(1 : Matrix ι ι ℂ) i j = if i = j then 1 else 0`.
Placeholders: `{ι : Type} [DecidableEq ι] (i j : ι)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

**R29 · `Matrix.trace`, `Matrix.diag_apply`** (`simp only [Matrix.trace, Matrix.diag_apply]`) change the
**goal**: `M.trace = ∑ i, M i i` (`trace` is defined as the sum of `diag M`, and `diag M i = M i i`).
Placeholders: `{ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)`.

| Before | After |
|---|---|
| `⊢ P M.trace` | `⊢ P (∑ x, M x x)` |

`simp [Matrix.trace, Matrix.one_apply]` does R28, R13 (with `mul_one`), R15 and R29 in one call (W3).

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: an operator crosses the inner product.** R21, R22 (with `←`), R23; `rw` closes the last goal by `rfl`:

```lean-goal
⊢ star (M *ᵥ v) ⬝ᵥ N *ᵥ w = star v ⬝ᵥ (Mᴴ * N) *ᵥ w
⊢ star v ᵥ* Mᴴ ⬝ᵥ N *ᵥ w = star v ⬝ᵥ (Mᴴ * N) *ᵥ w
⊢ star v ⬝ᵥ Mᴴ *ᵥ N *ᵥ w = star v ⬝ᵥ (Mᴴ * N) *ᵥ w
```

**W2: two Kronecker products merge.** R24, then R26 with `←`:

```lean-goal
⊢ (kroneckerMap (fun x1 x2 => x1 * x2) A B)ᴴ * kroneckerMap (fun x1 x2 => x1 * x2) C E = kroneckerMap (fun x1 x2 => x1 * x2) (Aᴴ * C) (Bᴴ * E)
⊢ kroneckerMap (fun x1 x2 => x1 * x2) Aᴴ Bᴴ * kroneckerMap (fun x1 x2 => x1 * x2) C E = kroneckerMap (fun x1 x2 => x1 * x2) (Aᴴ * C) (Bᴴ * E)
```

**W3: a diagonal indicator collapses a double sum.** `simp only [mul_ite, mul_one, mul_zero]` (R13), then
`simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]` (R15) closes it:

```lean-goal
⊢ (∑ i, ∑ j, f i j * if i = j then 1 else 0) = ∑ i, f i i
⊢ (∑ x, ∑ x_1, if x = x_1 then f x x_1 else 0) = ∑ i, f i i
```

---

## Part 3 · `sdc_orthonormal`

Statement: for messages `b c : Fin 2 × Fin 2`, `star (sdc b) ⬝ᵥ sdc c = if b = c then 1 else 0`. Unfold `sdc`,
apply Part 2 (`rw [sdc_overlap]`): the goal becomes
`(↑(Fintype.card (Fin 2)))⁻¹ * ((enc b)ᴴ * enc c).trace = if b = c then 1 else 0`. Then split into the
16 pairs of messages and compute.

**R30 · `unfold D`** changes the **goal**: the defined name `D` becomes its body. Here `D` is the guide's
`noncomputable def D (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ := (n : ℂ) • 1`.

| Before | After |
|---|---|
| `⊢ P (D n)` | `⊢ P (↑n • 1)` |

**R31 · `obtain ⟨a, b⟩ := p`** changes the **context**: a pair `p : α × β` is replaced by its components, and
`p` becomes `(a, b)` in the goal. Placeholders: `{α β : Type} (Q : α × β → Prop)`.

| Before | After |
|---|---|
| `p : α × β ⊢ Q p` | `a : α, b : β ⊢ Q (a, b)` |

Then `fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2` gives 16 goals (TACTIC_STATES,
"Extensionality and finite case splits").

### Evaluating one case

`simp [enc, X, Z, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]` evaluates every case. It applies
R32, R36–R38 by itself; R33–R35 must be named.

**R32 · `rw [Fintype.card_fin]`** changes the **goal**: `Fintype.card (Fin n) = n`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin 2))` | `⊢ P 2` |

**R33 · `rw [Matrix.trace_fin_two]`** changes the **goal**: for a 2×2 matrix `A.trace = A 0 0 + A 1 1`.
Placeholders: `(A : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P A.trace` | `⊢ P (A 0 0 + A 1 1)` |

**R34 · `rw [Matrix.mul_apply]`** changes the **goal**: `(M * N) i k = ∑ j, M i j * N j k`.
Placeholders: `{ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (i k : ι)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R35 · `rw [Fin.sum_univ_two]`** changes the **goal**: `∑ i : Fin 2, f i = f 0 + f 1`.
Placeholders: `(f : Fin 2 → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R36 · `rw [Matrix.conjTranspose_apply]`** changes the **goal**: `Mᴴ i j = star (M j i)`.
Placeholders: `(M : Matrix ι ι ℂ) (i j : ι)`.

| Before | After |
|---|---|
| `⊢ P (Mᴴ i j)` | `⊢ P (star (M j i))` |

**R37 · `Fin.val_one`, then `pow_one`** change the **goal**: the bit `(1 : Fin 2)` cast to `ℕ` is `1`, and
`M ^ 1 = M`. For the bit `0`: `Fin.val_zero`, `pow_zero : M ^ 0 = 1`. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After `rw [Fin.val_one]` | After `rw [pow_one]` |
|---|---|---|
| `⊢ P (M ^ ↑1)` | `⊢ P (M ^ 1)` | `⊢ P M` |

**R38 · `rw [Prod.mk.injEq]`** changes the **goal**: `((a, b) = (c, d)) = (a = c ∧ b = d)`; `simp` uses it to
decide `if (b₁, b₂) = (c₁, c₂)` for concrete bits. Placeholders: `(a c : α) (b d : β)`.

| Before | After |
|---|---|
| `⊢ P ((a, b) = (c, d))` | `⊢ P (a = c ∧ b = d)` |

On 3 of the 4 diagonal cases `simp` stops at `2⁻¹ * (1 + 1) = 1` (it closes `b = c = (0, 0)` itself); finish with
`<;> norm_num`, which runs only on the goals still open.

**W4: cases on a bit.** With `S = !![1, 0; 0, Complex.I]`, `fin_cases b` and then
`simp [S, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`; `norm_num` closes what is left:

```lean-goal
⊢ ((S ^ ↑b)ᴴ * S ^ ↑b).trace = 2
⊢ ((S ^ ↑((fun i => i) ⟨0, ⋯⟩))ᴴ * S ^ ↑((fun i => i) ⟨0, ⋯⟩)).trace = 2
⊢ 1 + 1 = 2
```

---

## Traps

- `star v ⬝ᵥ w` is the inner product; `v ⬝ᵥ w` alone has no conjugate. The conjugate lives in `star`, and
  R21 is what moves it onto the matrix as `ᴴ`.
- R22 must be used with `←`: forward it turns `v ⬝ᵥ (A *ᵥ w)` into the row form, the opposite of what you want.
- `rw` needs the left side literally. After R21 the goal has `star v ᵥ* Mᴴ ⬝ᵥ …`, which is exactly the right
  side of `Matrix.dotProduct_mulVec`, so `rw [← …]` matches; do R21 first.
- `⊗ₖ` prints as `kroneckerMap (fun x1 x2 => x1 * x2) A B`, but the lemma names say `kronecker`
  (`Matrix.conjTranspose_kronecker`, `Matrix.mul_kronecker_mul`). `simp only [Matrix.kroneckerMap_apply]`
  evaluates entries.
- `Finset.sum_ite_eq` wants `if i = j` with the summed variable on the right; for `if j = i` it is
  `Finset.sum_ite_eq'`. A `simp only` with the wrong one leaves the sum untouched.
- `mul_ite` handles a factor on the left of the `if`, `ite_mul` on the right. Include both, and
  `mul_zero`/`zero_mul` for the `else 0` branches.
- `star (↑√↑n)⁻¹` is not removed by `Complex.conj_ofReal` directly: the `⁻¹` is in the way. First
  `Complex.star_def`, then `map_inv₀`, then `Complex.conj_ofReal` (R16 → R17 → R18).
- `ring` does not know `√n * √n = n`. Rewrite the right side `(↑n)⁻¹` into `(↑√↑n)⁻¹ * (↑√↑n)⁻¹` with
  `rw [← h]` first; after that the identity is pure ring algebra.
- `(b.1 : ℕ)` turns a bit `b.1 : Fin 2` into `0` or `1`, so `Z ^ (b.1 : ℕ)` is `1` or `Z` (R37).
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, chain with `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| amplitude of Φ | `simp [Ket.MES]` (state it once as `MES_apply`) | R1 |
| `(↑√↑n)⁻¹ * (↑√↑n)⁻¹ = (↑n)⁻¹` | `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp` | R2–R6 |
| `⬝ᵥ`, `*ᵥ` → sums | `simp only [dotProduct, mulVec]` | R7, R8 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R9 |
| entry of `A ⊗ₖ B` | `Matrix.kroneckerMap_apply` | R10 |
| entry of `star v` | `Pi.star_apply` | R11 |
| `star`, `*` into an `if` | `apply_ite star, star_zero, mul_ite, mul_zero, ite_mul, zero_mul` | R12–R14 |
| indicator sum → one term | `Finset.sum_ite_eq, Finset.mem_univ, if_true` | R15 |
| conjugate of a real `⁻¹` | `Complex.star_def, map_inv₀, Complex.conj_ofReal` | R16–R18 |
| factor into a sum | `Finset.mul_sum` | R19 |
| compare sums termwise | `refine Finset.sum_congr rfl fun i _ => ?_` | R20 |
| `star (M v) ⬝ᵥ w → star v ⬝ᵥ (Mᴴ w)` | `rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]` | R21, R22 |
| `M (N v) → (M N) v` | `Matrix.mulVec_mulVec` | R23 |
| `(A ⊗ B)ᴴ`, `1ᴴ` | `Matrix.conjTranspose_kronecker`, `Matrix.conjTranspose_one` | R24, R25 |
| `(A ⊗ A')(B ⊗ B') → (AB) ⊗ (A'B')` | `rw [← Matrix.mul_kronecker_mul]` | R26 |
| `1 * 1` | `one_mul` | R27 |
| identity entries, trace as a sum | `simp [Matrix.trace, Matrix.one_apply]` | R28, R29 |
| unfold a definition | `unfold sdc` | R30 |
| split a pair | `obtain ⟨b1, b2⟩ := b` | R31 |
| 16 cases | `fin_cases b1 <;> fin_cases b2 <;> fin_cases c1 <;> fin_cases c2` | TACTIC_STATES |
| evaluate a 2×2 case | `simp [enc, X, Z, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]` | R32–R38 |
| numbers left over | `norm_num` | TACTIC_STATES |
| see the state | infoview | |
