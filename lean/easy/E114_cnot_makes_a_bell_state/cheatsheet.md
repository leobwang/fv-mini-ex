# E114 · CNOT makes a Bell state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). Earlier matrix problems (E074, M126) help but are not
needed. **New here:** Mathlib's `Matrix` indexed by pairs `Fin 2 × Fin 2` (two-qubit gates), the
matrix–vector product `*ᵥ`, the Kronecker product `⊗ₖ`, `Matrix.of`, `Pi.single`, sums over a product
type, and `ext` with a pair pattern `⟨a, b⟩`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid β]` is
  a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 2 × Fin 2` | pairs `(a, b)` with `a b ∈ {0, 1}`: the basis state \|ab⟩ of two qubits. `p.1`, `p.2` are the components |
| `Fin 2 × Fin 2 → ℂ` | a two-qubit state: one complex amplitude per basis state |
| `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` | a 4×4 complex matrix (a two-qubit gate) whose rows and columns are indexed by pairs. A matrix *is* a function of row and column: `M p q` is the entry in row `p`, column `q` |
| `M *ᵥ v` | `Matrix.mulVec M v`, matrix times column vector: `(M *ᵥ v) i = ∑ j, M i j * v j`. Typed `*\_v`; needs `open Matrix`. Groups to the right: `A *ᵥ B *ᵥ v` is `A *ᵥ (B *ᵥ v)` |
| `u ⬝ᵥ v` | `dotProduct u v = ∑ i, u i * v i` |
| `∑ x, f x` | the sum of `f x` over every `x` of the (finite) index type; over `Fin 2 × Fin 2` that is 4 terms |
| `A ⊗ₖ B` | the Kronecker product, typed `\otimes\_k`, needs `open scoped Kronecker`: `(A ⊗ₖ B) (i, k) (j, l) = A i j * B k l`. `H ⊗ₖ 1` is H on qubit 1, identity on qubit 2 |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how the infoview prints `A ⊗ₖ B` |
| `of f`, `Matrix.of f` | the matrix whose entry `(p, q)` is `f p q` |
| `Pi.single i x` | the vector with `x` at index `i`, `0` elsewhere. `Pi.single b 1` is the basis vector \|b⟩ |
| `!![a, b; c, d]`, `![a, b]` | a 2×2 matrix with rows `a b` and `c d`; the vector `(a, b)` |
| `vecCons a f i` | entry `i` of the vector with first entry `a` and the rest `f`: `![a, b] = vecCons a ![b]`. A partial `simp` shows it when the index `i` is still a variable such as `x.1`; it disappears once `i` is a numeral |
| `x.1`, `x_1.2` | components of a pair `x`, `x_1` bound by a sum `∑ x, …` over `Fin 2 × Fin 2` (R7 splits such a sum) |
| `c • M` | scalar `c` times every entry of `M` |
| `1` (a matrix) | the identity matrix: `1 i j = if i = j then 1 else 0` |
| `↑√2`, `(↑√2)⁻¹` | the real `Real.sqrt 2` cast into `ℂ`; its inverse `1/√2` |
| `(1 : Fin 2) + 1` | `0`: addition in `Fin 2` is mod 2 (XOR), so `b + a` flips `b` exactly when `a = 1` |
| `(fun i => i) ⟨0, ⋯⟩` | the value `0`, printed this way after `fin_cases` |
| `case «0».«1»` | the goal for the basis state \|01⟩ after `fin_cases a <;> fin_cases b` |

---

## Part 1 · `cnot_bell`

Statement: `CNOT *ᵥ ((H ⊗ₖ 1) *ᵥ tensor (ket 0) (ket 0)) = bell`: apply H to qubit 1 of \|00⟩, then CNOT;
the result is the vector `bell` with amplitude `1/√2` on \|00⟩ and \|11⟩ and `0` elsewhere. It is an equation of
two functions `Fin 2 × Fin 2 → ℂ`.

### Vector equation → four entries

**R1 · `ext ⟨a, b⟩`** changes the **goal and the context**. It uses `funext` (two functions are equal when they
agree on every input) and splits that input, a pair, into its components with the pattern `⟨a, b⟩`.
Placeholders: `{α : Type} (v w : Fin 2 × Fin 2 → α)`.

| Before | After |
|---|---|
| `⊢ v = w` | `a b : Fin 2 ⊢ v (a, b) = w (a, b)` |

**R2 · `fin_cases a`** changes the **goal list and the context**: `a` leaves the context, and there is one goal per
value `0, 1`. `fin_cases a <;> fin_cases b` gives the four basis states. Placeholders: as in R1, `(a b : Fin 2)`.

| Before | After |
|---|---|
| `a b : Fin 2 ⊢ v (a, b) = w (a, b)` | `b : Fin 2 ⊢ v ((fun i => i) ⟨0, ⋯⟩, b) = w ((fun i => i) ⟨0, ⋯⟩, b)`, `b : Fin 2 ⊢ v ((fun i => i) ⟨1, ⋯⟩, b) = w ((fun i => i) ⟨1, ⋯⟩, b)` |

### Evaluating one entry

One `simp [...]` call does all of R3–R16 at once. You must **name** R3 (your definitions), R4, R5 and R7;
`simp` applies R6 and R8–R16 by itself.

**R3 · `simp only [D]`** changes the **goal**: a defined name becomes its body. Placeholders: `D` defined by
`def D : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]`. In the exercise, name every definition that occurs.

| Before | After |
|---|---|
| `⊢ P D` | `⊢ P !![0, 1; 1, 0]` |

**R4 · `Matrix.mulVec`** (a definition, unfolded with `simp only [Matrix.mulVec]`) changes the **goal**: entry `i`
of `M *ᵥ v` becomes the dot product of row `i` of `M` with `v`. Placeholders:
`{α : Type} [NonUnitalNonAssocSemiring α]` (α has `+`, `*`, `0`; `ℂ` qualifies), `{m n : Type} [Fintype n]` (any
index types, `n` finite; here both are `Fin 2 × Fin 2`), `(M : Matrix m n α) (v : n → α) (i : m)`.

| Before | After |
|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` |

**R5 · `dotProduct`** (a definition) changes the **goal**: `u ⬝ᵥ v` becomes the sum `∑ i, u i * v i`.
Placeholders: as in R4, `(u v : n → α)`.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ v)` | `⊢ P (∑ i, u i * v i)` |

**R6 · `Matrix.mulVec_mulVec`** changes the **goal**. The lemma is `A *ᵥ B *ᵥ v = (A * B) *ᵥ v`: two gates applied
in turn are one product gate. `simp` applies it by itself, which is why a plain `simp [defs]` shows
`(of … * kroneckerMap …) *ᵥ …` instead of two `*ᵥ`. Harmless once R4, R5 are in the `simp` set. Placeholders:
`{α : Type} [NonUnitalSemiring α]` (`ℂ` qualifies), `{l m n : Type} [Fintype m] [Fintype n]`,
`(A : Matrix l m α) (B : Matrix m n α) (v : n → α)`.

| Before | After |
|---|---|
| `⊢ P (A *ᵥ B *ᵥ v)` | `⊢ P ((A * B) *ᵥ v)` |

**R7 · `Fintype.sum_prod_type`** changes the **goal**. The lemma is `∑ x, f x = ∑ x, ∑ y, f (x, y)` for `x`
ranging over a product type: a sum over pairs is a double sum, and each inner sum over `Fin 2` then becomes two
terms (R8). `simp` does **not** apply it by itself (W1). Placeholders: `{β : Type} [AddCommMonoid β]` (β has a
commutative `+` with `0`; `ℂ` qualifies), `(f : Fin 2 × Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ p, f p)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R8 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R9 · `Matrix.of_apply`** changes the **goal**: the lemma is `Matrix.of f p q = f p q`. This is how `CNOT`'s
entries are read. Placeholders: `{α : Type} (f : Fin 2 × Fin 2 → Fin 2 × Fin 2 → α) (p q : Fin 2 × Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (of f p q)` | `⊢ P (f p q)` |

**R10 · `Matrix.kroneckerMap_apply`** changes the **goal**: the lemma is `(A ⊗ₖ B) (i, k) (j, l) = A i j * B k l`
(`simp only` also reduces the projections `(i, k).1` to `i`). Placeholders: `{α : Type} [Mul α]`,
`(A B : Matrix (Fin 2) (Fin 2) α) (i j k l : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (i, k) (j, l))` | `⊢ P (A i j * B k l)` |

**R11 · `Matrix.one_apply`** changes the **goal**: the lemma is `(1 : Matrix n n α) i j = if i = j then 1 else 0`.
Placeholders: `{α : Type} [Zero α] [One α]`, `{n : Type} [DecidableEq n]` (equality on `n` can be decided, as on
`Fin 2` and `Fin 2 × Fin 2`), `(i j : n)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

**R12 · `Pi.single_apply`** changes the **goal**: the lemma is `Pi.single i x j = if j = i then x else 0`. This
is how `ket b` is read. Placeholders: `{α : Type} [Zero α] (i j : Fin 2) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x j)` | `⊢ P (if j = i then x else 0)` |

**R13 · `Matrix.smul_apply`, then `smul_eq_mul`** change the **goal**: the entry of a scaled matrix becomes a
product of numbers. This is how `H = (√2)⁻¹ • !![…]` is read. Placeholders:
`(c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After `rw [Matrix.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • M) i j)` | `⊢ P (c • M i j)` | `⊢ P (c * M i j)` |

**R14 · entry of a literal** changes the **goal**: `simp` reads `!![a, b; c, d] i j` for numerals `i j`
(lemmas `Matrix.of_apply`, `Matrix.cons_val_…`). Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

**R15 · `Fin 2` arithmetic with `simp`** changes the **goal**: `1 + 1` in `Fin 2` is `0` (mod 2). `decide` also
proves `(1 : Fin 2) + 1 = 0`. This is what makes CNOT flip the target: `b + a` is `b` for `a = 0` and `1 - b` for
`a = 1`. Placeholders: `(P : Fin 2 → Prop)`.

| Before | After |
|---|---|
| `⊢ P (1 + 1)` | `⊢ P 0` |

**R16 · an `if` with a concrete condition** changes the **goal**: `simp` decides a condition built from `Fin 2`
numerals, `=`, `∧`, `+`, and keeps the right branch. Placeholders: `{α : Type} (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (if 0 = 1 ∧ 1 = 1 then x else y)` | `⊢ P y` |

What is left after R3–R16 is a sum of products of `0`, `1` and `(↑√2)⁻¹`, which `simp` closes. No `√2 * √2` occurs:
each entry of the result has exactly one factor `(↑√2)⁻¹`.

### Worked combinations (W1–W3, on objects that are not the exercise's)

`SW` is the SWAP gate `of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0`; `v01`, `v10` are \|01⟩, \|10⟩ as
`fun p => ![1, 0] p.1 * ![0, 1] p.2` and similar.

**W1: without R7, `simp` stops at a sum over pairs.** `simp [SW, v01, Matrix.mulVec, dotProduct]` on
`(SW *ᵥ v01) (1, 0) = 1` leaves

```lean-goal
⊢ (∑ x, if 1 = x.2 ∧ 0 = x.1 then ![1, 0] x.1 * ![0, 1] x.2 else 0) = 1
```

and `simp [Fintype.sum_prod_type]` finishes it. Put R7 in the first `simp` call.

**W2.** `SW *ᵥ v01 = v10`: R1, then R2 twice, then
`simp [SW, v01, v10, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]` on all four goals.

**W3.** `(D ⊗ₖ 1) *ᵥ v01 = |11⟩`, with `D` the Pauli X matrix: the same three steps; `simp` applies R10 and R11
by itself.

---

## Part 2 · `cnot_sq`

Statement: `CNOT * CNOT = 1`: CNOT is its own inverse. It is an equation of two matrices indexed by pairs, so
it has 4 × 4 = 16 entries.

**R17 · `ext ⟨a, b⟩ ⟨c, d⟩`** changes the **goal and the context**. It uses `Matrix.ext` (two matrices are equal
when every entry is) and splits both the row index and the column index into components.
Placeholders: `{α : Type} (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `a b c d : Fin 2 ⊢ M (a, b) (c, d) = N (a, b) (c, d)` |

Then `fin_cases` (R2) on each of `a b c d`: 16 goals.

**R18 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (`ℂ` qualifies),
`{l m n : Type} [Fintype m]`, `(M : Matrix l m α) (N : Matrix m n α) (i : l) (k : n)`. Here the middle index
`j` ranges over `Fin 2 × Fin 2`, so R7 and R8 turn the sum into 4 terms.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R19 · `Prod.mk.injEq`** changes the **goal**: the lemma is `((a, b) = (c, d)) = (a = c ∧ b = d)`. It turns the
condition of R11 on pairs into conditions on components, which R16 then decides. `simp` applies it by itself.
Placeholders: `{α : Type} (a b c d : α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((a, b) = (c, d))` | `⊢ P (a = c ∧ b = d)` |

**W4.** `SW * SW = 1`: R17, R2 on all four components, then `simp [SW, Matrix.mul_apply, Fintype.sum_prod_type]`.
Without `Fintype.sum_prod_type` each goal stays a sum `∑ x, if x.1 = … ∧ x.2 = … then … else 0`.

---

## Traps

- A plain `simp [CNOT, H, ket, tensor, bell]` does not unfold `*ᵥ`; it only merges the two gates (R6) and stops.
  Name `Matrix.mulVec` and `dotProduct` (R4, R5).
- `simp` does not split a sum over pairs: without `Fintype.sum_prod_type` it is stuck at `∑ x, …` with `x.1`, `x.2`
  (W1, W4).
- For the matrix product use `Matrix.mul_apply` (R18); `mulVec`/`dotProduct` are for matrix times vector.
- `1` in `H ⊗ₖ 1` has its size inferred from context; in your own examples write `(1 : Matrix (Fin 2) (Fin 2) ℂ)`,
  or Lean cannot tell which identity matrix you mean.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| vector on pairs → entries | `ext ⟨a, b⟩` | R1 |
| matrix on pairs → entries | `ext ⟨a, b⟩ ⟨c, d⟩` | R17 |
| one goal per basis state | `fin_cases a <;> fin_cases b` | R2 |
| unfold your definitions | `simp [CNOT, H, …]` | R3 |
| matrix × vector entry | `simp [Matrix.mulVec, dotProduct]` | R4, R5 |
| matrix × matrix entry | `simp [Matrix.mul_apply]` | R18 |
| sum over `Fin 2 × Fin 2` | `simp [Fintype.sum_prod_type]` | R7, R8 |
| entries of `of f`, `A ⊗ₖ B`, `1`, `Pi.single`, `c • M`, `!![…]` | `simp` (automatic) | R9–R14 |
| `Fin 2` arithmetic, concrete `if` | `simp` (automatic), `decide` | R15, R16 |
| `(a, b) = (c, d)` | `simp` (automatic, `Prod.mk.injEq`) | R19 |
| see the state | infoview | |
