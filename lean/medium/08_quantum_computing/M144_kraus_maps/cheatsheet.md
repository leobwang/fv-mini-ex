# M144 · Kraus maps are trace preserving and positive: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). Matrices `Matrix n n ℂ` and `Aᴴ` as met in M126 help but
are re-explained below. **New here:** Mathlib's matrix trace, finite sums `∑`, matrix–vector products and
the dot product, positive semidefinite (PSD) matrices, the order on `ℂ`, and `simp_rw`.

The physics: a quantum channel in Kraus form is $\Phi(\rho) = \sum_i K_i \rho K_i^\dagger$, with Kraus
operators $K_i$ ($d\times d$ complex matrices indexed by a finite type `ι`). It is trace preserving when
$\sum_i K_i^\dagger K_i = I$ and maps PSD matrices to PSD matrices for any $K_i$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp_rw`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal or hypothesis.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing R]` is a
  requirement on `R` (a *type class*): `[CommRing R]` means `R` has `+ - *`, `0`, `1` with `*` commutative
  (`ℂ`, `ℝ`, `ℤ` qualify). `[Fintype n]` means `n` is a finite type, so sums over it and matrix products
  make sense (`Fin d` qualifies). `[DecidableEq n]` means equality on `n` can be decided, which the identity
  matrix `1` needs (its entries are `if i = j then 1 else 0`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix d d ℂ` | `d × d` complex matrices, rows and columns indexed by the finite type `d` |
| `Aᴴ` | conjugate transpose $A^\dagger$: `Aᴴ i j = conj (A j i)` |
| `A.trace` | $\operatorname{tr} A = \sum_i A_{ii}$ (`Matrix.trace A`) |
| `∑ i, f i` | $\sum_{i}$ over all of the finite type; it is `∑ i ∈ Finset.univ, f i` |
| `∑ i ∈ s, f i` | sum over the finite set `s : Finset ι` |
| `Finset.univ` | the set of all elements of a finite type |
| `v : n → ℂ` | a vector: a function from indices to entries |
| `M *ᵥ v` | matrix times column vector, $(Mv)_i = \sum_j M_{ij} v_j$ (`Matrix.mulVec`) |
| `v ᵥ* M` | row vector times matrix, $(vM)_j = \sum_i v_i M_{ij}$ (`Matrix.vecMul`) |
| `v ⬝ᵥ w` | $\sum_i v_i w_i$, no conjugation (`dotProduct`) |
| `star v` | entrywise complex conjugate of the vector `v`; so `star x ⬝ᵥ y` is $\langle x, y\rangle = \sum_i \overline{x_i}\, y_i$ |
| `M *ᵥ N *ᵥ v` | `M *ᵥ (N *ᵥ v)`: `*ᵥ` groups to the right |
| `v ᵥ* A ⬝ᵥ w` | `(v ᵥ* A) ⬝ᵥ w`: `ᵥ*` binds tighter than `⬝ᵥ` |
| `star x ⬝ᵥ M *ᵥ x` | `star x ⬝ᵥ (M *ᵥ x)` $= \langle x, Mx\rangle$, the quadratic form of `M` at `x` |
| `Mᴴᴴ` | `(Mᴴ)ᴴ`, which equals `M` (R13) |
| `M.IsHermitian` | `Mᴴ = M` |
| `M.PosSemidef` | `M` is PSD: Hermitian and $\langle x, Mx\rangle \ge 0$ for every `x` (R8 gives this form) |
| `0 ≤ z` with `z : ℂ` | the order from `open scoped ComplexOrder`: `z` is real and nonnegative (`0 ≤ z.re ∧ z.im = 0`) |
| `this` | the name `have := …` gives a fact when you give none |
| `a✝` | a hypothesis with no usable name (introduced as `_`) |
| `inst✝ : Fintype d` | an unnamed instance argument from a `[Fintype d]` bracket; ignore it |

---

## Part 1 · `kraus_trace`

Statement: if `∑ i, (K i)ᴴ * K i = 1` then `(kraus K ρ).trace = ρ.trace`, i.e.
$\operatorname{tr}\sum_i K_i\rho K_i^\dagger = \operatorname{tr}\rho$. Math: $\operatorname{tr}$ is linear,
$\operatorname{tr}(ABC) = \operatorname{tr}(CAB)$, so the left side is
$\operatorname{tr}\big((\sum_i K_i^\dagger K_i)\rho\big) = \operatorname{tr}\rho$.

**R1 · `rw [D]`** changes the **goal**: a defined name applied to arguments is replaced by its body (Lean
uses the definition's equation `D a b = body`). Placeholders: `(A M : Matrix n n ℂ)`, with
`def sandwich A M := A * M * A`. In the exercise: `rw [kraus]`.

| Before | After |
|---|---|
| `⊢ P (sandwich A M)` | `⊢ P (A * M * A)` |

**R2 · `rw [Matrix.trace_sum]`** changes the **goal**: the trace of a sum becomes the sum of traces.
Lemma: `Matrix.trace_sum (s : Finset ι) (f : ι → Matrix n n R) : (∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i).trace`.
Placeholders: `{ι n R : Type} [Fintype ι] [Fintype n] [CommRing R] (f : ι → Matrix n n R)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i).trace` | `⊢ P (∑ i, (f i).trace)` |

**R3 · `rw [Matrix.trace_mul_cycle]`** changes the **goal**: cyclicity of the trace on one product of three.
Lemma: `Matrix.trace_mul_cycle (A B C) : (A * B * C).trace = (C * A * B).trace` (`*` groups to the left,
so `A * B * C` is `(A * B) * C`). Placeholders: `{n R : Type} [Fintype n] [CommRing R] (A B C : Matrix n n R)`.

| Before | After |
|---|---|
| `⊢ P (A * B * C).trace` | `⊢ P (C * A * B).trace` |

**R4 · `simp_rw [Matrix.trace_mul_cycle (A _) M]`** changes the **goal**: R3 applied inside every term of
`∑ i, …`. Plain `rw` fails there with "Did not find an occurrence of the pattern", because the term
mentions the bound variable `i`; `simp_rw` rewrites under binders. The arguments `(A _) M` fix the first two
factors: without them `simp_rw` keeps rotating `A * B * C → C * A * B → B * C * A → …` and stops with
"Possibly looping simp theorem" and "maximum recursion depth has been reached". Lean may rename
the bound variable to `x`. Placeholders: `(A C : ι → Matrix n n R) (M : Matrix n n R)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (A i * M * C i).trace)` | `⊢ P (∑ x, (C x * A x * M).trace)` |

**R5 · `rw [← Matrix.trace_sum]`** changes the **goal**: R2 right to left, a sum of traces becomes the
trace of a single sum. Placeholders as R2.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i).trace)` | `⊢ P (∑ i, f i).trace` |

**R6 · `rw [← Finset.sum_mul]`** changes the **goal**: a common right factor leaves the sum. Lemma:
`Finset.sum_mul (s) (f) (a) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`. It holds in any (not necessarily
commutative) semiring, so for matrices. Placeholders: `(f : ι → Matrix n n R) (M : Matrix n n R)`.
Note `(K i)ᴴ * K i * ρ` is `((K i)ᴴ * K i) * ρ`, so `f i = (K i)ᴴ * K i` and `a = ρ`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i * M)` | `⊢ P ((∑ i, f i) * M)` |

Now the goal contains `∑ i, (K i)ᴴ * K i` literally, and `rw [hK]` replaces it by `1` (TACTIC_STATES,
"Rewriting").

**R7 · `rw [Matrix.one_mul]`** changes the **goal**: `1 * M` becomes `M`. Lemma:
`Matrix.one_mul (M) : 1 * M = M`. Placeholders: `[DecidableEq n] (M : Matrix n n R)`. When the goal becomes
`ρ.trace = ρ.trace`, `rw` closes it itself (it tries `rfl` after rewriting).

| Before | After |
|---|---|
| `⊢ P (1 * M)` | `⊢ P M` |

**W1** chains R2 → R4 → R5 on `(∑ i, A i * M * C i).trace = (∑ i, C i * A i * M).trace`:

```lean-goal
⊢ (∑ i, A i * M * C i).trace = (∑ i, C i * A i * M).trace
⊢ ∑ i, (A i * M * C i).trace = (∑ i, C i * A i * M).trace
⊢ ∑ x, (C x * A x * M).trace = (∑ i, C i * A i * M).trace
```

`rw [Matrix.trace_sum]` rewrote only the left side (the right side's sum has a different `f`), and the last
`rw [← Matrix.trace_sum]` makes both sides equal, so `rw` closes the goal.

---

## Part 2 · `conj_psd`

Statement: `ρ.PosSemidef → (B * ρ * Bᴴ).PosSemidef`. Math:
$\langle x, B\rho B^\dagger x\rangle = \langle B^\dagger x, \rho\, B^\dagger x\rangle \ge 0$, so test the PSD
property of `ρ` on the vector $y = B^\dagger x$; Hermitian-ness is one library lemma.

**R8 · `rw [Matrix.posSemidef_iff_dotProduct_mulVec] at *`** changes the **context and the goal**. Lemma:
`M.PosSemidef ↔ M.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x`. `at *` rewrites it in every hypothesis and in
the goal. Mathlib's *definition* of `PosSemidef` quantifies over finitely supported vectors `n →₀ ℂ`, so
always rewrite with R8 before using `hρ.2`. Placeholders: `(A M : Matrix n n ℂ) (hA : A.PosSemidef)`.

| Before | After |
|---|---|
| `hA : A.PosSemidef ⊢ M.PosSemidef` | `⊢ M.IsHermitian ∧ ∀ (x : n → ℂ), 0 ≤ star x ⬝ᵥ M *ᵥ x` and `hA : A.IsHermitian ∧ ∀ (x : n → ℂ), 0 ≤ star x ⬝ᵥ A *ᵥ x` |

**R9 · `refine ⟨e, fun x => ?_⟩`** changes the **goal and the context**: the first conjunct is proved by
the term `e` now; for the second, `x` enters the context and `Q x` is the goal. Placeholders:
`{α : Type} (A : Prop) (Q : α → Prop) (a : A)`.

| Before | After |
|---|---|
| `⊢ A ∧ ∀ (x : α), Q x` | `x : α ⊢ Q x` |

**R10 · `Matrix.isHermitian_mul_mul_conjTranspose B hA`** is a term of type `(B * A * Bᴴ).IsHermitian`.
Lemma: `Matrix.isHermitian_mul_mul_conjTranspose (B) : A.IsHermitian → (B * A * Bᴴ).IsHermitian`.
As `have hB := …` it changes the **context**; in the exercise it is the `e` of R9, with `hρ.1` for `hA`.
Placeholders: `(A B : Matrix n n ℂ) (hA : A.IsHermitian)`.

| Before | After |
|---|---|
| `hA : A.IsHermitian ⊢ G` | `hB : (B * A * Bᴴ).IsHermitian ⊢ G` |

**R11 · `have := h.2 v`** changes the **context**. For `h : A ∧ ∀ x, Q x`, `h.1 : A` and `h.2 : ∀ x, Q x`;
applying `h.2` to `v` gives `this : Q v`. In the exercise `v` is the vector `Bᴴ *ᵥ x`. Placeholders:
`{α : Type} (A : Prop) (Q : α → Prop) (v : α)`.

| Before | After |
|---|---|
| `v : α ⊢ Q v` | `this : Q v ⊢ Q v` |

The next three entries rewrite **in a hypothesis** (`rw [...] at h`): the context changes, the goal does not.

**R12 · `rw [Matrix.star_mulVec] at h`** changes the **context**. Lemma:
`Matrix.star_mulVec (M) (v) : star (M *ᵥ v) = star v ᵥ* Mᴴ` ($\overline{Mv} = \bar v\, M^\dagger$ as a row).
Placeholders: `(M : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `h : Q (star (M *ᵥ v)) ⊢ Q (star v ᵥ* Mᴴ)` | `h : Q (star v ᵥ* Mᴴ) ⊢ Q (star v ᵥ* Mᴴ)` |

**R13 · `rw [Matrix.conjTranspose_conjTranspose] at h`** changes the **context**: `Mᴴᴴ = M`.
Placeholders: `(M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `h : Q Mᴴᴴ ⊢ Q M` | `h : Q M ⊢ Q M` |

**R14 · `rw [← Matrix.dotProduct_mulVec] at h`** changes the **context**. Lemma:
`Matrix.dotProduct_mulVec (v) (A) (w) : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w` (associativity $v\,(Aw) = (vA)\,w$).
Right to left it moves `A` off the left vector onto the right one. Placeholders:
`(A : Matrix n n ℂ) (v w : n → ℂ)`.

| Before | After |
|---|---|
| `h : Q (v ᵥ* A ⬝ᵥ w) ⊢ Q (v ⬝ᵥ A *ᵥ w)` | `h : Q (v ⬝ᵥ A *ᵥ w) ⊢ Q (v ⬝ᵥ A *ᵥ w)` |

**W2** chains R12 → R14 on the goal `star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w`; the last `rw` closes it:

```lean-goal
⊢ star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w
⊢ star v ᵥ* Mᴴ ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w
```

**R15 · `rw [← Matrix.mulVec_mulVec]`** changes the **goal**. Lemma:
`Matrix.mulVec_mulVec (v) (M) (N) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v`. Right to left it splits a product acting on
a vector. `B * ρ * Bᴴ` is `(B * ρ) * Bᴴ`, so the first use peels off `Bᴴ`, and a second use splits `B * ρ`.
Placeholders: `(M N : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ Q ((M * N) *ᵥ v)` | `⊢ Q (M *ᵥ N *ᵥ v)` |

**R16 · `rwa [e]`** **closes** the goal: it is `rw [e]` followed by `assumption` (close the goal with a
hypothesis that matches it exactly). Placeholders: `{α : Type} (a b : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `e : a = b, h : P b ⊢ P a` | no goals |

---

## Part 3 · `kraus_psd`

Statement: `ρ.PosSemidef → (kraus K ρ).PosSemidef`. A sum of PSD matrices is PSD, and each term
`K i * ρ * (K i)ᴴ` is PSD by `conj_psd` (Part 2), which you may use here as a lemma.

**R17 · `apply Matrix.posSemidef_sum`, then `intro i _`** changes the **goal**, then the **context**. Lemma:
`Matrix.posSemidef_sum (s : Finset ι) : (∀ i ∈ s, (x i).PosSemidef) → (∑ i ∈ s, x i).PosSemidef`.
`∀ i ∈ s, Q i` means `∀ i, i ∈ s → Q i`, so `intro i _` takes both (`_` leaves the membership unnamed:
`a✝`). `apply` sees through `kraus K ρ` to the sum, but `rw [kraus]` (R1) first makes the goal readable.
Term form: `Matrix.posSemidef_sum _ fun i _ => …`. Placeholders: `(x : ι → Matrix n n ℂ)`.

| Before | After `apply Matrix.posSemidef_sum` | After `intro i _` |
|---|---|---|
| `⊢ (∑ i, x i).PosSemidef` | `⊢ ∀ i ∈ Finset.univ, (x i).PosSemidef` | `i : ι, a✝ : i ∈ Finset.univ ⊢ (x i).PosSemidef` |

---

## Traps

- `rw [Matrix.trace_mul_cycle]` cannot reach inside `∑ i, …` ("Did not find an occurrence of the pattern"): use `simp_rw` (R4).
- `simp_rw [Matrix.trace_mul_cycle]` with no arguments rotates the product forever ("maximum recursion
  depth has been reached"). Pin it: `Matrix.trace_mul_cycle (K _) ρ`.
- `rw [hK]` needs `∑ i, (K i)ᴴ * K i` literally in the goal: fold the sum (R5) and pull `ρ` out (R6) first.
- `hρ.2` on an un-rewritten `hρ : ρ.PosSemidef` quantifies over `x : d →₀ ℂ` (finitely supported
  functions), not vectors `d → ℂ`. Rewrite with R8 `at *` first.
- `M *ᵥ N *ᵥ v` is `M *ᵥ (N *ᵥ v)` and `v ᵥ* A ⬝ᵥ w` is `(v ᵥ* A) ⬝ᵥ w`. Read the parentheses before
  choosing a direction for R14 and R15.
- `star (Bᴴ *ᵥ x)` becomes `star x ᵥ* Bᴴᴴ` (R12), and the double `ᴴᴴ` must go (R13) before R14 matches.
- The `BANNED:` names (`mul_mul_conjTranspose_same`, `conjTranspose_mul_mul_same`,
  `star_left_conjugate_nonneg`, `star_right_conjugate_nonneg`) prove `conj_psd` outright; `try?` is banned too.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `kraus` | `rw [kraus]` | R1 |
| trace of a sum → sum of traces | `rw [Matrix.trace_sum]` | R2 |
| `(A * B * C).trace → (C * A * B).trace` | `rw [Matrix.trace_mul_cycle]` | R3 |
| the same under `∑ i, …` | `simp_rw [Matrix.trace_mul_cycle (A _) M]` | R4 |
| sum of traces → trace of a sum | `rw [← Matrix.trace_sum]` | R5 |
| `∑ i, f i * a → (∑ i, f i) * a` | `rw [← Finset.sum_mul]` | R6 |
| use the hypothesis | `rw [hK]` | TACTIC_STATES |
| `1 * M → M` | `rw [Matrix.one_mul]` | R7 |
| PSD ↔ Hermitian ∧ quadratic form ≥ 0 | `rw [Matrix.posSemidef_iff_dotProduct_mulVec] at *` | R8 |
| prove `A ∧ ∀ x, Q x` | `refine ⟨e, fun x => ?_⟩` | R9 |
| `(B * A * Bᴴ)` Hermitian | `Matrix.isHermitian_mul_mul_conjTranspose B hA` | R10 |
| use `h : A ∧ ∀ x, Q x` at `v` | `have := h.2 v` | R11 |
| `star (M *ᵥ v) → star v ᵥ* Mᴴ` | `rw [Matrix.star_mulVec] at h` | R12 |
| `Mᴴᴴ → M` | `rw [Matrix.conjTranspose_conjTranspose] at h` | R13 |
| `v ᵥ* A ⬝ᵥ w → v ⬝ᵥ A *ᵥ w` | `rw [← Matrix.dotProduct_mulVec] at h` | R14 |
| `(M * N) *ᵥ v → M *ᵥ N *ᵥ v` | `rw [← Matrix.mulVec_mulVec]` | R15 |
| rewrite, then close by a hypothesis | `rwa [e]` | R16 |
| sum of PSD is PSD | `apply Matrix.posSemidef_sum; intro i _` | R17 |
| see the state | infoview | |
