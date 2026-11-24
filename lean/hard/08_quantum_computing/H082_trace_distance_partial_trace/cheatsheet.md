# H082 · Trace distance contracts under partial trace: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `simp only`, `have`, `obtain`, `exact`, `rfl`,
anonymous constructors `⟨_, _⟩`.
**New here:** physlib's mixed states (`MState`), trace norm, trace distance and partial trace; Mathlib's
matrices, `Matrix.trace`, the Kronecker product `⊗ₖ`, the unitary group `𝐔[n]`, big-operator sums `∑`
over finite types, `IsGreatest`, and the tactics `gcongr` and `dsimp`.

**The mathematics.** For a finite index type `d` (the basis labels), a state `ρ : MState d` is a density
matrix: positive semidefinite, trace 1; `ρ.m : Matrix d d ℂ` is its matrix. Write $\Delta = \rho - \sigma$ on
$d_1 \times d_2$ (two subsystems A, B).

- Trace norm: $\lVert M\rVert_1 = \operatorname{tr}\sqrt{M^\dagger M}$ (sum of singular values; $M^\dagger$ = conjugate
  transpose). Trace distance: $D(\rho,\sigma) = \tfrac12\lVert\rho-\sigma\rVert_1$ (`TrDistance`).
- Partial trace over B: $(\operatorname{Tr}_B M)_{ij} = \sum_k M_{(i,k),(j,k)}$ (`Matrix.traceRight`).
- Variational formula (`Matrix.traceNorm_eq_max_re_tr_U`): $\lVert M\rVert_1 = \max_{U \text{ unitary}} \operatorname{Re}\operatorname{tr}(UM)$,
  and the max is attained.
- Duality (MILESTONE `trace_mul_traceRight`): $\operatorname{tr}(U \cdot \operatorname{Tr}_B M) = \operatorname{tr}((U \otimes 1) M)$, both
  equal to $\sum_{x,y,k} U_{xy} M_{(y,k),(x,k)}$.

Proof: pick $U$ with $\lVert\operatorname{Tr}_B\Delta\rVert_1 = \operatorname{Re}\operatorname{tr}(U\operatorname{Tr}_B\Delta) = \operatorname{Re}\operatorname{tr}((U\otimes 1)\Delta)$.
$U \otimes 1$ is unitary, so it is one candidate in the max for $\Delta$: the value is $\le \lVert\Delta\rVert_1$. Multiply by ½.

MILESTONE `traceRight_m_sub` moves the subtraction inside the partial trace, and MILESTONE
`unitaryGroup_congr` repairs an instance mismatch (Traps).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, for entries that only change the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket is a requirement on a type
  (a *type class*): `[Fintype d]` says `d` is finite, so `∑ x : d` makes sense; `[DecidableEq d]` says
  equality on `d` can be decided, so `if i = j then …` and the identity matrix make sense. The exercise's
  `d₁`, `d₂` and `d₁ × d₂` meet both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. `∅` means
  the goal is closed.

## Reading the goals

| You see | It means |
|---|---|
| `MState d` | a density matrix on `d`; `ρ.m : Matrix d d ℂ` is its matrix (`ρ.M` is the same as a `HermitianMat`) |
| `Matrix m n ℂ` | complex matrices with rows indexed by `m`, columns by `n`; `M i j` is an entry |
| `(i, k)`, `x.1`, `x.2` | a pair in `d₁ × d₂` and its components |
| `TrDistance ρ σ` | $\tfrac12\lVert\rho-\sigma\rVert_1$; unfolds to `1 / 2 * (ρ.m - σ.m).traceNorm` (R15) |
| `A.traceNorm` | the trace norm $\lVert A\rVert_1$, a real number |
| `ρ.traceRight`, `A.traceRight` | partial trace over the second factor, of a state / of a matrix (R8, R13) |
| `A.trace`, `z.re` | $\operatorname{tr} A = \sum_i A_{ii}$ (R1); the real part of `z : ℂ` |
| `∑ x, f x` | sum over all `x` of a finite type (`Finset.univ`); `∑ x ∈ s, f x` sums over a finite set `s` |
| `Matrix.kroneckerMap (fun x1 x2 => x1 * x2) U 1` | `U ⊗ₖ 1`: entry `((a, b), (c, e))` is `U a c * 1 b e` (R4) |
| `1 i j` | entry of the identity matrix: `if i = j then 1 else 0` (R5) |
| `𝐔[n]` | `Matrix.unitaryGroup n ℂ`: matrices with $U^\dagger U = 1$, as a set of matrices |
| `@Matrix.unitaryGroup n i1 _ ℂ _ _` | `𝐔[n]` with every argument written out (`@`), so the `DecidableEq` instance `i1` can be chosen by hand; `_` lets Lean fill the rest (Part 3) |
| `↑⟨U, hU⟩` | `U` packed with its proof `hU : U ∈ 𝐔[n]` into an element of `𝐔[n]`, then unpacked; it is `U` (R19) |
| `IsGreatest S a` | `a ∈ S ∧ ∀ x ∈ S, x ≤ a`: `a` is the maximum of `S` (R16, R17) |
| `{x \| ∃ U, f U = x}` | the set of values `f U` |
| `x_1`, `x_2`, `j_1`, `i₁` | names Lean invents for bound variables (summation indices); the names carry no meaning |
| `⋯` | a proof term the infoview hides, e.g. in `↑⟨U ⊗ₖ 1, ⋯⟩` inside `hle` before R19 |
| `x✝ : x ∈ Finset.univ` | an unnamed hypothesis (from `fun x _ => …`), always true, never needed |
| `case hbc` | the goal `gcongr` leaves for the factors that differ (R21) |

---

## Part 1 · `trace_mul_traceRight` (MILESTONE)

Statement: `(U * A.traceRight).trace = ((U ⊗ₖ 1) * A).trace` for `U : Matrix d₁ d₁ ℂ`,
`A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ`. Turn both sides into explicit sums (R1–R9) and show they are the same
triple sum in a different order (R10, R11).

### Traces, products and pairs → sums

**R1 · `simp only [Matrix.trace, Matrix.diag]`** changes the **goal**: the trace becomes the sum of the
diagonal. Placeholders: `{n : Type} [Fintype n] (M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P M.trace` | `⊢ P (∑ x, M x x)` |

**R2 · `rw [Matrix.mul_apply]`** changes the **goal**. The lemma is `(M * N) i k = ∑ j, M i j * N j k`.
Placeholders: `{l m n : Type} [Fintype m] (M : Matrix l m ℂ) (N : Matrix m n ℂ) (i : l) (k : n)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R3 · `rw [Fintype.sum_prod_type]`** changes the **goal**. The lemma is
`∑ x : α × β, g x = ∑ a, ∑ b, g (a, b)`. Placeholders: `{α β : Type} [Fintype α] [Fintype β] (g : α × β → ℂ)`.
In the exercise it splits every sum over `d₁ × d₂`.

| Before | After |
|---|---|
| `⊢ P (∑ x, g x)` | `⊢ P (∑ x, ∑ y, g (x, y))` |

**R4 · `simp only [Matrix.kroneckerMap_apply]`** changes the **goal**. The lemma is
`(A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2` (stated for `kroneckerMap f`; `simp` also evaluates `(i, j).1` to `i`).
Placeholders: `{a b c e : Type} (A : Matrix a c ℂ) (B : Matrix b e ℂ) (i : a) (j : b) (k : c) (l : e)`.
`⊗ₖ` needs `open scoped Kronecker`, and the infoview never prints it.

| Before | After |
|---|---|
| `⊢ P (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B (i, j) (k, l))` | `⊢ P (A i k * B j l)` |

**R5 · `rw [Matrix.one_apply]`** changes the **goal**. The lemma is `1 i j = if i = j then 1 else 0`.
Placeholders: `{n : Type} [DecidableEq n] (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

**R6 · `simp only [mul_ite, mul_one, mul_zero]`** changes the **goal**. `mul_ite` is
`a * (if p then b else c) = if p then a * b else a * c`; `mul_one`, `mul_zero` clean the branches. When the
`if` is on the left, `ite_mul`, `one_mul`, `zero_mul` do the same. Placeholders:
`{n : Type} [DecidableEq n] (i j : n) (z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * if i = j then 1 else 0)` | `⊢ P (if i = j then z else 0)` |

**R7 · `simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]`** changes the **goal**: a sum in which only
the term `j = i` survives becomes that term. `Finset.sum_ite_eq` is
`∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0`; `Finset.mem_univ` (`i ∈ Finset.univ`) and
`if_true` remove the `if`. For `if j = i` (the other order) the lemma is `Finset.sum_ite_eq'`; `simp` picks the
right one if you list both. Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (i : n) (f : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ j, if i = j then f j else 0)` | `⊢ P (f i)` |

R1–R7 go into ONE `simp only [...]` on the milestone (it rewrites both sides). Afterwards the left side reads
`∑ x, ∑ j, U x j * A.traceRight j x` and the right side is a triple sum over `d₁`, `d₂`, `d₁`.

### Partial-trace entries and moving factors

**R8 · `simp only [Matrix.traceRight, Matrix.of_apply]`** changes the **goal**: an entry of the partial trace
becomes a sum over the traced index. `Matrix.traceRight A = Matrix.of fun i j => ∑ k, A (i, k) (j, k)`, and
`Matrix.of_apply` evaluates `Matrix.of f i j` to `f i j`. Placeholders:
`{d₁ d₂ : Type} [Fintype d₂] (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₁)`.

| Before | After |
|---|---|
| `⊢ P (A.traceRight i j)` | `⊢ P (∑ i₁, A (i, i₁) (j, i₁))` |

**R9 · `rw [Finset.mul_sum]`** changes the **goal**. The lemma is `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`.
Placeholders: `{α : Type} [Fintype α] (z : ℂ) (f : α → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * ∑ i, f i)` | `⊢ P (∑ i, z * f i)` |

### Reordering sums

**R10 · `rw [Finset.sum_comm]`** changes the **goal**. The lemma is
`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`. `rw` swaps the FIRST double sum it finds, which is the
outermost pair on the left side. Rewriting twice in a row swaps the same pair back. Placeholders:
`{α β : Type} [Fintype α] [Fintype β] (f : α → β → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∑ y, f x y)` | `⊢ P (∑ y, ∑ x, f x y)` |

**R11 · `refine Finset.sum_congr rfl fun x _ => ?_`** changes the **goal and the context**: to prove two sums
over the same set equal, prove the summands equal at each `x`. `Finset.sum_congr` is
`s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`. This is how you reach the
inner sums: after R11, R10 swaps the two sums *inside* the outer one. As a term,
`Finset.sum_congr rfl fun x _ => Finset.sum_comm` does both at once. Placeholders:
`{α : Type} [Fintype α] (f g : α → ℂ)`.

| Before | After |
|---|---|
| `⊢ ∑ x, f x = ∑ x, g x` | `x : α, x✝ : x ∈ Finset.univ ⊢ f x = g x` |

**W1: `tr (M N) = tr (N M)`.** R1 and R2 in one `simp only`, then R10 on the outer sums, then R11 twice to
reach a single product:

```lean-goal
⊢ (M * N).trace = (N * M).trace
⊢ ∑ x, ∑ j, M x j * N j x = ∑ x, ∑ j, N x j * M j x
⊢ ∑ y, ∑ x, M x y * N y x = ∑ x, ∑ j, N x j * M j x
⊢ ∑ x, M x j * N j x = ∑ j_1, N j j_1 * M j_1 j
⊢ M i j * N j i = N j i * M i j
```

---

## Part 2 · `traceRight_m_sub` (MILESTONE)

Statement: `ρ.traceRight.m - σ.traceRight.m = (ρ.m - σ.m).traceRight`. The left side is about states, the
right side about raw matrices; split the right side, then both sides agree by definition.

**R12 · `rw [Matrix.traceRight_sub]`** changes the **goal**. The lemma is
`(A - B).traceRight = A.traceRight - B.traceRight`. Placeholders:
`{d₁ d₂ : Type} [Fintype d₂] (A B : Matrix (d₁ × d₂) (d₁ × d₂) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (A - B).traceRight` | `⊢ P (A.traceRight - B.traceRight)` |

**R13 · `rfl`** **closes** `ρ.traceRight.m = ρ.m.traceRight`: `MState.traceRight` is defined with
`M := ρ.M.traceRight`, so both sides unfold to the same term (`MState.traceRight_M` is this fact for `ρ.M`).
`rfl` also closes the subtraction of two such equations. Placeholders:
`{dA dB : Type} [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB] (ρ : MState (dA × dB))`.

| Before | After |
|---|---|
| `⊢ ρ.traceRight.m = ρ.m.traceRight` | ∅ |

---

## Part 3 · `unitaryGroup_congr` (MILESTONE)

Statement: `U ∈ @Matrix.unitaryGroup n i1 _ ℂ _ _ → U ∈ @Matrix.unitaryGroup n i2 _ ℂ _ _` for two instances
`i1 i2 : DecidableEq n`. `@` lets you pass the instance by hand. Both sides print as `U ∈ 𝐔[n]`.

**R14 · `obtain rfl : i1 = i2 := Subsingleton.elim _ _`** changes the **context**: `i2` disappears and every
`i2` becomes `i1`. `Subsingleton.elim : ∀ a b : α, a = b` holds for a type with at most one element, and
`DecidableEq α` is one (two decision procedures for `=` always agree). `obtain rfl : a = b := e` substitutes
the variable `b` away. Placeholders: `{α : Type} (i1 i2 : DecidableEq α) (P : DecidableEq α → Prop)`.

| Before | After |
|---|---|
| `i1 i2 : DecidableEq α ⊢ P i2` | `i1 : DecidableEq α ⊢ P i1` |

After R14 the goal is literally the hypothesis: `exact h`.

---

## Part 4 · `td_traceRight`

Statement: `TrDistance ρ.traceRight σ.traceRight ≤ TrDistance ρ σ`. Unfold (R15), rewrite with MILESTONE 2,
get the attaining unitary (R16), build `U ⊗ₖ 1` (R18), apply the variational bound (R17), clean up (R19,
R20 with MILESTONE 1), and compare (R21).

**R15 · `unfold TrDistance`** changes the **goal**: `TrDistance ρ σ` is replaced by its definition.
Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d)`. It unfolds every occurrence, so both
sides of the exercise change.

| Before | After |
|---|---|
| `⊢ P (TrDistance ρ σ)` | `⊢ P (1 / 2 * (ρ.m - σ.m).traceNorm)` |

**R16 · `obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1`** changes the **context**. The lemma
is `IsGreatest {x : ℝ | ∃ U : 𝐔[n], ((U.val * A).trace).re = x} A.traceNorm`. Its `.1` says the maximum is
attained: `∃ U : 𝐔[n], …`. The outer `⟨_, hUeq⟩` takes the witness apart, the inner `⟨U, hU⟩` splits the
unitary into its matrix `U` and the proof `hU`. Placeholders: `{n : Type} [Fintype n] (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ G` | `U : Matrix n n ℂ, hU : U ∈ 𝐔[n] ⊢ G` |

and the context also gains `hUeq : (↑⟨U, hU⟩ * A).trace.re = A.traceNorm`: $\operatorname{Re}\operatorname{tr}(UA) = \lVert A\rVert_1$.

**R17 · `have hle := hS.2 ⟨b, rfl⟩`** changes the **context**. For `hS : IsGreatest S a`, `hS.2` is
`∀ x ∈ S, x ≤ a`. Membership `f b ∈ {x | ∃ U, f U = x}` is `∃ U, f U = f b`, proved by `⟨b, rfl⟩`. In the
exercise `b` is the unitary `U ⊗ₖ 1` packed with a proof that it lies in the *classical* `𝐔[_]`, so
the argument is `⟨⟨_, unitaryGroup_congr _ _ _ hU'⟩, rfl⟩` (Traps). Placeholders:
`{β : Type} (f : β → ℝ) (a : ℝ) (b : β) (hS : IsGreatest {x | ∃ U, f U = x} a)`.

| Before | After |
|---|---|
| `⊢ G` | `hle : f b ≤ a ⊢ G` |

**W2: the bound with `U = 1`.** `(Matrix.traceNorm_eq_max_re_tr_U A).2 ⟨1, rfl⟩` gives
`hle : (↑1 * A).trace.re ≤ A.traceNorm`, i.e. $\operatorname{Re}\operatorname{tr}A \le \lVert A\rVert_1$:

```lean-goal
⊢ A.trace.re ≤ A.traceNorm
```

**R18 · `have hU' : … := Matrix.kronecker_mem_unitary hU (one_mem _)`** changes the **context**. The lemma
is `U₁ ∈ unitary _ → U₂ ∈ unitary _ → U₁ ⊗ₖ U₂ ∈ unitary _` (`𝐔[n]` is `unitary (Matrix n n ℂ)`), and
`one_mem _ : 1 ∈ 𝐔[m]`. Placeholders:
`{n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (U : Matrix n n ℂ) (hU : U ∈ 𝐔[n])`.
W3 swaps the factors: `Matrix.kronecker_mem_unitary (one_mem _) hV : 1 ⊗ₖ V ∈ 𝐔[n × m]`.

| Before | After |
|---|---|
| `⊢ G` | `hU' : Matrix.kroneckerMap (fun x1 x2 => x1 * x2) U 1 ∈ 𝐔[n × m] ⊢ G` |

**R19 · `dsimp only`** changes the **goal**; `dsimp only at h₁ h₂` changes the **context** the same way. It
simplifies by definitional unfolding only. Here it reduces `↑⟨U, hU⟩` (pack `U` with `hU`, then take the matrix
back out) to `U`, so `rw` can see `U * …`. In the exercise the `↑⟨_, _⟩` sit in `hUeq` and `hle`, so write
`dsimp only at hUeq hle`. Placeholders:
`{n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (hU : U ∈ 𝐔[n])`.

| Before | After |
|---|---|
| `⊢ P ↑⟨U, hU⟩` | `⊢ P U` |

**R20 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal. In the
exercise, `rw [trace_mul_traceRight] at hUeq` (MILESTONE 1). Placeholders: `{α : Type} (a b : α) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

**R21 · `gcongr`** changes the **goal**: for `c * x ≤ c * y` it proves `0 ≤ c` by itself and leaves `x ≤ y`
(the goal `case hbc`). If a hypothesis `hle : x ≤ y` is in the context, `gcongr` uses it and closes the goal.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ 1 / 2 * x ≤ 1 / 2 * y` | `⊢ x ≤ y` |

---

## Traps

- **Two `DecidableEq` instances.** `traceNorm_eq_max_re_tr_U` is stated under `open Classical`, so its `𝐔[n]`
  uses the classical instance (`Classical.propDecidable`), not your `[DecidableEq d₁]`. `hU` from R16 and the
  `hU'` you build with R18 both print as `_ ∈ 𝐔[_]`, yet `exact hU` fails with a type mismatch. Pass them through
  MILESTONE 3 (`unitaryGroup_congr _ _ _ hU`): once from classical to yours for R18, and once from yours to
  classical for R17.
- The infoview prints `U ⊗ₖ 1` as `Matrix.kroneckerMap (fun x1 x2 => x1 * x2) U 1`. You may write `⊗ₖ` in
  your own `have` statements (with `open scoped Kronecker`).
- Write `(1 : Matrix d₂ d₂ ℂ)`: a bare `U ⊗ₖ 1` does not say what size the identity is.
- `rw [Finset.sum_comm]` swaps the outermost double sum on the left side, and a second `rw` swaps it back.
  To swap inner sums, go under the outer sum first (R11).
- `Finset.sum_ite_eq` wants `if i = j`, `Finset.sum_ite_eq'` wants `if j = i`.
- After R16 and R17, `hUeq` and `hle` still contain `↑⟨_, _⟩`. Reduce them with `dsimp only at hUeq hle` (R19)
  before rewriting, so that `hUeq`, `hle` and the goal all mention the same matrix `U ⊗ₖ 1` literally.
- `gcongr` closes `1 / 2 * x ≤ 1 / 2 * y` only if `hle : x ≤ y` (with the same `x`, `y`) is already there:
  build `hle`, rewrite the goal with `rw [← hUeq]`, then call `gcongr`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `tr M` → sum | `simp only [Matrix.trace, Matrix.diag]` | R1 |
| entry of a product | `Matrix.mul_apply` | R2 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R3 |
| entry of `A ⊗ₖ B` | `simp only [Matrix.kroneckerMap_apply]` | R4 |
| entry of `1` | `Matrix.one_apply` | R5 |
| factor into an `if` | `mul_ite`, `ite_mul`, `mul_one`, `mul_zero`, `zero_mul` | R6 |
| collapse `∑ j, if i = j then f j else 0` | `Finset.sum_ite_eq`, `Finset.mem_univ`, `if_true` | R7 |
| entry of `A.traceRight` | `simp only [Matrix.traceRight, Matrix.of_apply]` | R8 |
| `a * ∑` → `∑ a *` | `Finset.mul_sum` | R9 |
| swap two sums | `rw [Finset.sum_comm]` / `Finset.sum_comm` as a term | R10 |
| equal summands | `refine Finset.sum_congr rfl fun x _ => ?_` | R11 |
| `(A - B).traceRight` | `rw [Matrix.traceRight_sub]` | R12 |
| `ρ.traceRight.m = ρ.m.traceRight` | `rfl` | R13 |
| two instances of `DecidableEq` | `obtain rfl : i1 = i2 := Subsingleton.elim _ _` | R14 |
| `TrDistance` → trace norm | `unfold TrDistance` | R15 |
| attaining unitary | `obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1` | R16 |
| `re (tr (V * A)) ≤ ‖A‖₁` | `(Matrix.traceNorm_eq_max_re_tr_U A).2 ⟨⟨V, hV⟩, rfl⟩` | R17 |
| `U ⊗ₖ 1` unitary | `Matrix.kronecker_mem_unitary hU (one_mem _)` | R18 |
| `↑⟨U, hU⟩` → `U` in hypotheses | `dsimp only at h₁ h₂` | R19 |
| rewrite a hypothesis | `rw [e] at h` | R20 |
| `c * x ≤ c * y` from `x ≤ y` | `gcongr` | R21 |
| see the state | infoview | |
