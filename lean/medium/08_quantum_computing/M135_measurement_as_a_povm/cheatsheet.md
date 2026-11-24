# M135 · Measurement as a POVM: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw`, `simp`, `exact`, `<;>`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices over an arbitrary
finite index type (`Matrix d d ℂ`, `Matrix.diagonal`, `trace`, the identity `1`), finite sums `∑`,
positive semidefiniteness, the order `≤` on `ℂ`, and physlib's `HermitianMat`, `MState`, `Prob`,
`ProbDistribution` and `POVM`.

**The physics.** Let `d` be a finite set of outcomes/basis labels. A *density matrix* (mixed state) is a
matrix $\rho \in \mathbb{C}^{d \times d}$ with $\rho = \rho^\dagger$ (Hermitian: equal to its conjugate
transpose), $\rho \succeq 0$ (positive semidefinite: $x^\dagger \rho x \ge 0$ for every vector $x$) and
$\operatorname{tr}\rho = 1$. A *POVM* (positive operator-valued measure) with outcome set $X$ is a family
$(E_x)_{x \in X}$ of Hermitian matrices with $E_x \succeq 0$ and $\sum_x E_x = 1$ (the identity). Measuring
$\rho$ gives outcome $x$ with probability $p(x) = \operatorname{tr}(E_x \rho)$ (Born rule); positivity makes
$p(x) \ge 0$ and normalisation makes $\sum_x p(x) = \operatorname{tr}\rho = 1$. The exercise takes
$X = d$ and $E_i = P_i = |i\rangle\langle i|$, the diagonal matrix with a single `1` at $(i, i)$:
$P_i \succeq 0$ (its diagonal is $\ge 0$), $\sum_i P_i = 1$ (entry $(a, b)$ is $\sum_i [a = b][a = i] = [a = b]$,
where $[\cdot]$ is 1 if true, 0 otherwise), and $\operatorname{tr}(P_i\rho) = \sum_x [x = i]\,\rho_{xx} = \rho_{ii}$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), gives the lemma's statement, lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a requirement
  on the type (a *type class*); `Fin 2`, `Fin 2 × Fin 2` and the exercise's `d` meet all of them here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[Fintype d]` | `d` is finite, so `∑ i, f i` and `trace` make sense |
| `[DecidableEq d]` | `i = j` can be tested, needed for `if i = j then … else …`, `Matrix.diagonal` and `1` |
| `Matrix d d ℂ` | complex matrices with rows and columns indexed by `d`; `M a b` is the entry in row `a`, column `b` |
| `Matrix.diagonal v` | the matrix with `v i` at `(i, i)` and `0` elsewhere (R12) |
| `M.trace`, `M.diag i` | `Matrix.trace M = ∑ i, M i i`; `M.diag i = M i i` (R23) |
| `1 a b` | entry of the identity matrix: `1` if `a = b`, else `0` (R13) |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over every element of the finite type; `Finset.univ` is "all of it" |
| `HermitianMat d ℂ` | physlib: the subtype of `Matrix d d ℂ` of Hermitian matrices (`Aᴴ = A`, where `Aᴴ` is the conjugate transpose); an element is a matrix plus a proof |
| `↑A` (with `A : HermitianMat d ℂ`) | `A.mat`, the underlying `Matrix d d ℂ` (R1, R8) |
| `HermitianMat.diagonal ℂ f` | the Hermitian diagonal matrix with real diagonal `f : d → ℝ` (R3) |
| `↑(f x)` inside `Matrix.diagonal` | the real number `f x` cast into `ℂ` (`RCLike.ofReal`, R3, R7, R14) |
| `M.PosSemidef` | `M` is Hermitian and `x† M x ≥ 0` for every vector `x` |
| `0 ≤ A` (with `A : HermitianMat d ℂ`) | `A` is positive semidefinite (R1) |
| `0 ≤ z` (with `z : ℂ`) | via `open scoped ComplexOrder`: `0 ≤ z.re` and `z.im = 0` (R7) |
| `MState d` | physlib: a density matrix, structure `⟨M, nonneg, tr⟩` with `M : HermitianMat d ℂ`, `0 ≤ M`, trace `1` |
| `↑ρ`, `↑↑ρ`, `ρ.m` | `ρ.M : HermitianMat d ℂ`; its matrix `ρ.M.mat`; `ρ.m` is the same matrix under a shorter name (R25) |
| `Prob` | physlib: `{ p : ℝ // 0 ≤ p ∧ p ≤ 1 }`, a real number in `[0, 1]`; `↑p` is the real number |
| `ProbDistribution X` | physlib: `{ f : X → Prob // ∑ i, ↑(f i) = 1 }`; it can be applied to `x : X` like a function |
| `POVM X d` | physlib: structure `⟨mats, nonneg, normalized⟩`: `mats : X → HermitianMat d ℂ`, each `0 ≤ mats x`, `∑ x, mats x = 1` |
| `{ mats := zMats, nonneg := ⋯, normalized := ⋯ }` | how `⟨zMats, zMats_nonneg, zMats_sum⟩ : POVM d d` prints; `⋯` is an elided proof |
| `Λ.measure ρ`, `↑((Λ.measure ρ) x)` | the outcome distribution of measuring `ρ` with `Λ`, and the probability of `x` as a real (R19) |
| `ProbDistribution.mk' f h0 h1` | the distribution built from `f : X → ℝ` with proofs `h0 : ∀ x, 0 ≤ f x`, `h1 : ∑ x, f x = 1` (R20) |
| `⟨fun i => ⟨r i, ⋯⟩, ⋯⟩` | the same distribution as nested anonymous constructors: a `Prob` `⟨r i, ⋯⟩` per outcome, plus the sum proof |
| `inner ℝ A B` | the real inner product of Hermitian matrices, `re tr(A B)` (R22) |
| `z.re` (with `z : ℂ`) | the real part of the complex number `z` |
| `RCLike.re z` | the real part, stated for `ℝ` and `ℂ` at once (`RCLike` = "ℝ or ℂ"); for `z : ℂ` it is `z.re` (R28) |
| `case pos`, `case neg`, `h✝ : j = i` | the two branches after `split_ifs` and their unnamed conditions (R6) |
| `i_1`, `x` | names Lean invents for bound variables |
| `↓reduceIte` | a simp procedure: `if True then u else w` → `u` (R17) |

---

## Part 1 · `zMats_nonneg`

Statement: `0 ≤ zMats i`, i.e. the projector $P_i$ is positive semidefinite. Route: Loewner order →
`PosSemidef` (R1), unfold `zMats` (R2) and its matrix (R3), diagonal criterion (R4), then one real number
per diagonal entry (R5, R6, R7).

**R1 · `rw [HermitianMat.zero_le_iff]`** changes the **goal**. The lemma is
`0 ≤ A ↔ (↑A).PosSemidef` for `A : HermitianMat n 𝕜` (`𝕜` is `ℝ` or `ℂ`). Placeholders:
`{ι : Type} [Fintype ι] (A : HermitianMat ι ℂ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ A` | `⊢ (↑A).PosSemidef` |

**R2 · `rw [D]`** changes the **goal**: a name made by `def` is replaced by its body (Lean rewrites with the
definition's equation). Here `Dg c := HermitianMat.diagonal ℂ (fun _ => c)` (`c · 1`, guide only);
placeholders `(c : ℝ) (P : HermitianMat ι ℂ → Prop)`. In the exercise, `rw [zMats]`; inside `simp`, write
`simp [zMats]`.

| Before | After |
|---|---|
| `⊢ P (Dg c)` | `⊢ P (HermitianMat.diagonal ℂ fun x => c)` |

**R3 · `rw [HermitianMat.diagonal_mat]`** changes the **goal**. The lemma is
`↑(HermitianMat.diagonal 𝕜 f) = Matrix.diagonal fun x => ↑(f x)`: the matrix of the Hermitian diagonal is the
ordinary diagonal of the cast entries. Placeholders: `{ι : Type} [DecidableEq ι] (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑(HermitianMat.diagonal ℂ f)` | `⊢ P (Matrix.diagonal fun x => ↑(f x))` |

**R4 · `rw [Matrix.posSemidef_diagonal_iff]`** changes the **goal**. The lemma is
`(Matrix.diagonal v).PosSemidef ↔ ∀ i, 0 ≤ v i`. Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι]
(v : ι → ℂ)` (any ordered `*`-ring works; `ℂ` with `ComplexOrder` does).

| Before | After |
|---|---|
| `⊢ (Matrix.diagonal v).PosSemidef` | `⊢ ∀ (i : ι), 0 ≤ v i` |

**R5 · `intro j`** changes the **context and the goal**: the `∀`-bound variable becomes a hypothesis named
`j`. Placeholders: `{ι : Type} (Q : ι → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (i : ι), Q i` | `j : ι ⊢ Q j` |

**R6 · `split_ifs`** changes the **goal list and the context**: one goal per branch of the `if`, each with
its condition as `h✝`. Placeholders: `{α : Type} (p : Prop) [Decidable p] (a b : α)`. Follow it with
`<;> simp` to treat both branches.

| Before | After |
|---|---|
| `⊢ P (if p then a else b)` | `h✝ : p ⊢ P a`, `h✝ : ¬p ⊢ P b` |

**R7 · `rw [RCLike.ofReal_nonneg]`** changes the **goal**: `0 ≤ ↑x ↔ 0 ≤ x`, a complex inequality about a
real cast becomes a real one. Placeholders: `(x : ℝ)`. `simp` applies it by itself, together with
`↑1 = 1`, `↑0 = 0`, so on numerals `simp` closes the goal outright (second example).

| Before | After |
|---|---|
| `⊢ 0 ≤ ↑x` | `⊢ 0 ≤ x` |
| `⊢ 0 ≤ ↑1` | closed by `simp` |

**W1** chains R1 → R2 → R3 → R4 → R5 → R7 on `Dg c` with `c ≥ 0`:

```lean-goal
⊢ 0 ≤ Dg c
⊢ ∀ (i : ι), 0 ≤ ↑c
⊢ 0 ≤ ↑c
⊢ 0 ≤ c
```

---

## Part 2 · `zMats_sum`

Statement: `∑ i, zMats i = 1`, the completeness relation $\sum_i |i\rangle\langle i| = 1$. Route: compare
underlying matrices (R8), push `↑` through `∑` (R9), compare entries (R10), then one `simp` that unfolds
(R2, R3) and evaluates entries (R11, R12, R13, R14) and collapses the Kronecker-delta sum (R15–R18).

**R8 · `ext1`** changes the **goal**. It uses `HermitianMat.ext : ↑A = ↑B → A = B`: two Hermitian matrices
are equal when their matrices are. Placeholders: `{ι : Type} (A B : HermitianMat ι ℂ)`.

| Before | After |
|---|---|
| `⊢ A = B` | `⊢ ↑A = ↑B` |

**R9 · `rw [HermitianMat.mat_finset_sum]`** changes the **goal**. The lemma is
`↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)`. Placeholders: `{ι κ : Type} [Fintype κ] (f : κ → HermitianMat ι ℂ)`.

| Before | After |
|---|---|
| `⊢ P ↑(∑ k, f k)` | `⊢ P (∑ i, ↑(f i))` |

**R10 · `ext a b`** changes the **context and the goal**. It uses `Matrix.ext`: matrices are equal when
every entry is. Placeholders: `{ι : Type} (M N : Matrix ι ι ℂ)`.

| Before | After |
|---|---|
| `⊢ M = N` | `a b : ι ⊢ M a b = N a b` |

**R11 · `rw [Matrix.sum_apply]`** changes the **goal**. The lemma is `(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j`.
Placeholders: `{ι κ : Type} [Fintype κ] (g : κ → Matrix ι ι ℂ) (a b : ι)`.

| Before | After |
|---|---|
| `⊢ P ((∑ k, g k) a b)` | `⊢ P (∑ c, g c a b)` |

**R12 · `rw [Matrix.diagonal_apply]`** changes the **goal**. The lemma is
`Matrix.diagonal v i j = if i = j then v i else 0`. Placeholders: `{ι : Type} [DecidableEq ι] (v : ι → ℂ)
(a b : ι)`.

| Before | After |
|---|---|
| `⊢ P (Matrix.diagonal v a b)` | `⊢ P (if a = b then v a else 0)` |

**R13 · `rw [HermitianMat.mat_one]`, then `rw [Matrix.one_apply]`** changes the **goal**. `mat_one : ↑1 = 1`
(the matrix of the Hermitian identity is the identity matrix), `one_apply : 1 i j = if i = j then 1 else 0`.
Placeholders: `{ι : Type} [DecidableEq ι] (a b : ι)`.

| Before | After `rw [HermitianMat.mat_one]` | After `rw [Matrix.one_apply]` |
|---|---|---|
| `⊢ P (↑1 a b)` | `⊢ P (1 a b)` | `⊢ P (if a = b then 1 else 0)` |

**R14 · `simp only [MonoidWithZeroHom.map_ite_one_zero]`** changes the **goal**. The lemma is
`f (if p then 1 else 0) = if p then 1 else 0` for a map `f` preserving `*`, `1`, `0`; the cast
`ℝ → ℂ` is one. Use `simp`, not `rw`: `rw` does not recognise the cast as such a map. Placeholders:
`(p : Prop) [Decidable p]`.

| Before | After |
|---|---|
| `⊢ P ↑(if p then 1 else 0)` | `⊢ P (if p then 1 else 0)` |

**R15 · `rw [Finset.sum_ite_irrel]`** changes the **goal**. The lemma is
`(∑ x ∈ s, if p then f x else g x) = if p then ∑ x ∈ s, f x else ∑ x ∈ s, g x`: a condition that does not
mention the summation variable moves outside. Placeholders: `{κ : Type} [Fintype κ] (p : Prop) [Decidable p]
(f g : κ → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k, if p then f k else g k)` | `⊢ P (if p then ∑ x, f x else ∑ x, g x)` |

**R16 · `rw [Finset.sum_ite_eq]`** changes the **goal**. The lemma is
`(∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`: the delta picks the term `x = a`.
Placeholders: `{κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (u : κ → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, if a = x then u x else 0)` | `⊢ P (if a ∈ Finset.univ then u a else 0)` |

**R17 · `simp only [Finset.mem_univ, ↓reduceIte]`** changes the **goal**: `a ∈ Finset.univ` is `True`, and
`if True then u else w` is `u`. Placeholders: `{κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (u w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then u else w)` | `⊢ P u` |

**R18 · `rw [Finset.sum_const_zero]`** changes the **goal**: `∑ x ∈ s, 0 = 0`. Placeholders: `{κ : Type}
[Fintype κ]`.

| Before | After |
|---|---|
| `⊢ P (∑ _x, 0)` | `⊢ P 0` |

**W2** sums one-entry diagonals: after `ext a b` (R10),

```lean-goal
⊢ (∑ k, Matrix.diagonal fun j => if j = k then f k else 0) a b = Matrix.diagonal f a b
```

and `simp [Matrix.sum_apply, Matrix.diagonal_apply]` closes it (R11, R12, then R15–R18 by itself).
In `zMats_sum` the same `simp` also needs the names for R2, R3, R13 (`zMats`, `HermitianMat.diagonal_mat`,
`Matrix.one_apply`); R14 and R15–R18 are in `simp`'s default set.

---

## Part 3 · `z_born`

Statement: measuring `ρ` with the POVM `⟨zMats, zMats_nonneg, zMats_sum⟩` gives outcome `i` with probability
`(ρ.m i i).re`. Parts 1 and 2 are its proof fields, so they must be proved first. Route: unfold the
measurement down to `inner ℝ (zMats i) ↑ρ` (R19–R21), turn the inner product into a trace (R22), unfold
`zMats` (R2, R3), then evaluate the trace (R23–R28).

**R19 · `simp only [POVM.measure]`** changes the **goal**: by definition
`Λ.measure ρ = ProbDistribution.mk' (fun x => inner ℝ (Λ.mats x) ↑ρ) ⋯ ⋯`. Placeholders:
`{X ι : Type} [Fintype X] [Fintype ι] [DecidableEq ι] (Λ : POVM X ι) (ρ : MState ι) (x : X)`.

| Before | After |
|---|---|
| `⊢ P ↑((Λ.measure ρ) x)` | `⊢ P ↑((ProbDistribution.mk' (fun x => inner ℝ (Λ.mats x) ↑ρ) ⋯ ⋯) x)` |

**R20 · `simp only [ProbDistribution.mk']`** changes the **goal**: `mk'` unfolds to nested anonymous
constructors, one `Prob` per outcome. Placeholders: `{X : Type} [Fintype X] (f : X → ℝ)
(h0 : ∀ x, 0 ≤ f x) (h1 : ∑ x, f x = 1) (x : X)`.

| Before | After |
|---|---|
| `⊢ P ↑((ProbDistribution.mk' f h0 h1) x)` | `⊢ P ↑(⟨fun i => ⟨f i, ⋯⟩, h1⟩ x)` |
| `⊢ P ↑(⟨fun i => ⟨f i, ⋯⟩, h1⟩ x)` | `⊢ P (f x)` (after R21) |

**R21 · `simp only [ProbDistribution.funlike_apply]`** changes the **goal**. The lemma is
`⟨d, h⟩ x = d x`: applying a distribution applies its function. `simp` also removes the `Prob` wrapper
(`↑⟨r, ⋯⟩ = r`) by itself. Placeholders: `{X : Type} [Fintype X] (d : X → Prob)
(hd : ∑ x, ↑(d x) = 1) (x : X)`.

| Before | After |
|---|---|
| `⊢ P ↑(⟨d, hd⟩ x)` | `⊢ P ↑(d x)` |

**R22 · `rw [HermitianMat.inner_eq_re_trace]`** changes the **goal**. The lemma is
`inner ℝ A B = RCLike.re (↑A * ↑B).trace`, i.e. $\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(AB)$.
Placeholders: `{ι : Type} [Fintype ι] (A B : HermitianMat ι ℂ)`.

| Before | After |
|---|---|
| `⊢ P (inner ℝ A B)` | `⊢ P (RCLike.re (↑A * ↑B).trace)` |

**R23 · `simp only [Matrix.trace]`, then `simp only [Matrix.diag_apply]`** changes the **goal**: the trace
becomes the sum of diagonal entries. Placeholders: `{ι : Type} [Fintype ι] (M : Matrix ι ι ℂ)`.

| Before | After `simp only [Matrix.trace]` | After `simp only [Matrix.diag_apply]` |
|---|---|---|
| `⊢ P M.trace` | `⊢ P (∑ i, M.diag i)` | `⊢ P (∑ x, M x x)` |

**R24 · `rw [Matrix.diagonal_mul]`** changes the **goal**. The lemma is
`(Matrix.diagonal v * M) i j = v i * M i j`: multiplying by a diagonal on the left scales row `i` by `v i`.
Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι)`.

| Before | After |
|---|---|
| `⊢ P ((Matrix.diagonal v * M) i j)` | `⊢ P (v i * M i j)` |

**R25 · `rw [MState.mat_M]`** changes the **goal**. The lemma is `↑↑ρ = ρ.m`. Placeholders:
`{ι : Type} [Fintype ι] [DecidableEq ι] (ρ : MState ι)`. The right side of `z_born` is stated with `ρ.m`,
so this makes both sides talk about the same name.

| Before | After |
|---|---|
| `⊢ P ↑↑ρ` | `⊢ P ρ.m` |

**R26 · `rw [ite_mul]`, then `rw [one_mul, zero_mul]`** changes the **goal**. `ite_mul :
(if p then a else b) * c = if p then a * c else b * c`. Placeholders: `(p : Prop) [Decidable p] (z : ℂ)`.

| Before | After `rw [ite_mul]` | After `rw [one_mul, zero_mul]` |
|---|---|---|
| `⊢ P ((if p then 1 else 0) * z)` | `⊢ P (if p then 1 * z else 0 * z)` | `⊢ P (if p then z else 0)` |

**R27 · `rw [Finset.sum_ite_eq']`** changes the **goal**. The lemma is
`(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`, R16 with the equation the other way round.
Which one applies depends on whether the summation variable is left or right of `=`. Placeholders as R16.

| Before | After |
|---|---|
| `⊢ P (∑ x, if x = a then u x else 0)` | `⊢ P (if a ∈ Finset.univ then u a else 0)` |

**R28 · `rw [RCLike.re_to_complex]`** changes the **goal**: `RCLike.re z = z.re` for `z : ℂ`. Placeholders:
`(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (RCLike.re z)` | `⊢ P z.re` |

**W3**: `simp [Matrix.trace, Matrix.diagonal_mul]` closes
`(Matrix.diagonal v * M).trace = ∑ i, v i * M i i` (R23, R24).

**W4: Born rule for any POVM.** R19 → R20 → R21 → R22 → R25 on an arbitrary `Λ : POVM X ι`:

```lean-goal
⊢ ↑((Λ.measure ρ) x) = RCLike.re (↑(Λ.mats x) * ρ.m).trace
⊢ ↑((ProbDistribution.mk' (fun x => inner ℝ (Λ.mats x) ↑ρ) ⋯ ⋯) x) = RCLike.re (↑(Λ.mats x) * ρ.m).trace
⊢ ↑(⟨fun i => ⟨inner ℝ (Λ.mats i) ↑ρ, ⋯⟩, ⋯⟩ x) = RCLike.re (↑(Λ.mats x) * ρ.m).trace
⊢ inner ℝ (Λ.mats x) ↑ρ = RCLike.re (↑(Λ.mats x) * ρ.m).trace
⊢ RCLike.re (↑(Λ.mats x) * ↑↑ρ).trace = RCLike.re (↑(Λ.mats x) * ρ.m).trace
```

In `z_born`, after these steps and `rw [zMats, HermitianMat.diagonal_mat]`, the trace is a sum over `x` of
`↑(if x = i then 1 else 0) * ρ.m x x`; R14, R26 make it a delta sum, R27 and R17 pick `ρ.m i i`, R28 matches
the right side. `simp [Matrix.trace, Matrix.diagonal_mul, …]` does all of that at once.

---

## Traps

- `rw [MonoidWithZeroHom.map_ite_one_zero]` fails on the cast `↑(if p then 1 else 0)`: use
  `simp only [MonoidWithZeroHom.map_ite_one_zero]` (R14) or plain `simp`.
- `Finset.sum_ite_eq` vs `Finset.sum_ite_eq'`: they differ only in `a = x` vs `x = a` (R16, R27). Wrong
  one → `rw` fails; `simp` knows both.
- Plain `ext` on an equation of `HermitianMat`s goes all the way to entries with unnamed indices
  (`↑(∑ k, f k) i✝ j✝ = …`), with `↑` still outside the sum. `ext1` stops at the matrices, so you can
  `rw [HermitianMat.mat_finset_sum]` (R8, R9) and then name the indices with `ext a b` (R10).
- `(⟨d, hd⟩ : ProbDistribution X) x` does not elaborate: `ProbDistribution X` unfolds to a subtype before
  Lean looks for a function coercion. You never need to write this; it is only how the goal prints.
- `z_born` mentions `zMats_nonneg` and `zMats_sum` inside its statement: those two must be proved
  (sorry-free) for `z_born` to count as done.
- `x ≤ y` on `ℂ` is not "compare absolute values": it requires equal imaginary parts (`ComplexOrder`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 ≤ A` (Hermitian) → `PosSemidef` | `rw [HermitianMat.zero_le_iff]` | R1 |
| unfold a `def` | `rw [zMats]` / `simp [zMats]` | R2 |
| matrix of `HermitianMat.diagonal` | `rw [HermitianMat.diagonal_mat]` | R3 |
| diagonal PSD ↔ entries `≥ 0` | `rw [Matrix.posSemidef_diagonal_iff]` | R4 |
| `∀` → variable | `intro j` | R5 |
| case on an `if` | `split_ifs <;> simp` | R6 |
| `0 ≤ ↑x` in `ℂ` | `rw [RCLike.ofReal_nonneg]` / `simp` | R7 |
| equal `HermitianMat`s | `ext1` | R8 |
| `↑(∑ …)` → `∑ ↑…` | `rw [HermitianMat.mat_finset_sum]` | R9 |
| matrix equality → entries | `ext a b` | R10 |
| entries of `∑`, `diagonal`, `1` | `Matrix.sum_apply`, `Matrix.diagonal_apply`, `HermitianMat.mat_one`, `Matrix.one_apply` | R11–R13 |
| cast of a `1`/`0` `if` | `simp only [MonoidWithZeroHom.map_ite_one_zero]` | R14 |
| delta sums | `Finset.sum_ite_irrel`, `Finset.sum_ite_eq`, `Finset.sum_ite_eq'`, `Finset.mem_univ`, `Finset.sum_const_zero` | R15–R18, R27 |
| unfold a measurement | `simp only [POVM.measure, ProbDistribution.mk', ProbDistribution.funlike_apply]` | R19–R21 |
| inner product → trace | `rw [HermitianMat.inner_eq_re_trace]` | R22 |
| trace → `∑ i, M i i` | `simp only [Matrix.trace, Matrix.diag_apply]` | R23 |
| `(diagonal v * M) i j` | `rw [Matrix.diagonal_mul]` | R24 |
| `↑↑ρ` → `ρ.m` | `rw [MState.mat_M]` | R25 |
| `(if p then 1 else 0) * z` | `simp only [ite_mul, one_mul, zero_mul]` | R26 |
| `RCLike.re z` → `z.re` | `rw [RCLike.re_to_complex]` | R28 |
| see the state | infoview | |
