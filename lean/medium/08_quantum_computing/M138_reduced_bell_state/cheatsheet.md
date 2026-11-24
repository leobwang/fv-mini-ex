# M138 · Reduced Bell state is maximally mixed: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's quantum states (`MState`, `Ket`,
`HermitianMat`), the partial trace `traceLeft`, the maximally entangled state `Ket.MES`, the uniform
distribution `ProbDistribution.uniform`, and Mathlib's `Matrix.diagonal`, finite sums `∑`, casts
`ℕ → ℝ → ℂ` and `Real.sqrt`. If you did M126, R24–R26 are its √ entries again.

## The objects

- `d` is a finite type (`[Fintype d]`) with decidable equality (`[DecidableEq d]`) and at least one element
  (`[Nonempty d]`). Write $n = |d|$, printed `Fintype.card d`.
- `Ket d` is a unit vector $\psi : d \to \mathbb C$, $\sum_x |\psi_x|^2 = 1$. It is a structure: `ψ.vec : d → ℂ`
  is the stored vector, and `ψ x` (a ket used as a function) unfolds to `ψ.vec x` (R16).
- `HermitianMat d ℂ` is the subtype of matrices $A$ with $A^\dagger = A$; `A.mat : Matrix d d ℂ` is the
  underlying matrix.
- `MState d` is a density matrix: a structure with `ρ.M : HermitianMat d ℂ`, positive semidefinite, trace 1.
  `ρ.m : Matrix d d ℂ` is *defined* as `ρ.M.mat`. `MState.ext_m` says two states with equal `m` are equal.
- `MState.pure ψ` is $|\psi\rangle\langle\psi|$: entry $(i, j)$ is $\psi_i \overline{\psi_j}$ (`MState.pure_apply`).
- `Ket.MES d : Ket (d × d)` is $\Phi(x, y) = [x = y]/\sqrt n$, i.e. $|\Phi\rangle = \sum_i |i\rangle|i\rangle/\sqrt n$.
- `ρ.traceLeft : MState d₂` for `ρ : MState (d₁ × d₂)` is the partial trace over the left factor:
  $(\mathrm{tr}_1 A)_{ij} = \sum_k A_{(k,i),(k,j)}$ (`Matrix.traceLeft`).
- `MState.uniform` is `MState.ofClassical ProbDistribution.uniform`: the diagonal matrix with entries
  `ProbDistribution.uniform x = 1 / n`, i.e. $I/n$.

The theorem: $\mathrm{tr}_1 |\Phi\rangle\langle\Phi| = I/n$. Entry $(i, j)$ of the left side is
$\sum_k \Phi(k,i)\overline{\Phi(k,j)}$; only $k = i = j$ contributes, giving $(1/\sqrt n)^2 = 1/n$ on the diagonal
and $0$ off it.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[DivisionCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `inst✝ : Fintype d` | an unnamed instance hypothesis from a `[…]` binder |
| `ρ.m` | `MState.m ρ`, the density matrix of `ρ` as a plain `Matrix d d ℂ` |
| `↑ρ` | `ρ.M`, the `HermitianMat` inside the state `ρ` |
| `↑A` (A a `HermitianMat`) | `A.mat`, the plain matrix |
| `↑↑ρ` | `ρ.M.mat`, which is the same matrix as `ρ.m` but written so `.M`/`.mat` lemmas match (R3) |
| `↑ρ.traceLeft` | `(ρ.traceLeft).M`: take the partial trace of the state, then its `HermitianMat` |
| `(↑ρ).traceLeft` | `(ρ.M).traceLeft`: the partial trace of the `HermitianMat` (R4) |
| `(MState.pure ψ).m.traceLeft` | `Matrix.traceLeft` of the plain matrix |
| `of (fun i j => e) i j` | `Matrix.of` turns a function into a matrix; applying it gives `e` back (R12) |
| `diagonal f` | `Matrix.diagonal f`: `f i` on the diagonal, `0` elsewhere |
| `HermitianMat.diagonal ℂ f` | the same, for a real `f`, as a `HermitianMat` |
| `ProbDistribution.uniform x` | the uniform probability of `x`, of type `Prob` (a real in $[0, 1]$) |
| `↑↑(ProbDistribution.uniform i)` | that probability cast `Prob → ℝ → ℂ` |
| `∑ x, f x` | $\sum_{x \in d} f(x)$, a sum over all of `d` (`Finset.univ`) |
| `Fintype.card d`, `Finset.univ.card` | $n = \lvert d\rvert$ (two spellings, R22) |
| `↑√↑(Fintype.card d)` | $\sqrt n$: `n` cast `ℕ → ℝ`, `Real.sqrt`, then cast `ℝ → ℂ` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate $\bar z$ |
| `(Ket.MES d) (x, i)` | $\Phi(x, i)$, the amplitude of the basis state $\lvert x\rangle\lvert i\rangle$ |
| `case pos`, `case neg` | the two goals after `by_cases`: condition true / false |

---

## Part 1 · `traceLeft_MES`

Statement: `(MState.pure (Ket.MES d)).traceLeft = MState.uniform`. Tracing out the left half of the maximally
entangled state gives the maximally mixed state. Plan: reduce to one matrix entry (R1–R3), unwrap both sides
down to plain matrices (R4–R13), split on `i = j` (R14, R15), evaluate (R16–R23), and finish the √ fact
(R24–R28) or the zero (R29).

### From an equation of states to an equation of numbers

**R1 · `apply MState.ext_m`** changes the **goal**: equality of states becomes equality of their matrices.
The lemma is `MState.ext_m : ρ₁.m = ρ₂.m → ρ₁ = ρ₂`. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d)`.

| Before | After |
|---|---|
| `⊢ ρ = σ` | `⊢ ρ.m = σ.m` |

**R2 · `ext i j`** changes the **goal and the context**: a matrix equation becomes one entry, with fresh
indices. Placeholders: `{d : Type} (A B : Matrix d d ℂ)`. The index type is a general `d`, not `Fin n`, so you
cannot enumerate entries with `fin_cases`; you reason about a general `(i, j)`.

| Before | After |
|---|---|
| `⊢ A = B` | `i j : d ⊢ A i j = B i j` |

**R3 · `show ρ.M.mat i j = σ.M.mat i j`** changes the **goal** to a definitionally equal one. `ρ.m` is defined as
`ρ.M.mat`, so `show` accepts the restatement; afterwards the goal mentions `.M` and `.mat` literally and the
`rw` lemmas R4–R9 can find them. Placeholders: `(ρ σ : MState d) (i j : d)`. In the exercise, write the full
left and right sides; `(MState.uniform : MState d)` needs the type ascription.

| Before | After |
|---|---|
| `⊢ ρ.m i j = σ.m i j` | `⊢ ↑↑ρ i j = ↑↑σ i j` |

### Unwrapping the left side

**R4 · `rw [MState.traceLeft_M]`** changes the **goal**: the lemma is `↑ρ.traceLeft = (↑ρ).traceLeft`. It moves
the partial trace from the state level to the `HermitianMat` level. Placeholders:
`{d₁ d₂ : Type}` (both `[Fintype]`, `[DecidableEq]`) `(ρ : MState (d₁ × d₂))`.

| Before | After |
|---|---|
| `⊢ P ↑ρ.traceLeft` | `⊢ P (↑ρ).traceLeft` |

**R5 · `rw [HermitianMat.traceLeft_mat]`** changes the **goal**: `↑A.traceLeft = (↑A).traceLeft`, one level
down, from `HermitianMat` to `Matrix`. Placeholders: `{d₁ d₂ : Type} [Fintype d₁] (A : HermitianMat (d₁ × d₂) ℂ)`.

| Before | After |
|---|---|
| `⊢ P ↑A.traceLeft` | `⊢ P (↑A).traceLeft` |

**R6 · `rw [MState.mat_M]`** changes the **goal**: `ρ.M.mat = ρ.m` folds `↑↑ρ` back into `ρ.m`, the form
`MState.pure_apply` (R13) is stated for. Placeholders: `(ρ : MState d)`.

| Before | After |
|---|---|
| `⊢ P ↑↑ρ` | `⊢ P ρ.m` |

### Unwrapping the right side

**R7 · `rw [MState.uniform]`** changes the **goal**: it unfolds the definition
`MState.uniform = MState.ofClassical ProbDistribution.uniform`. Needs `[Nonempty d]`.

| Before | After |
|---|---|
| `⊢ P MState.uniform` | `⊢ P (MState.ofClassical ProbDistribution.uniform)` |

**R8 · `rw [MState.coe_ofClassical]`** changes the **goal**: `(ofClassical p).M = HermitianMat.diagonal ℂ (p ·)`.
A classical distribution becomes the diagonal Hermitian matrix of its probabilities. Placeholders:
`(p : ProbDistribution d)`.

| Before | After |
|---|---|
| `⊢ P ↑(MState.ofClassical p)` | `⊢ P (HermitianMat.diagonal ℂ fun x => ↑(p x))` |

**R9 · `rw [HermitianMat.diagonal_mat]`** changes the **goal**: `(HermitianMat.diagonal 𝕜 f).mat =
Matrix.diagonal (f · : n → 𝕜)`. Placeholders: `[DecidableEq d] (f : d → ℝ)`, with `𝕜 = ℂ`.

| Before | After |
|---|---|
| `⊢ P ↑(HermitianMat.diagonal ℂ f)` | `⊢ P (diagonal fun x => ↑(f x))` |

**R10 · `rw [Matrix.diagonal_apply]`** changes the **goal**: `diagonal f i j = if i = j then f i else 0`.
Placeholders: `[DecidableEq d] (f : d → ℂ) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P (diagonal f i j)` | `⊢ P (if i = j then f i else 0)` |

R4–R10 can go in one `rw [ … ]` list, in this order, right after R3.

### The partial trace as a sum

**R11 · `simp only [Matrix.traceLeft]`** changes the **goal**: it unfolds
`Matrix.traceLeft A = of fun i₁ j₁ => ∑ i₂, A (i₂, i₁) (i₂, j₁)`. Placeholders:
`{d₁ d₂ : Type} [Fintype d₁] (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₂)`.

| Before | After |
|---|---|
| `⊢ P (A.traceLeft i j)` | `⊢ P (of (fun i₁ j₁ => ∑ i₂, A (i₂, i₁) (i₂, j₁)) i j)` |

**R12 · `Matrix.of_apply`** changes the **goal**: `of f i j = f i j`. With `f` a `fun`, Lean also substitutes
`i, j` into its body. Placeholders: `(f : d → d → ℂ) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P (of f i j)` | `⊢ P (f i j)` |

**R13 · `simp only [MState.pure_apply]`** changes the **goal**: `(pure ψ).m i j = ψ i * conj (ψ j)`. Use `simp only`,
not `rw`: the entries sit under the bound variable of `∑`, where `rw` cannot rewrite. Placeholders:
`(ψ : Ket d) (i : d)`.

| Before | After |
|---|---|
| `⊢ P (∑ k, (MState.pure ψ).m k i)` | `⊢ P (∑ x, ψ x * (starRingEnd ℂ) (ψ i))` |

After R11–R13 the exercise's goal is
`∑ x, (Ket.MES d) (x, i) * (starRingEnd ℂ) ((Ket.MES d) (x, j)) = if i = j then ↑↑(ProbDistribution.uniform i) else 0`.

### Case split

**R14 · `by_cases h : i = j`** changes the **goal list**: one goal becomes two, `case pos` with `h : i = j` and
`case neg` with `h : ¬i = j`. Handle each with a `·` bullet. Placeholders: `(i j : d) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : i = j ⊢ G`, `h : ¬i = j ⊢ G` |

**R15 · `subst h`** changes the **context**: with `h : i = j` it removes `j` and `h` and replaces every `j` by `i`.
Placeholders: `(i j : d) (P : d → d → Prop)`.

| Before | After |
|---|---|
| `h : i = j ⊢ P i j` | `i : d ⊢ P i i` |

### Evaluating the entries

`simp [Ket.MES, Ket.apply]` does all of R16–R23 in one call (W3 shows the same collapse on another vector). The
entries show what each piece does, so you can read what `simp` left.

**R16 · `rw [Ket.apply]`** changes the **goal**: `ψ x = ψ.vec x`. Needed because `Ket.MES` is defined through its
`vec` field. Placeholders: `[Fintype d] (ψ : Ket d) (x : d)`.

| Before | After |
|---|---|
| `⊢ P (ψ x)` | `⊢ P (ψ.vec x)` |

**R17 · `simp only [Ket.MES]`** changes the **goal**: it unfolds the amplitude
`(Ket.MES d).vec (x, y) = if x = y then 1 / ↑√↑(Fintype.card d) else 0`. Placeholders: `[Fintype d] [Nonempty d] (x y : d)`.

| Before | After |
|---|---|
| `⊢ P ((Ket.MES d).vec (x, y))` | `⊢ P (if x = y then 1 / ↑√↑(Fintype.card d) else 0)` |

**R18 · `rw [one_div]`** changes the **goal**: `one_div : 1 / a = a⁻¹`. Placeholders:
`{α : Type} [DivInvMonoid α] (a : α)` (α has `*`, `/`, `⁻¹`; `ℝ` and `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (1 / a)` | `⊢ P a⁻¹` |

**R19 · `rw [ite_mul]`, then `rw [zero_mul]`** change the **goal**: `ite_mul : (if c then a else b) * x = if c then
a * x else b * x`, `zero_mul : 0 * x = 0`. Together they push a factor into an indicator. Placeholders:
`{α : Type} [MulZeroClass α] (c : Prop) [Decidable c] (a b : α)` (α has `*` and a `0` with `0 * x = 0`; `ℂ` qualifies).

| Before | After `rw [ite_mul]` | After `rw [zero_mul]` |
|---|---|---|
| `⊢ P ((if c then a else 0) * b)` | `⊢ P (if c then a * b else 0 * b)` | `⊢ P (if c then a * b else 0)` |

**R20 · `rw [Finset.sum_ite_eq']`, then `rw [if_pos (Finset.mem_univ a)]`** change the **goal**: the lemma is
`(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`, so a sum of an indicator keeps the single term
`x = a`; `Finset.mem_univ a : a ∈ Finset.univ` removes the test. Placeholders:
`{ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (b : ι → M)` (M has `+` and `0`; `ℂ` qualifies).

| Before | After `rw [Finset.sum_ite_eq']` | After `rw [if_pos …]` |
|---|---|---|
| `⊢ P (∑ x, if x = a then b x else 0)` | `⊢ P (if a ∈ Finset.univ then b a else 0)` | `⊢ P (b a)` |

**R21 · `rw [map_inv₀]`, then `rw [Complex.conj_ofReal]`** change the **goal**: conjugation commutes with `⁻¹`
(`map_inv₀ : f a⁻¹ = (f a)⁻¹` for a ring map `f`) and fixes real numbers (`Complex.conj_ofReal : conj ↑r = ↑r`).
Placeholders: `(r : ℝ)`.

| Before | After `rw [map_inv₀]` | After `rw [Complex.conj_ofReal]` |
|---|---|---|
| `⊢ P ((starRingEnd ℂ) (↑r)⁻¹)` | `⊢ P ((starRingEnd ℂ) ↑r)⁻¹` | `⊢ P (↑r)⁻¹` |

**R22 · `rw [ProbDistribution.uniform_def]`, then `rw [Finset.card_univ]`** change the **goal**:
`↑(uniform y) = 1 / ↑Finset.univ.card` and `Finset.univ.card = Fintype.card α`. Placeholders:
`{α : Type} [Fintype α] [Nonempty α] (y : α)`.

| Before | After `uniform_def` | After `card_univ` |
|---|---|---|
| `⊢ P ↑(ProbDistribution.uniform y)` | `⊢ P (1 / ↑Finset.univ.card)` | `⊢ P (1 / ↑(Fintype.card α))` |

**R23 · `rw [if_pos rfl]`, `rw [if_neg h]`** change the **goal**: an `if` whose condition is proved (`rfl : i = i`)
or refuted (`h : ¬i = j`) becomes one branch. `simp` decides `i = i` by itself; for `i = j` give it `h`.
Placeholders: `{α d : Type} [DecidableEq d] (i j : d) (a b : α) (h : ¬i = j)`.

| Before | After `if_pos rfl` | After `if_neg h` |
|---|---|---|
| `⊢ P (if i = i then a else b) ∧ P (if i = j then a else b)` | `⊢ P a ∧ P (if i = j then a else b)` | `⊢ P a ∧ P b` |

In `case pos`, after `subst h` and `simp [Ket.MES, Ket.apply]`, what is left is
`(↑√↑(Fintype.card d))⁻¹ * (↑√↑(Fintype.card d))⁻¹ = (↑(Fintype.card d))⁻¹`, i.e. $(1/\sqrt n)^2 = 1/n$
written as a product. W4 runs R24–R28 on the same shape with $2n$ in place of $n$.

### The √ fact

**R24 · `rw [← mul_inv]`** changes the **goal**. The lemma is `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`, and `←` uses
it right to left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)` (commutative `*` with `⁻¹`; `ℂ`
and `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R25 · `rw [← Complex.ofReal_mul]`** changes the **goal**. The lemma is `↑(x * y) = ↑x * ↑y`; right to left it
moves `*` inside the `ℝ → ℂ` cast so a real lemma can apply. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R26 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. The lemma is `0 ≤ x → √x * √x = x`: the goal is
rewritten and a side goal `0 ≤ x` is added. Pass the proof as an argument to avoid the side goal (R27).
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R27 · `Nat.cast_nonneg n`** **closes** `⊢ 0 ≤ ↑n`: a natural number cast into `ℝ` is nonnegative. In the
exercise write `rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]`; the `_` is the `n` Lean infers.

| Before | After |
|---|---|
| `n : ℕ ⊢ 0 ≤ ↑n` | closed |

**R28 · `Complex.ofReal_natCast`** changes the **goal**: `((n : ℝ) : ℂ) = (n : ℂ)`, two casts become one.
`simp` applies it by itself, and it is what closes `(↑↑n)⁻¹ = (↑n)⁻¹`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑↑n` | `⊢ P ↑n` |

### Off the diagonal

In `case neg`, `simp [Ket.MES, Ket.apply, h]` does R16–R23 (with `if_neg h` from R23) and then R29; both sides
become `0`.

**R29 · `rw [map_zero]`, then `rw [mul_zero]`** change the **goal**: `conj 0 = 0`, then `a * 0 = 0`.
Placeholders: `(a : ℂ)`.

| Before | After `map_zero` | After `mul_zero` |
|---|---|---|
| `⊢ P (a * (starRingEnd ℂ) 0)` | `⊢ P (a * 0)` | `⊢ P 0` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: right-side unwrap for a general distribution `p`.** R3, then R8, R9, R10:

```lean-goal
⊢ (MState.ofClassical p).m i j = if i = j then ↑↑(p i) else 0
⊢ ↑↑(MState.ofClassical p) i j = if i = j then ↑↑(p i) else 0
⊢ ↑(HermitianMat.diagonal ℂ fun x => ↑(p x)) i j = if i = j then ↑↑(p i) else 0
⊢ diagonal (fun x => ↑↑(p x)) i j = if i = j then ↑↑(p i) else 0
⊢ (if i = j then ↑↑(p i) else 0) = if i = j then ↑↑(p i) else 0
```

The last goal needs `rfl`: the two `↑` from `ℝ` to `ℂ` print alike but are different functions (Traps).

**W2: left-side unwrap for a general ket `ψ : Ket (d₁ × d₂)`.** R3, then R4–R6, then R11–R12, then R13:

```lean-goal
⊢ (MState.pure ψ).traceLeft.m i j = ∑ k, ψ (k, i) * (starRingEnd ℂ) (ψ (k, j))
⊢ ↑↑(MState.pure ψ).traceLeft i j = ∑ k, ψ (k, i) * (starRingEnd ℂ) (ψ (k, j))
⊢ (MState.pure ψ).m.traceLeft i j = ∑ k, ψ (k, i) * (starRingEnd ℂ) (ψ (k, j))
⊢ ∑ i₂, (MState.pure ψ).m (i₂, i) (i₂, j) = ∑ k, ψ (k, i) * (starRingEnd ℂ) (ψ (k, j))
```

**W3: one `simp` collapses a sum of indicator products** (R19, R20, R21, R23):

```lean-goal
⊢ ∑ x, (if x = a then ↑c else 0) * (starRingEnd ℂ) (if x = a then ↑c else 0) = ↑c * ↑c
```

**W4: the √ fact for $\sqrt{2n}$**, R24, R25, R26 with R27, R28:

```lean-goal
⊢ (↑√↑(2 * n))⁻¹ * (↑√↑(2 * n))⁻¹ = (↑(2 * n))⁻¹
⊢ (↑√↑(2 * n) * ↑√↑(2 * n))⁻¹ = (↑(2 * n))⁻¹
⊢ (↑(√↑(2 * n) * √↑(2 * n)))⁻¹ = (↑(2 * n))⁻¹
⊢ (↑↑(2 * n))⁻¹ = (↑(2 * n))⁻¹
```

---

## Traps

- Without R3, `rw [MState.traceLeft_M]` fails with "did not find an occurrence of the pattern": `ρ.traceLeft.m`
  contains no `.M`, because `MState.m` is a definition that `rw` does not unfold. `show` with `.M.mat` first.
- The `show` line must state the right side with its type: `(MState.uniform : MState d).M.mat i j`.
- `MState.pure_apply` sits under `∑ x, …` after R11–R12: use `simp only`, not `rw` (R13).
- Split on `i = j` (R14) before evaluating; with a general `d` there is no `fin_cases`.
- Do not `simp` the whole goal before the R4–R10 `rw` chain: `simp` does some of those steps itself and
  rewrites the coercions into other forms (`↑↑ρ i j` becomes the `HermitianMat` entry `↑ρ i j`), so the
  `rw` list no longer matches.
- Two casts `ℝ → ℂ` print as the same `↑`: `Complex.ofReal` and `RCLike.ofReal` (from `HermitianMat.diagonal`,
  which works over any `RCLike 𝕜`). `rw` treats them as different; `rfl` or `simp` sees they agree (W1).
- `simp` leaves `(√n)⁻¹ * (√n)⁻¹`, a product, never `(√n)⁻¹ ^ 2`: use the `*` route R24–R26, not `sq_sqrt`.
- `Real.mul_self_sqrt` needs `0 ≤ ↑n`; pass `(Nat.cast_nonneg _)` (R27).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| states equal ← matrices equal | `apply MState.ext_m` | R1 |
| matrix equation → one entry | `ext i j` | R2 |
| expose `.M.mat` | `show ρ.M.mat i j = σ.M.mat i j` | R3 |
| partial trace down to a `Matrix` | `rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M]` | R4–R6 |
| uniform state → `if i = j then …` | `rw [MState.uniform, MState.coe_ofClassical, HermitianMat.diagonal_mat, Matrix.diagonal_apply]` | R7–R10 |
| partial trace entry → `∑` | `simp only [Matrix.traceLeft, Matrix.of_apply]` | R11, R12 |
| pure-state entry → `ψ i * conj (ψ j)` | `simp only [MState.pure_apply]` | R13 |
| diagonal vs off-diagonal | `by_cases h : i = j`, then `subst h` | R14, R15 |
| evaluate `Ket.MES` and collapse the sum | `simp [Ket.MES, Ket.apply]` (add `h` off the diagonal) | R16–R23, R29 |
| `(√n)⁻¹ * (√n)⁻¹ → n⁻¹` | `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]` | R24–R27 |
| `↑↑n → ↑n` | `simp` (uses `Complex.ofReal_natCast`) | R28 |
| see the state | infoview | |
