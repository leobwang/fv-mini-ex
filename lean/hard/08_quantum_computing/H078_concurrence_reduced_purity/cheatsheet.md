# H078 · Concurrence and reduced purity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033); 2×2 matrix entries and `Fin.sum_univ_two` as in M126
(repeated here). **New here:** physlib's quantum states (`Ket`, `MState`, `HermitianMat`, the partial trace
`traceRight`, `purity`, the subtype `Prob`), Mathlib's complex numbers taken apart into real and imaginary
parts (`Complex.normSq`, `.re`, `.im`), and the closing tactics `linear_combination` and `nlinarith`.

**The mathematics.** Write `a, b, c, d` for the amplitudes `ψ (0,0), ψ (0,1), ψ (1,0), ψ (1,1)` of a
two-qubit unit vector `ψ`. Tracing out the second qubit gives

  ρ_A = [[p, w], [w̄, q]],  p = |a|² + |b|²,  q = |c|² + |d|²,  w = a c̄ + b d̄,  p + q = 1.

Then `Tr ρ_A² = p² + q² + 2|w|² = (p + q)² − 2(pq − |w|²)`, and Lagrange's identity
`pq − |w|² = |ad − bc|²` gives `Tr ρ_A² = 1 − 2|ad − bc|²`. The state is a product state iff `ad = bc`
(all 2×2 minors vanish), iff the purity is 1.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `P : ℝ → ℝ → Prop` holds two places at once.
- `G : Prop` with `k : T → G` is "any goal": the entry only adds the fact `T` to the context.
- Placeholders are written as Lean binders. `{d : Type}` is any type. A bracket such as `[Fintype d]` is a
  requirement on `d` (a *type class*): `[Fintype d]` says `d` is finite (`Fin 2`, `Fin 2 × Fin 2` are),
  `[DecidableEq d]` says equality on `d` can be decided (true for both). `[AddCommMonoid α]`: `α` has a
  commutative `+` with `0` (`ℝ`, `ℂ`); `[CommMonoid α]`: a commutative `*` with `1`; `[AddGroup α]`: `+`, `0`, `-`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `d₁ × d₂` | the product type: pairs `(i, j)` with `i : d₁`, `j : d₂`; the index set of a two-party system |
| `inst✝ : Fintype d` in the context | an unnamed type-class assumption (here: `d` is finite) from a `[Fintype d]` binder |
| `Ket d` | a unit vector in `ℂ^d` (physlib); `ψ x : ℂ` is its amplitude at the basis state `x` |
| `Ket (Fin 2 × Fin 2)`, `ψ (i, j)` | a two-qubit ket; `ψ (i, j)` is the amplitude of the basis state with qubits `i`, `j` |
| `MState d` | a density matrix on `d`: Hermitian, positive semidefinite, trace 1 |
| `MState.pure ψ` | the pure state `ψ ψ†` (Dirac notation: the projector onto `ψ`) |
| `ρ.traceRight` | the partial trace over the second factor: `MState (d₁ × d₂) → MState d₁` |
| `ρ.m` | the plain complex matrix of `ρ` (`Matrix d d ℂ`) |
| `↑ρ` | `ρ.M`, the `HermitianMat` inside the state `ρ` |
| `↑A` for `A : HermitianMat d ℂ` | `A.mat`, the plain matrix inside the Hermitian matrix |
| `↑↑ρ` | `ρ.M.mat`, which is by definition `ρ.m` (R1, R4) |
| `HermitianMat d ℂ` | complex `d×d` matrices `A` with `Aᴴ = A` |
| `Matrix d d ℂ` | complex matrices with rows and columns indexed by `d`; `M i j` is the entry in row `i`, column `j` |
| `M (i, k) (j, k)` | an entry of a matrix on `d₁ × d₂`: row `(i, k)`, column `(j, k)` |
| `Matrix.of f` | the matrix whose entry `(i, j)` is `f i j` |
| `∑ x, f x` | the sum of `f x` over every element `x` of a finite type (`Finset.univ.sum f`); `∑ x, ∑ y, …` is a double sum |
| `M.trace` | `∑ i, M i i` |
| `Prob` | `{p : ℝ // 0 ≤ p ∧ p ≤ 1}`, a real number in `[0, 1]` bundled with that proof |
| `↑p` for `p : Prob` | the real number inside `p` |
| `ρ.purity` | `Tr ρ²` as a `Prob`; by definition `inner Prob ρ ρ` (R7) |
| `inner Prob ρ σ` | `Tr (ρ σ)` as a `Prob` |
| `inner ℝ A B` | `re Tr (A B)`, the real inner product of Hermitian matrices (R9) |
| `RCLike.re z` | the real part of `z`, written for `ℝ` and `ℂ` at once; on `ℂ` it is `z.re` (R10) |
| `(starRingEnd ℂ) z` | the complex conjugate `z̄` |
| `z.re`, `z.im` | real and imaginary part of `z : ℂ` (real numbers) |
| `Complex.normSq z` | `z.re * z.re + z.im * z.im`, the squared modulus, a real number |
| `‖z‖` | the modulus of `z`, a real number; `‖z‖ ^ 2 = Complex.normSq z` (R24) |
| `↑r` for `r : ℝ` in a complex goal | `r` cast into `ℂ`; e.g. `↑(Complex.normSq z)`. Write it `((r : ℝ) : ℂ)` |
| `ψ.IsProd` | `∃ ξ φ, ψ = ξ ⊗ᵠ φ`: a product state (`⊗ᵠ` is the tensor product of kets, amplitude `ξ i * φ j`) |
| `x : α := e` in the context | a local definition made by `set` (R18) |
| `case mp`, `case mpr` | the `→` and `←` directions after `constructor` on an `↔` |

---

## Part 1 · `traceRight_pure_apply` (milestone)

Statement: `(MState.pure ψ).traceRight.m i j = ∑ k, ψ (i, k) * (starRingEnd ℂ) (ψ (j, k))`, i.e.
`(Tr_B ψψ†)ᵢⱼ = ∑ₖ ψ(i,k) ψ̄(j,k)`. The work is peeling physlib's wrappers off in the right order:
state → Hermitian matrix → plain matrix, with the partial trace pushed inward at each level.

**R1 · `show G'`** changes the **goal** to a definitionally equal one. `ρ.m` is defined as `ρ.M.mat`
(printed `↑↑ρ`); the lemmas R2, R3 are stated for the `↑↑` form, so `rw` cannot use them on `ρ.m`.
Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (i j : d)`. In the exercise the right side
can stay as `_`.

| Before | After |
|---|---|
| `⊢ P (ρ.m i j)` | `⊢ P (↑↑ρ i j)` |

**R2 · `rw [MState.traceRight_M]`** changes the **goal**. The lemma is `↑ρ.traceRight = (↑ρ).traceRight`: the
Hermitian matrix of the reduced state is the partial trace of the Hermitian matrix. Placeholders:
`{d₁ d₂ : Type}` (each `[Fintype]`, `[DecidableEq]`), `(ρ : MState (d₁ × d₂))`.

| Before | After |
|---|---|
| `⊢ P ↑ρ.traceRight` | `⊢ P (↑ρ).traceRight` |

**R3 · `rw [HermitianMat.traceRight_mat]`** changes the **goal**. The lemma is `↑A.traceRight = (↑A).traceRight`,
the same commutation from Hermitian matrices to plain matrices. Placeholders:
`{d₁ d₂ : Type} [Fintype d₂] (A : HermitianMat (d₁ × d₂) ℂ)`.

| Before | After |
|---|---|
| `⊢ P ↑A.traceRight` | `⊢ P (↑A).traceRight` |

**R4 · `rw [MState.mat_M]`** changes the **goal**. The lemma is `↑↑ρ = ρ.m`. Placeholders: `(ρ : MState d)`.

| Before | After |
|---|---|
| `⊢ P ↑↑ρ` | `⊢ P ρ.m` |

**R5 · `simp only [Matrix.traceRight, Matrix.of_apply]`** changes the **goal**: an entry of a partial trace
becomes a sum. `Matrix.traceRight M` is defined as `Matrix.of fun i j => ∑ k, M (i, k) (j, k)`, and
`Matrix.of_apply` evaluates `Matrix.of f i j = f i j`. Placeholders:
`{d₁ d₂ : Type} [Fintype d₂] (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (i j : d₁)`. Lean renames the bound variable
(`i₁`); names of bound variables do not matter.

| Before | After |
|---|---|
| `⊢ P (M.traceRight i j)` | `⊢ P (∑ i₁, M (i, i₁) (j, i₁))` |

**R6 · `simp only [MState.pure_apply]`** changes the **goal**. The lemma is
`(MState.pure ψ).m i j = ψ i * (starRingEnd ℂ) (ψ j)`. Use `simp only`, not `rw`: after R5 the entry sits
inside `∑ i₁, …`, under a binder, where `rw` cannot rewrite. Placeholders: `(ψ : Ket d) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P ((MState.pure ψ).m i j)` | `⊢ P (ψ i * (starRingEnd ℂ) (ψ j))` |

---

## Part 2 · `purity_eq` (milestone)

Statement: `(ρ.purity : ℝ) = ((ρ.m * ρ.m).trace).re`, for any `ρ : MState d`. Unfold `purity`, leave `Prob`,
turn the inner product into a trace, and compare the two real parts.

**R7 · `simp only [MState.purity]`** changes the **goal**: it unfolds `ρ.purity` to its definition
`inner Prob ρ ρ`. Placeholders: `(ρ : MState d)`. (The guide needs `open scoped MState` to *write*
`inner Prob ρ ρ`; the exercise never writes it.)

| Before | After |
|---|---|
| `⊢ P ρ.purity` | `⊢ P (inner Prob ρ ρ)` |

**R8 · `MState.val_inner`** changes the **goal**: the real number inside the `Prob`-valued inner product is the
real inner product of the Hermitian matrices, `↑(inner Prob ρ σ) = inner ℝ ↑ρ ↑σ`. Placeholders:
`(ρ σ : MState d)`.

| Before | After |
|---|---|
| `⊢ P ↑(inner Prob ρ σ)` | `⊢ P (inner ℝ ↑ρ ↑σ)` |

**R9 · `HermitianMat.inner_eq_re_trace`** changes the **goal**. The lemma is
`inner ℝ A B = RCLike.re (↑A * ↑B).trace`. Placeholders: `{d : Type} [Fintype d] (A B : HermitianMat d ℂ)`.
After it, R4 turns each `↑↑ρ` into `ρ.m`.

| Before | After |
|---|---|
| `⊢ P (inner ℝ A B)` | `⊢ P (RCLike.re (↑A * ↑B).trace)` |

**R10 · `rfl`** **closes** `RCLike.re z = z.re` for `z : ℂ`: `RCLike.re` on `ℂ` is defined as `Complex.re`.
This is how `purity_eq` ends.

| Before | After |
|---|---|
| `⊢ RCLike.re z = z.re` | no goals |

---

## Part 3 · `lagrange` (milestone)

Statement: `(normSq a + normSq b) * (normSq c + normSq d) − normSq (a c̄ + b d̄) = normSq (a d − b c)`, i.e.
`‖u‖²‖v‖² − |⟨v, u⟩|² = |u₀v₁ − u₁v₀|²` for `u = (a, b)`, `v = (c, d)`. `ring` does not know `normSq` or `z̄`.
Rewrite everything into real and imaginary parts (R11–R14, one `simp only` with all of them), and the identity
becomes a polynomial identity in 8 real unknowns that `ring` closes.

**R11 · `Complex.normSq_apply`** changes the **goal**. The lemma is `normSq z = z.re * z.re + z.im * z.im`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq z)` | `⊢ P (z.re * z.re + z.im * z.im)` |

**R12 · `Complex.add_re`, `add_im`, `sub_re`, `sub_im`** change the **goal**: `(z ± w).re = z.re ± w.re`,
and the same for `.im`. Placeholders: `(z w : ℂ)`. (The guide shows `add_re` and `sub_im`.)

| Before | After |
|---|---|
| `⊢ P (z + w).re (z - w).im` | `⊢ P (z.re + w.re) (z.im - w.im)` |

**R13 · `Complex.mul_re`, `Complex.mul_im`** change the **goal**: `(z w).re = z.re w.re − z.im w.im` and
`(z w).im = z.re w.im + z.im w.re`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * w).re (z * w).im` | `⊢ P (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)` |

**R14 · `Complex.conj_re`, `Complex.conj_im`** change the **goal**: `z̄.re = z.re`, `z̄.im = −z.im`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) z).re ((starRingEnd ℂ) z).im` | `⊢ P z.re (-z.im)` |

Then `ring` (TACTIC_STATES, "Closing"). W2 is the same pattern on `normSq (z w) = normSq z · normSq w`.

---

## Part 4 · `reduced_purity`

Statement: `↑(MState.pure ψ).traceRight.purity = 1 - 2 * ‖ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)‖ ^ 2`.
Prove the three milestones first; this part uses all of them.

**R15 · `have hn := ψ.normalized`** changes the **context**: `Ket.normalized` is the fact
`∑ x, Complex.normSq (ψ x) = 1` (the ket has norm 1). Placeholders: `{d : Type} [Fintype d] (ψ : Ket d)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hn : ∑ x, Complex.normSq (ψ x) = 1` |

**R16 · `simp only [Fintype.sum_prod_type] at hn`** changes the **context**: a sum over a product type becomes
a double sum, `∑ x, f x = ∑ x, ∑ y, f (x, y)`. Placeholders: `{d₁ d₂ : Type}` (both `[Fintype]`),
`(f : d₁ × d₂ → ℝ)`. With R17 in the same `simp only`, the double sum over `Fin 2 × Fin 2` becomes four terms:
`hn : normSq a + normSq b + (normSq c + normSq d) = 1`.

| Before | After |
|---|---|
| `⊢ G` with `hn : ∑ p, f p = 1` | `⊢ G` with `hn : ∑ x, ∑ y, f (x, y) = 1` |

**R17 · `Fin.sum_univ_two`** changes the **goal** (or a hypothesis, with `at hn`): a sum over `Fin 2` becomes
two terms. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R18 · `set x := e`** changes the **context** and the **goal**: it adds the local definition `x : α := e` and
replaces every `e`, in the goal and in the hypotheses, by `x`. Use it to name `ρ := (MState.pure ψ).traceRight`;
later `simp [ρ, …]` unfolds the name again. Placeholders: `{α : Type} (f : α → α) (a : α)`, `e := f a`.

| Before | After |
|---|---|
| `h : P (f a) ⊢ P (f a)` | `x : α := f a, h : P x ⊢ P x` |

**R19 · `Complex.mul_conj`** changes the **goal**. The lemma is `z * (starRingEnd ℂ) z = ↑(Complex.normSq z)`:
`z z̄ = |z|²`, cast from `ℝ` into `ℂ`. It turns the diagonal entries `ψ(i,k) ψ̄(i,k)` into real numbers.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * (starRingEnd ℂ) z)` | `⊢ P ↑(Complex.normSq z)` |

**R20 · `Matrix.trace_fin_two`** changes the **goal**: `A.trace = A 0 0 + A 1 1`. Placeholders:
`{α : Type} [AddCommMonoid α] (A : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ P A.trace` | `⊢ P (A 0 0 + A 1 1)` |

**R21 · `Matrix.mul_apply`** changes the **goal**: `(M * N) i k = ∑ j, M i j * N j k`. Each `rw` rewrites one
product entry (all copies of it), so after R20 you need it twice. Placeholders:
`{α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R22 · `rw [mul_comm a]`** changes the **goal**. `mul_comm : a * b = b * a`; giving the left factor `a` makes
`rw` touch only products that start with `a`. In the trace, `rw [mul_comm (starRingEnd ℂ _)]` turns
`w̄ * w` into `w * w̄` so that R19 applies. Placeholders: `{α : Type} [CommMonoid α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (a * b) (c * b)` | `⊢ P (b * a) (c * b)` |

**R23 · `Complex.ofReal_re`, `Complex.ofReal_im`** change the **goal**: `(↑r).re = r`, `(↑r).im = 0`. Together
with R12 and R13 they take the real part of the expanded trace. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑r).re (↑r).im` | `⊢ P r 0` |

**R24 · `Complex.sq_norm`** changes the **goal**: `‖z‖ ^ 2 = Complex.normSq z`, so the goal speaks only of
`normSq`, as `hn` and `lagrange` do. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (‖z‖ ^ 2)` | `⊢ P (Complex.normSq z)` |

**R25 · `linear_combination e₁ * h₁ + e₂ * h₂`** **closes** `lhs = rhs` when
`(lhs − rhs) − (e₁ (h₁.lhs − h₁.rhs) + e₂ (h₂.lhs − h₂.rhs))` is `0` by `ring`. The coefficients `eᵢ` may be
expressions, not only numbers: in the exercise, `hn : p + q = 1` gets the coefficient `p + q + 1`, since
`(p + q)² − 1 = (p + q + 1)(p + q − 1)`. Placeholders (guide): `(x y s : ℝ) (h₁ : x + y = s) (h₂ : x * y = 1)`.

| Before | After |
|---|---|
| `⊢ x ^ 2 + y ^ 2 = s ^ 2 - 2` | no goals |

### Worked combinations (W1, W3, on objects that are not the exercise's; W2 is in Part 3)

**W1: normalisation of a one-qubit ket.** R15, then R17 `at hn`:

```lean-goal
⊢ Complex.normSq (φ 0) + Complex.normSq (φ 1) = 1
```

with `hn : Complex.normSq (φ 0) + Complex.normSq (φ 1) = 1` after the second step; `exact hn`.

**W3: the trace of `A * A` for a 2×2 matrix.** R20, R21 twice, R17 twice:

```lean-goal
⊢ (A * A).trace = A 0 0 * A 0 0 + A 0 1 * A 1 0 + (A 1 0 * A 0 1 + A 1 1 * A 1 1)
⊢ (A * A) 0 0 + (A * A) 1 1 = A 0 0 * A 0 0 + A 0 1 * A 1 0 + (A 1 0 * A 0 1 + A 1 1 * A 1 1)
⊢ ∑ j, A 0 j * A j 0 + ∑ j, A 1 j * A j 1 = A 0 0 * A 0 0 + A 0 1 * A 1 0 + (A 1 0 * A 0 1 + A 1 1 * A 1 1)
```

The last `rw [Fin.sum_univ_two, Fin.sum_univ_two]` makes both sides equal and `rw` closes the goal with `rfl`.
In the exercise the same expansion of `(ρ.m * ρ.m).trace` is followed by `rw` with the four entry facts.

---

## Part 5 · `isProd_iff_reduced_pure`

Statement: `ψ.IsProd ↔ (MState.pure ψ).traceRight.purity = 1`. Move the purity equation into `ℝ` (R26, R27),
substitute Part 4 with `rw [reduced_purity]`, and replace `IsProd` by its minor condition (R28). What is left is
`(∀ i₁ i₂ j₁ j₂, minors vanish) ↔ 1 - 2 * ‖ad - bc‖ ^ 2 = 1`.

**R26 · `rw [Subtype.ext_iff]`** changes the **goal**: an equation in a subtype becomes an equation of the
underlying values. `Prob` is a subtype of `ℝ`. Placeholders: `(p q : Prob)`.

| Before | After |
|---|---|
| `⊢ P (p = q)` | `⊢ P (↑p = ↑q)` |

**R27 · `rw [Prob.coe_one]`** changes the **goal**: `↑(1 : Prob) = (1 : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑1` | `⊢ P 1` |

**R28 · `rw [Ket.IsProd_iff_mul_eq_mul]`** changes the **goal**. The lemma is
`ψ.IsProd ↔ ∀ i₁ i₂ j₁ j₂, ψ (i₁, j₁) * ψ (i₂, j₂) = ψ (i₁, j₂) * ψ (i₂, j₁)`: a two-party ket is a product iff
its amplitude matrix has rank ≤ 1, i.e. every 2×2 minor vanishes. Placeholders:
`{d₁ d₂ : Type}` (both `[Fintype]`), `(ψ : Ket (d₁ × d₂))`.

| Before | After |
|---|---|
| `⊢ P ψ.IsProd` | `⊢ P (∀ (i₁ i₂ : d₁) (j₁ j₂ : d₂), ψ (i₁, j₁) * ψ (i₂, j₂) = ψ (i₁, j₂) * ψ (i₂, j₁))` |

**R29 · `rw [← sub_eq_zero (a := a)]`** changes the **goal**. `sub_eq_zero : a - b = 0 ↔ a = b`; right to left it
turns `a = b` into `a - b = 0`. Naming the left side `a` makes `rw` pick that equation and no other.
Placeholders: `{α : Type} [AddGroup α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (a = b) (c = b)` | `⊢ P (a - b = 0) (c = b)` |

**R30 · `rw [← norm_eq_zero]`** changes the **goal**. `norm_eq_zero : ‖z‖ = 0 ↔ z = 0`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z = 0)` | `⊢ P (‖z‖ = 0)` |

**R31 · `norm_nonneg z`** is the fact `0 ≤ ‖z‖`; pass it to `nlinarith` as a hint.

| Before | After |
|---|---|
| `⊢ 0 ≤ ‖z‖` | no goals |

**R32 · `nlinarith [t₁, …]`** **closes** a polynomial equation or inequality over `ℝ` that follows from the
hypotheses and the hint terms `tᵢ` by multiplying pairs of them and adding. `1 − 2a² = 1` with `0 ≤ a` gives
`a = 0`. Placeholders: `(a : ℝ) (h : 1 - 2 * a ^ 2 = 1) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `⊢ a = 0` | no goals |

The rest is generic: `constructor` on the `↔` (TACTIC_STATES, "Structure"); in the `→` direction, apply the
hypothesis to the indices `0 1 0 1`; in the `←` direction, `intro` the four indices, `fin_cases` each, and
`simp [h, mul_comm]` (W5).

### Worked combinations (W4–W5)

**W4: a norm equation → a vanishing difference.** R29, R30, then `constructor`; the `→` goal closes with R32
and the hint R31, the `←` goal with `intro h; rw [h]; ring`:

```lean-goal
⊢ 3 + ‖z - w‖ ^ 2 = 3 ↔ z = w
⊢ 3 + ‖z - w‖ ^ 2 = 3 ↔ z - w = 0
⊢ 3 + ‖z - w‖ ^ 2 = 3 ↔ ‖z - w‖ = 0
⊢ 3 + ‖z - w‖ ^ 2 = 3 → ‖z - w‖ = 0
⊢ ‖z - w‖ = 0 → 3 + ‖z - w‖ ^ 2 = 3
```

**W5: all index combinations.** `intro i j`, then `fin_cases i <;> fin_cases j <;> simp [h, mul_comm]`:
`simp` evaluates `i ≠ j` on each case and uses `h` (and `mul_comm` for the swapped product `g 1 * g 0`).

```lean-goal
⊢ ∀ (i j : Fin 2), i ≠ j → g i * g j = 2
⊢ i ≠ j → g i * g j = 2
```

---

## Traps

- `rw [MState.traceRight_M]` fails on a goal that shows `ρ.m`: the lemma speaks of `↑ρ.traceRight`. `show` the
  `ρ.M.mat` form first (R1).
- Under `∑ k, …` use `simp only [...]`, not `rw` (R6): `rw` cannot rewrite under a binder.
- `ring` knows neither `normSq` nor `starRingEnd`. Rewrite into `.re`/`.im` first (R11–R14), or name the
  facts and close with `linear_combination` (R25).
- `rw [Complex.mul_conj]` matches only `w * w̄`. Expanding `(ρ.m * ρ.m).trace` and rewriting with
  `ρ.m 1 0 = w̄` produces both `w * w̄` and `w̄ * w`; flip the second with `rw [mul_comm (starRingEnd ℂ _)]`
  (R22) first.
- `hn` is about `normSq`, the goal about `‖·‖ ^ 2`: rewrite with `Complex.sq_norm` (R24) before
  `linear_combination`.
- Without `(a := …)`, `rw [← sub_eq_zero]` rewrites the first equation it finds, which is the `= 1`, not `ad = bc` (R29).
- Do not unfold `ψ.IsProd` (an `∃ ξ φ, …`) by hand: `isProd_iff_reduced_pure` is a short corollary of
  `reduced_purity` plus `Ket.IsProd_iff_mul_eq_mul` (R28). The work is `reduced_purity`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `ρ.m` → the `↑↑ρ` form the lemmas want | `show (…).M.mat i j = _` | R1 |
| push the partial trace inward | `rw [MState.traceRight_M, HermitianMat.traceRight_mat, MState.mat_M]` | R2, R3, R4 |
| entry of `traceRight`, of a pure state | `simp only [Matrix.traceRight, Matrix.of_apply, MState.pure_apply]` | R5, R6 |
| purity → `re Tr(ρ ρ)` | `simp only [MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace, MState.mat_M]` | R7–R9, R4 |
| `RCLike.re z = z.re` | `rfl` | R10 |
| complex identity → real identity | `simp only [Complex.normSq_apply, Complex.add_re, …, Complex.conj_im]`, then `ring` | R11–R14 |
| norm-1 fact as four terms | `have hn := ψ.normalized; simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at hn` | R15–R17 |
| name a big term | `set ρ := …` | R18 |
| `z * z̄` → real | `Complex.mul_conj` | R19 |
| trace of a 2×2 product | `rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]` | R20, R21, R17 |
| swap one product | `rw [mul_comm a]` | R22 |
| real part of a cast | `Complex.ofReal_re`, `Complex.ofReal_im` | R23 |
| `‖z‖ ^ 2` → `normSq z` | `rw [Complex.sq_norm]` | R24 |
| close from equations with coefficients | `linear_combination e₁ * h₁ - 2 * h₂` | R25 |
| `Prob` equation → real equation | `rw [Subtype.ext_iff, Prob.coe_one]` | R26, R27 |
| product state → vanishing minors | `rw [Ket.IsProd_iff_mul_eq_mul]` | R28 |
| `a = b` → `‖a - b‖ = 0` | `rw [← sub_eq_zero (a := a), ← norm_eq_zero]` | R29, R30 |
| `1 - 2 x ^ 2 = 1 → x = 0` | `nlinarith [norm_nonneg _]` | R31, R32 |
| all index cases | `fin_cases i₁ <;> fin_cases i₂ <;> … <;> simp [h, mul_comm]` | W5 |
| see the state | infoview | |
