# M134 · Pure states are projectors: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (the Hadamard gate) and M133 (Born probabilities) help
with matrices, `ext`, `starRingEnd` and casts, but are not required. **New here:** physlib's kets `Ket d` and
mixed states `MState d` with the pure state `MState.pure ψ`; Mathlib's matrix entries over an arbitrary finite
index type, finite sums `∑` (`Finset.sum`) and moving factors through them, the complex modulus `‖z‖` and the
cast `ℝ → ℂ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**, **context**,
or **goal list**), gives the lemma's statement, lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as
  `[NonUnitalNonAssocSemiring R]` is a requirement on `R` (a *type class*). Each entry says which familiar types
  meet it.
- `{d : Type} [Fintype d] [DecidableEq d]`: `d` indexes the basis (`Fin 2` for a qubit, `Fin 2 × Fin 2` for two);
  `Fintype d` says it is finite (so `∑ k` over all of `d` makes sense), `DecidableEq d` that `i = j` can be
  decided (physlib needs it to build `MState d`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ket d` | physlib's pure state: a structure with `vec : d → ℂ` (the amplitudes) and `normalized' : ∑ x, ‖vec x‖ ^ 2 = 1` |
| `ψ i`, `ψ.vec i` | the amplitude `ψᵢ`. `ψ i` applies `ψ` as a function (a `FunLike` coercion), which unfolds to `ψ.vec i` (`Ket.coe_fun_eq`); the infoview shows both forms |
| `MState d` | physlib's mixed state (density matrix) `ρ`: a positive semidefinite Hermitian `d × d` matrix of trace 1 |
| `MState.pure ψ` | the pure state `ρ = \|ψ⟩⟨ψ\|`, entries `ρᵢⱼ = ψᵢ · conj ψⱼ` (R3) |
| `ρ.m` | the bare matrix `Matrix d d ℂ` of the state `ρ` |
| `Matrix d d ℂ`, `M i j` | `d × d` complex matrices, a function `d → d → ℂ`; `M i j` is the entry in row `i`, column `j` |
| `(M * N) i k` | entry of the matrix product, `∑ⱼ Mᵢⱼ Nⱼₖ` (R2) |
| `(starRingEnd ℂ) z` | the complex conjugate `z̄`; this is how Mathlib's `conj z` prints |
| `‖z‖` | the modulus `\|z\|` of `z : ℂ`, a **real** number |
| `↑r` | the real `r` cast into `ℂ` (`Complex.ofReal r`); `↑‖z‖ ^ 2` is `(↑‖z‖) ^ 2` |
| `∑ x, f x` | `Finset.sum Finset.univ f`: the sum of `f x` over every `x : d` |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset d`; lemmas are stated this way, `s = Finset.univ` gives `∑ i, f i` |
| `x`, `i_1`, `j_1` as summation index | names Lean picks for the bound variable after a rewrite; `∑ x, f x` and `∑ k, f k` are the same term |
| `(a * ∑ k, f k) * b` | the same term as `a * (∑ k, f k) * b`: `∑ k,` reaches as far right as it can, so Lean prints parentheses around the product instead |
| `fun k => F k` | the function `k ↦ F k`; `congr 1` exposes the summands this way (R10) |
| `case e_f` | the goal `congr 1` produced for the function argument `f` of `Finset.sum` |
| `this` | the name of a fact added by `have :=` without a name (R4) |

---

## Part 1 · `pure_idempotent`

Statement: for `ψ : Ket d`, `(MState.pure ψ).m * (MState.pure ψ).m = (MState.pure ψ).m`, i.e. `ρ² = ρ` for
`ρ = |ψ⟩⟨ψ|`: a pure state is a projector. On paper, entry `(i, j)`:
`(ρρ)ᵢⱼ = ∑ₖ ψᵢ ψ̄ₖ · ψₖ ψ̄ⱼ = ψᵢ (∑ₖ ψ̄ₖ ψₖ) ψ̄ⱼ = ψᵢ · 1 · ψ̄ⱼ = ρᵢⱼ`, using `∑ₖ ψ̄ₖ ψₖ = ∑ₖ |ψₖ|² = 1`.
The Lean proof follows it: one entry (R1–R3), the fact `∑ₖ ψ̄ₖ ψₖ = 1` (R4–R6), a two-step `calc` (R7–R13).

### Matrix equation → one entry

**R1 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when every
entry is. Placeholders: `{d α : Type} (M N : Matrix d d α)`. Unlike `Fin 2`, a general `d` has no `fin_cases`:
you prove entry `(i, j)` for arbitrary `i j`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : d ⊢ M i j = N i j` |

**R2 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
`(M * N) i k = ∑ j, M i j * N j k`. Placeholders: `{d α : Type} [Fintype d] [Mul α] [AddCommMonoid α]` (α has
`*` and a commutative `+` with `0`, as `ℂ` does), `(M N : Matrix d d α) (i k : d)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R3 · `simp only [MState.pure_apply]`** changes the **goal**. The lemma is
`MState.pure_apply : (MState.pure ψ).m i j = ψ i * (starRingEnd ℂ) (ψ j)`, i.e. `ρᵢⱼ = ψᵢ ψ̄ⱼ`. After R2 the
entries sit inside `∑ k, …` and mention the bound `k`; `rw` cannot rewrite there (it rewrites only an entry
outside the sum, if there is one), `simp only` rewrites all of them. Write
`simp only [Matrix.mul_apply, MState.pure_apply]` to do R2 and R3 in one step. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] (φ : Ket d) (A : Matrix d d ℂ) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P (∑ k, (MState.pure φ).m i k * A k j)` | `⊢ P (∑ x, φ i * (starRingEnd ℂ) (φ x) * A x j)` |

### Normalisation in `ℂ`

The sum left after the `calc` below is `∑ k, (starRingEnd ℂ) (ψ k) * ψ k`, in `ℂ`. Normalisation is
`∑ x, ‖ψ.vec x‖ ^ 2 = 1`, in `ℝ`. Prove the bridge as a `have h : … = 1 := by …` (TACTIC_STATES, "Adding facts").

**R4 · `have := φ.normalized'`** changes the **context**: it adds the field `Ket.normalized'` of `φ` as `this`.
Placeholders: `{d : Type} [Fintype d] (φ : Ket d)`. It is stated with `φ.vec x`; your goals say `φ x`. They are
the same number, but `rw [this]` will not see that; R6 does.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `this : ∑ x, ‖φ.vec x‖ ^ 2 = 1` |

**R5 · `simp only [Complex.conj_mul']`** changes the **goal**. The lemma is
`Complex.conj_mul' : (starRingEnd ℂ) z * z = ↑‖z‖ ^ 2`, i.e. `z̄ z = |z|²` with `|z|` real and cast to `ℂ`.
`simp only` applies it under `∑`. Placeholders: `{d : Type} [Fintype d] (f : d → ℂ)`. The order matters:
`z * conj z` needs `Complex.mul_conj'` instead.

| Before | After |
|---|---|
| `⊢ P (∑ k, (starRingEnd ℂ) (f k) * f k)` | `⊢ P (∑ x, ↑‖f x‖ ^ 2)` |

**R6 · `exact_mod_cast h`** **closes** a goal written with casts `↑r` of reals into `ℂ`, using a hypothesis `h` that
says the same thing in `ℝ`. It normalises the casts on both (`↑a ^ 2 = ↑(a ^ 2)`, `∑ ↑ = ↑∑`, `↑1 = 1`) and
then matches `h` up to unfolding definitions, which identifies `φ x` with `φ.vec x`. Placeholders: `{d : Type} [Fintype d] (r : d → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ x, ↑(r x) ^ 2 = ↑c`, with `h : ∑ x, r x ^ 2 = c` | closed |

### The `calc`: pull `ψᵢ` and `ψ̄ⱼ` out of the sum

**R7 · `calc`** changes the **goal list**: the goal `a = c` is replaced by one goal per step. Write
`calc a = b := proof₁` and then `_ = c := proof₂` on the next line (`_` is the previous right side). The first
left side and the last right side must match the goal (bound variable names may differ). Use `:= by …` for each
step, or `:= ?_` to leave it as a goal. The first left side may be `_` (`calc _ = b := …`): Lean then takes it
from the goal. Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a = c` | `⊢ a = b`, `⊢ b = c` |

**R8 · `rw [Finset.mul_sum]`** changes the **goal**. The lemma is `Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`:
a factor on the left moves into the sum. Placeholders: `{d R : Type} [Fintype d] [NonUnitalNonAssocSemiring R]`
(`R` has `+`, `*`, `0` and distributivity; `ℂ`, `ℝ`, `ℕ` qualify), `(a : R) (f : d → R)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ k, f k)` | `⊢ P (∑ i, a * f i)` |

**R9 · `rw [Finset.sum_mul]`** changes the **goal**. The lemma is `Finset.sum_mul : (∑ i ∈ s, f i) * b = ∑ i ∈ s, f i * b`:
a factor on the right moves into the sum. Placeholders as R8, with `(b : R)`. `*` groups to the left, so in
`a * (∑ k, f k) * b` the right factor `b` multiplies `a * ∑ …`, not the sum: do R8 first, then R9.

| Before | After |
|---|---|
| `⊢ P ((∑ k, f k) * b)` | `⊢ P (∑ i, f i * b)` |

**R10 · `congr 1`** changes the **goal**: two sums over the same set are equal when their summand functions are.
Placeholders: `{d R : Type} [Fintype d] [CommRing R] (a : R) (f : d → R)`. `congr 1` also closes a goal it can
finish by `rfl` or by a hypothesis.

| Before | After |
|---|---|
| `⊢ ∑ k, a * f k = ∑ k, f k * a` | `⊢ (fun k => a * f k) = fun k => f k * a` |

**R11 · `ext k`** changes the **goal and the context**: two functions are equal when they agree at every `k`
(`funext`). It also gives the bound variables of both sides the same name `k`. Placeholders as R10.

| Before | After |
|---|---|
| `⊢ (fun k => a * f k) = fun k => f k * a` | `k : d ⊢ a * f k = f k * a` |

**R12 · `ring`** **closes** an equation that holds in every commutative ring, here a rearrangement of a product of
four factors. It treats `(starRingEnd ℂ) w` and `ψ k` as unknowns, so it does not know `z̄ z = |z|²`; that is
R5's job. Example: `a * (starRingEnd ℂ) w * b = (starRingEnd ℂ) w * (b * a)`.

**R13 · `rw [mul_one]`** changes the **goal**. The lemma is `mul_one : a * 1 = a`. After `rw [h]` with
`h : ∑ … = 1` the goal contains `ψ i * 1 * …`. Placeholders: `{M : Type} [MulOneClass M] (a b : M)` (`M` has
`*` and a `1` that is neutral; `ℂ` qualifies). When the rewrite leaves `x = x`, `rw` closes the goal by `rfl`.

| Before | After |
|---|---|
| `⊢ P (a * 1 * b)` | `⊢ P (a * b)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a pure state times another matrix `A`, entry `(i, j)`.** Goal
`((MState.pure φ).m * A) i j = φ i * ∑ k, (starRingEnd ℂ) (φ k) * A k j`. The states after R2 + R3
(`simp only`), R8, R10 and R11; `ring` (R12) closes the last:

```lean-goal
⊢ ∑ x, φ i * (starRingEnd ℂ) (φ x) * A x j = φ i * ∑ k, (starRingEnd ℂ) (φ k) * A k j
⊢ ∑ x, φ i * (starRingEnd ℂ) (φ x) * A x j = ∑ i_1, φ i * ((starRingEnd ℂ) (φ i_1) * A i_1 j)
⊢ (fun x => φ i * (starRingEnd ℂ) (φ x) * A x j) = fun i_1 => φ i * ((starRingEnd ℂ) (φ i_1) * A i_1 j)
⊢ φ i * (starRingEnd ℂ) (φ k) * A k j = φ i * ((starRingEnd ℂ) (φ k) * A k j)
```

**W2: a vector `f` with `hf : ∑ x, ‖f x‖ ^ 2 = 2`.** To prove `∑ x, (starRingEnd ℂ) (f x) * f x = 2`, R5 gives

```lean-goal
⊢ ∑ x, ↑‖f x‖ ^ 2 = 2
```

and `exact_mod_cast hf` (R6) closes it.

**W3: constants on both sides of a sum.** `∑ k, b * (f k * a) = a * b` from `hf : ∑ k, f k = 1`: a `calc` (R7)
through `a * (∑ k, f k) * b`, whose first step is R8, R9, R10, R11, R12 and whose second is `rw [hf]`, R13.

---

## Traps

- The library's rank-one product lemmas (`Matrix.vecMulVec_mul_vecMulVec` and its relatives) and
  `MState.pure_mul_self` are `BANNED`: they would prove the theorem in one line. Prove it entrywise.
- `rw` cannot rewrite inside `∑ k, …` when the pattern mentions `k`. After R2, `rw [MState.pure_apply]` succeeds
  but rewrites only the right side `(MState.pure ψ).m i j`, and the entries inside the sum stay. Use
  `simp only [lemma]` there (R3, R5).
- Write the `calc`'s first left side exactly as the goal after `simp only` shows it (copy it from the infoview;
  only the name of the summation index may differ), or write `_` and let Lean take it from the goal (R7).
- `ψ.vec x` and `ψ x` are the same amplitude written two ways, and casts are in the way too:
  `rw [ψ.normalized']` on `⊢ ∑ x, ↑‖ψ x‖ ^ 2 = 1` fails ("did not find an occurrence of the pattern").
  `exact_mod_cast` sees through both (R6).
- `Complex.conj_mul'` is `conj z * z`; `Complex.mul_conj'` is `z * conj z`. State `h` in the order your goal has.
- `rw [Finset.sum_mul]` before `rw [Finset.mul_sum]` fails on `a * (∑ …) * b`: the factor right of `∑` is not yet
  next to the sum (R9).
- Keep the indentation of a `calc`: the `_ = …` lines line up under each other, and each step's `by` block is
  indented further.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation → entry `(i, j)` | `ext i j` | R1 |
| entry of a product / of `(MState.pure ψ).m` | `simp only [Matrix.mul_apply, MState.pure_apply]` | R2, R3 |
| normalisation as a fact | `have := ψ.normalized'` | R4 |
| `conj z * z → ↑‖z‖ ^ 2` under `∑` | `simp only [Complex.conj_mul']` | R5 |
| real statement → same statement with casts in `ℂ` | `exact_mod_cast this` | R6 |
| chain equalities | `calc a = b := by … ` / `_ = c := by …` | R7 |
| `a * ∑ f → ∑ a * f` | `rw [Finset.mul_sum]` | R8 |
| `(∑ f) * b → ∑ f * b` | `rw [Finset.sum_mul]` | R9 |
| equal sums → equal summands | `congr 1; ext k` | R10, R11 |
| rearrange a product | `ring` | R12 |
| use `h : ∑ … = 1`, drop the `1` | `rw [h, mul_one]` | R13 |
| see the state | infoview | |
