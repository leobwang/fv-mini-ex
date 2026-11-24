# M133 · Unitaries preserve Born probabilities: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (the Hadamard gate) helps with matrices, `star` and `ᴴ`,
but is not required. **New here:** physlib's kets `Ket d` and unitary group `𝐔[d]`; Mathlib's
matrix–vector products `*ᵥ`, `ᵥ*`, the dot product `⬝ᵥ`, entrywise conjugation `star`, the complex
modulus `‖z‖`, and the cast `ℝ → ℂ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), gives the lemma's statement, lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[NonUnitalSemiring α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- `{n : Type} [Fintype n] [DecidableEq n]`: `n` indexes the basis (`Fin 2` for a qubit); `Fintype` says it is
  finite (so `∑ i` makes sense), `DecidableEq` that `i = j` can be decided (needed for the identity matrix `1`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `𝐔[d]` | physlib notation for `Matrix.unitaryGroup d ℂ`: the set of `d × d` complex matrices `U` with `star U * U = 1` and `U * star U = 1` |
| `U : ↥𝐔[d]` | `↥` turns that set into a type: `U` is a matrix *bundled with* the proof that it is unitary |
| `↑U`, `U.val` | the bare matrix `Matrix d d ℂ` inside `U` (`U.val` is how you write it, `↑U` how Lean prints it) |
| `Ket d` | physlib's pure state: a structure with `vec : d → ℂ` (the amplitudes) and `normalized' : ∑ x, ‖vec x‖ ^ 2 = 1` |
| `ψ.vec i` | the amplitude `ψᵢ` of basis state `i` |
| `M *ᵥ v` | `Matrix.mulVec`: matrix times **column** vector, `(M v)ᵢ = ∑ⱼ Mᵢⱼ vⱼ` |
| `v ᵥ* M` | `Matrix.vecMul`: **row** vector times matrix, `(v M)ⱼ = ∑ᵢ vᵢ Mᵢⱼ` |
| `v ⬝ᵥ w` | `dotProduct`: `∑ᵢ vᵢ wᵢ`. **No conjugation**: the Hermitian product `⟨v, w⟩` is `star v ⬝ᵥ w` |
| `star v` (vector) | entrywise complex conjugate: `(star v) i = conj (v i)` (R9) |
| `star M` (matrix), `Mᴴ` | the conjugate transpose `M†`: `Mᴴ i j = conj (M j i)`; `star M = Mᴴ` (R4) |
| `star z`, `(starRingEnd ℂ) z` | the complex conjugate `z̄`; the second is how `conj z` prints (R10) |
| `‖z‖` | the modulus `|z|` of `z : ℂ`, a **real** number |
| `↑x` | the real `x` cast into `ℂ` (`Complex.ofReal x`) |
| `∑ i, f i` | `∑` over all `i` of the finite type (`Finset.univ`) |
| `v ᵥ* A ⬝ᵥ w`, `v ⬝ᵥ A *ᵥ w` | grouping: `*ᵥ`, `ᵥ*` bind tighter than `⬝ᵥ`, so these are `(v ᵥ* A) ⬝ᵥ w` and `v ⬝ᵥ (A *ᵥ w)`; e.g. `star (↑U *ᵥ ψ.vec) ⬝ᵥ ↑U *ᵥ ψ.vec` is `(Uψ)† (Uψ)` |
| `v ᵥ* M ᵥ* N`, `M *ᵥ N *ᵥ v` | `(v ᵥ* M) ᵥ* N` and `M *ᵥ (N *ᵥ v)`: each product groups toward its vector |

---

## Part 1 · `unitary_born`

Statement: for `U : 𝐔[d]` and `ψ : Ket d`, `∑ i, ‖(U.val *ᵥ ψ.vec) i‖ ^ 2 = 1`. In words: the Born
probabilities `|(Uψ)ᵢ|²` still sum to 1, i.e. `‖Uψ‖² = ‖ψ‖²`. The sum is in `ℝ`; the algebra that moves `U`
(`U†U = 1`) lives in `ℂ` with `star v ⬝ᵥ v = ∑ v̄ᵢ vᵢ`. The proof has two milestones and a chain:

- **(a)** `U` leaves `star v ⬝ᵥ v` unchanged for `v = ψ.vec` (R1–R6, a `rw` chain);
- **(b)** for every `v : d → ℂ`, `((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v` (R7–R13, one `simp`);
- chain (b) for `Uψ`, (a), (b) for `ψ` backwards; use `normalized'`; leave `ℂ` (R14–R16).

### Milestone (a): moving `U` through the dot product

Read it as `(Uψ)† (Uψ) = ψ† U† U ψ = ψ† ψ`. Each step is one `rw`.

**R1 · `rw [Matrix.star_mulVec]`** changes the **goal**. The lemma is `star (M *ᵥ v) = star v ᵥ* Mᴴ`: the
conjugate of the column `M v` is the row `v̄ M†`. Placeholders: `{m n α : Type} [Fintype n]
[NonUnitalSemiring α] [StarRing α] (M : Matrix m n α) (v : n → α)`; `ℂ` meets both brackets (`StarRing`: a
ring with a conjugation `star` that reverses products).

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R2 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**. The lemma is `v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w`,
i.e. `vᵀ(Aw) = (vᵀA)w`: the matrix moves from the right factor to the left one. Placeholders:
`{m n α : Type} [Fintype m] [Fintype n] [NonUnitalSemiring α] (v : m → α) (A : Matrix m n α) (w : n → α)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ A *ᵥ w)` | `⊢ P (v ᵥ* A ⬝ᵥ w)` |

**R3 · `rw [Matrix.vecMul_vecMul]`** changes the **goal**. The lemma is `v ᵥ* M ᵥ* N = v ᵥ* (M * N)`
(associativity of row × matrix × matrix). Placeholders: `{m n o α : Type} [Fintype m] [Fintype n]
[NonUnitalSemiring α] (v : m → α) (M : Matrix m n α) (N : Matrix n o α)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* M ᵥ* N)` | `⊢ P (v ᵥ* (M * N))` |

**R4 · `rw [← Matrix.star_eq_conjTranspose]`** changes the **goal**. The lemma is `star M = Mᴴ`; right to left
it turns `Mᴴ` back into `star M`, the form R5 is stated in. Placeholders: `{n α : Type} [Star α]
(M : Matrix n n α)` (square matrices only).

| Before | After |
|---|---|
| `⊢ P Mᴴ` | `⊢ P (star M)` |

**R5 · `rw [Matrix.UnitaryGroup.star_mul_self]`** changes the **goal**. The lemma is `star ↑U * ↑U = 1` for
`U : 𝐔[n]`: unitarity `U†U = 1`, read off the bundled proof. Placeholders: `{n : Type} [Fintype n]
[DecidableEq n] (U : 𝐔[n])`.

| Before | After |
|---|---|
| `⊢ P (star ↑U * ↑U)` | `⊢ P 1` |

**R6 · `rw [Matrix.vecMul_one]`** changes the **goal**. The lemma is `v ᵥ* 1 = v`. After it, both sides of
milestone (a) are the same text and `rw` closes the goal by `rfl`. Placeholders: `{n α : Type} [Fintype n]
[DecidableEq n] [NonAssocSemiring α] (v : n → α)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* 1)` | `⊢ P v` |

### Milestone (b): from `star v ⬝ᵥ v` in `ℂ` to `∑ ‖vᵢ‖²` in `ℝ`

`simp [dotProduct, Complex.conj_mul']` does all of R8–R13. Name R8 and R11; `simp` finds R9, R10, R12, R13
by itself. The entries show what happens inside.

**R7 · `intro v`** changes the **goal and the context**: a `∀` goal loses its binder and `v` enters the
context. Placeholders: `{n : Type} (Q : (n → ℂ) → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (v : n → ℂ), Q v` | `v : n → ℂ ⊢ Q v` |

**R8 · `simp only [dotProduct]`** changes the **goal**: it unfolds the definition `v ⬝ᵥ w = ∑ i, v i * w i`.
Placeholders: `{n α : Type} [Fintype n] [Mul α] [AddCommMonoid α] (v w : n → α)` (`α` has `*` and a
commutative `+` with `0`, as `ℂ` does).

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R9 · `rw [Pi.star_apply]`** changes the **goal**. The lemma is `star x i = star (x i)`: an entry of the
conjugated vector is the conjugate of the entry. Placeholders: `{n : Type} (v : n → ℂ) (i : n)`.

| Before | After |
|---|---|
| `⊢ P (star v i)` | `⊢ P (star (v i))` |

**R10 · `simp only [Complex.star_def]`** changes the **goal**. The lemma is `star = ⇑(starRingEnd ℂ)` (`⇑` turns
the bundled ring map `starRingEnd ℂ` into a plain function `ℂ → ℂ`):
on `ℂ`, `star` *is* Mathlib's `conj`, printed `(starRingEnd ℂ)`. R11 is stated with the second form. (`simp`
uses the general `RCLike.star_def`, the same fact for `ℝ` and `ℂ`.) Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star z)` | `⊢ P ((starRingEnd ℂ) z)` |

**R11 · `rw [Complex.conj_mul']`** changes the **goal**. The lemma is `(starRingEnd ℂ) z * z = ↑‖z‖ ^ 2`, i.e.
`z̄ z = |z|²`, with the real `‖z‖` cast into `ℂ`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) z * z)` | `⊢ P (↑‖z‖ ^ 2)` |

**R12 · `rw [Complex.ofReal_sum]`** changes the **goal**. The lemma is `↑(∑ i ∈ s, f i) = ∑ i ∈ s, ↑(f i)`:
the cast of a real sum is the sum of the casts (`∑ i ∈ s` sums over a finite set `s : Finset α`; `∑ i, f i` is
the case `s = Finset.univ`). Placeholders: `{n : Type} [Fintype n] (f : n → ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑(∑ i, f i)` | `⊢ P (∑ i, ↑(f i))` |

**R13 · `rw [Complex.ofReal_pow]`** changes the **goal**. The lemma is `↑(r ^ n) = ↑r ^ n`. After R12 and R13
the left side of (b) reads `∑ i, ↑‖v i‖ ^ 2`, the same as the right side after R8–R11. Placeholders:
`(r : ℝ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(r ^ k)` | `⊢ P (↑r ^ k)` |

### Chaining and leaving `ℂ`

**R14 · `have h := h₁.trans (h₂.trans h₃.symm)`** changes the **context**: it adds the composite equation.
`Eq.trans : a = b → b = c → a = c`, `Eq.symm : a = b → b = a`; dot notation `h₁.trans h₂` means
`Eq.trans h₁ h₂`. A `_` argument, as in `(fact _)`, is filled in by unification with its neighbour in the
chain. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `h₁ : a = b, h₂ : b = c, h₃ : d = c ⊢ a = d` | `h : a = d ⊢ a = d` |

**R15 · `rw [φ.normalized'] at h`** changes the **context**: `at h` rewrites hypothesis `h`, the goal stays.
`Ket.normalized'` is the field `∑ x, ‖φ.vec x‖ ^ 2 = 1` stored in every ket `φ : Ket n`. Placeholders:
`{n : Type} [Fintype n] (φ : Ket n) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : P (∑ x, ‖φ.vec x‖ ^ 2)` and `⊢ P 1` | `h : P 1 ⊢ P 1` |

**R16 · `exact_mod_cast h`** **closes** the goal: it proves a real statement from the same statement about
casts, here `x = y` from `↑x = ↑y` (the cast `ℝ → ℂ` is injective). It also normalises casts of numerals, so
`h : ↑x = ↑1` proves `x = 1`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `h : ↑x = ↑y ⊢ x = y` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: the column-vector version of R3–R6.** `star U *ᵥ (U *ᵥ v) = v`, using the column lemmas
`Matrix.mulVec_mulVec : M *ᵥ N *ᵥ v = (M * N) *ᵥ v` and `Matrix.one_mulVec : 1 *ᵥ v = v` around R5:

```lean-goal
⊢ star ↑U *ᵥ ↑U *ᵥ v = v
⊢ (star ↑U * ↑U) *ᵥ v = v
⊢ 1 *ᵥ v = v
```

**W2: `simp` does R9–R13 by itself.** For two complex numbers `a b`, `simp [Complex.conj_mul']` closes

```lean-goal
⊢ ↑(‖a‖ ^ 2 + ‖b‖ ^ 2) = star a * a + star b * b
```

**W3: leaving `ℂ`.** From `h₁ : ↑x = c`, `h₂ : ↑y = c`, `hy : y = 2`: R14 gives `h : ↑x = ↑y`,
`rw [hy] at h` (as R15) gives `h : ↑x = ↑2`, and R16 closes `x = 2`.

| Before | After |
|---|---|
| `⊢ x = 2` | `h : ↑x = ↑y ⊢ x = 2` |
| `h : ↑x = ↑y ⊢ x = 2` | `h : ↑x = ↑2 ⊢ x = 2` |

---

## Traps

- `⬝ᵥ` does **not** conjugate. `v ⬝ᵥ v = ∑ vᵢ²`, not `∑ |vᵢ|²`; write `star v ⬝ᵥ v`.
- `rw [Matrix.UnitaryGroup.star_mul_self]` does not fire on `(↑U)ᴴ * ↑U`: `ᴴ` and `star` are different text.
  Turn `ᴴ` into `star` first (R4).
- R2 needs the goal in the form `v ⬝ᵥ A *ᵥ w`. After R1 the left factor is a row (`star v ᵥ* Mᴴ`) and the right
  one a column (`U *ᵥ ψ`): R2 moves `U` from the column to the row, then R3 merges the two matrices.
- In the statement of milestone (b), write the types: `((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)`. Without `: ℝ` the sum is
  computed in `ℂ` (Lean prints `∑ i, ↑‖v i‖ ^ 2`), and later `rw [ψ.normalized'] at h` cannot find the real
  sum `∑ x, ‖ψ.vec x‖ ^ 2` in `h`.
- `simp [dotProduct]` without `Complex.conj_mul'` stops at `(starRingEnd ℂ) (v x) * v x`; that lemma is not a
  default `simp` lemma.
- `rw [φ.normalized']` rewrites the *goal*; to change a hypothesis, add `at h` (R15).
- The goal is in `ℝ`, the chain in `ℂ`: `exact h` fails on `↑x = ↑1` vs `x = 1`. Use `exact_mod_cast` (R16).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| conjugate of a column `M v` → row `v̄ M†` | `rw [Matrix.star_mulVec]` | R1 |
| move a matrix across `⬝ᵥ` | `rw [Matrix.dotProduct_mulVec]` | R2 |
| merge `v ᵥ* M ᵥ* N` | `rw [Matrix.vecMul_vecMul]` | R3 |
| `Mᴴ → star M` | `rw [← Matrix.star_eq_conjTranspose]` | R4 |
| `star ↑U * ↑U → 1` | `rw [Matrix.UnitaryGroup.star_mul_self]` | R5 |
| `v ᵥ* 1 → v` / `1 *ᵥ v → v` | `rw [Matrix.vecMul_one]` / `rw [Matrix.one_mulVec]` | R6, W1 |
| prove a `∀ v` fact | `intro v` | R7 |
| `star v ⬝ᵥ v` ↔ `∑ ‖vᵢ‖²` | `simp [dotProduct, Complex.conj_mul']` | R8–R13 |
| glue equations | `have h := h₁.trans (h₂.trans h₃.symm)` | R14 |
| use `∑ ‖ψ.vec x‖² = 1` in a hypothesis | `rw [ψ.normalized'] at h` | R15 |
| `ℂ`-equation of casts → `ℝ`-equation | `exact_mod_cast h` | R16 |
| see the state | infoview | |
