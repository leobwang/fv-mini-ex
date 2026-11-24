# M178 · Lorentz matrices have determinant ±1: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's Lorentz group `LorentzGroup d` and
Minkowski matrix `η`; Mathlib's determinant `Matrix.det` and its product and transpose rules; the
`↔`/`∨` lemmas `mul_eq_zero`, `Or.resolve_left`, `mul_self_eq_one_iff`; the closers `linear_combination`
and `linarith`.

The math: in `d` space dimensions, `η = diag(1, −1, …, −1)` is the Minkowski metric, a real
`(1 + d) × (1 + d)` matrix with `det η = (−1)^d`. A Lorentz matrix `Λ` satisfies `Λᵀ η Λ = η`. Taking
determinants (`det (AB) = det A · det B`, `det Aᵀ = det A`):

$$\det\Lambda \cdot (-1)^d \cdot \det\Lambda = (-1)^d
\;\Longrightarrow\; (-1)^d\,\big((\det\Lambda)^2 - 1\big) = 0
\;\Longrightarrow\; (\det\Lambda)^2 = 1
\;\Longrightarrow\; \det\Lambda = \pm 1,$$

where the middle step divides by `(−1)^d ≠ 0`. In Lean the division is done as "a product is zero, the
first factor is not, so the second is" (R9, R10).

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`simp`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal or hypothesis" (`P : α → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing R]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `LorentzGroup d`, `𝓛 d` | the **set** of real matrices indexed by `Fin 1 ⊕ Fin d` (one time index, `d` space indices) that preserve `η`; `𝓛 d` is how it prints |
| `Λ : ↑(𝓛 d)` | `Λ` is an element of that set used as a type (a subtype): a matrix paired with a proof that it is in the set. The `↑` turns the set into that type; the notation `𝓛` comes from `open LorentzGroup` |
| `Λ.1`, `↑Λ` | the underlying matrix of `Λ`; you write `Λ.1`, the infoview prints `↑Λ` |
| `η` | `minkowskiMatrix`, `diag(1, −1, …, −1)`. Notation from `open minkowskiMatrix`; its size `d` is implicit |
| `Mᵀ`, `(↑Λ)ᵀ` | transpose: `Mᵀ i j = M j i` |
| `M.det`, `(↑Λ).det`, `det 1` | `Matrix.det M`, the determinant (dot notation `M.det` = `Matrix.det M`). Needs a square matrix over a commutative ring |
| `Matrix n n R` | square matrices with rows and columns indexed by `n` and entries in `R`. `[Fintype n]`: `n` is finite; `[DecidableEq n]`: indices can be compared (both hold for `Fin k` and `Fin 1 ⊕ Fin d`) |
| `(-1) ^ d` | the real number `(−1)^d`, `d : ℕ` |
| `-1 ≠ 0` | `¬(-1 = 0)`: `a ≠ b` unfolds to `a = b → False` |
| `A ∨ B` | "A or B"; `A ↔ B` "A iff B", whose directions are `.mp : A → B` and `.mpr : B → A` |

---

## Part 1 · `det_pm_one`

Statement: for every `d : ℕ` and `Λ : LorentzGroup d`, `Λ.1.det = 1 ∨ Λ.1.det = -1`.

### The defining identity and its determinant

**R1 · `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self`** changes the **context**. The lemma is
`Λᵀ * η * Λ = η`. Its `Λ` is implicit (written `{Λ}` in its type), so Lean cannot guess it: name it,
`transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)`. Placeholders: `{d : ℕ} (Λ : LorentzGroup d)`.

| Before | After |
|---|---|
| `⊢ G` | `h : (↑Λ)ᵀ * η * ↑Λ = η ⊢ G` |

**R2 · `congrArg Matrix.det h`** changes the **context**. `congrArg f : a = b → f a = f b` applies a function to
both sides; with `f = Matrix.det` a matrix equation becomes a number equation. Nest it with R1:
`have h := congrArg Matrix.det (… R1 …)`. Placeholders: `{n R : Type} [DecidableEq n] [Fintype n]
[CommRing R] (M N : Matrix n n R) (h : M = N)` (`ℝ` is a `CommRing`).

| Before | After |
|---|---|
| `h : M = N ⊢ G` | `hd : M.det = N.det ⊢ G` |

### Evaluating the determinants (inside `h`)

In the solution R3, R4, R5 go in **one** `simp only [Matrix.det_mul, Matrix.det_transpose,
minkowskiMatrix.det_eq_neg_one_pow_d] at h`. `… at h` rewrites the hypothesis `h` instead of the goal.

**R3 · `Matrix.det_mul`** changes the **context**. The lemma is `(M * N).det = M.det * N.det`. `*` groups to the
left, so `M * N * K` is `(M * N) * K` and the lemma fires twice; `simp only` keeps going, a single `rw`
would not reach the inner product. Placeholders: as in R2, plus `(M N K : Matrix n n R)`.

| Before | After |
|---|---|
| `h : P (M * N * K).det ⊢ G` | `h : P (M.det * N.det * K.det) ⊢ G` |

**R4 · `Matrix.det_transpose`** changes the **context**. The lemma is `Mᵀ.det = M.det`. Placeholders: as in R2.

| Before | After |
|---|---|
| `h : P Mᵀ.det ⊢ G` | `h : P M.det ⊢ G` |

**R5 · `minkowskiMatrix.det_eq_neg_one_pow_d`** changes the **context**. The lemma is `η.det = (-1) ^ d`.
Placeholders: `{d : ℕ}`; in the guide `η` is written `minkowskiMatrix (d := d)` to fix its size.

| Before | After |
|---|---|
| `h : P η.det ⊢ G` | `h : P ((-1) ^ d) ⊢ G` |

After R1–R5 the solution's `h` reads `(↑Λ).det * (-1) ^ d * (↑Λ).det = (-1) ^ d`.

### Cancelling the nonzero factor `(-1) ^ d`

**R6 · `linear_combination h`** **closes** an equation `lhs = rhs` when `lhs − rhs` equals `h.lhs − h.rhs` after
`ring` normalisation (so you may factor, expand and move terms freely). `linear_combination e * h` uses `e`
times `h`. Use it to state the factored form as a `have`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : a * b * a = b + c ⊢ b * (a * a - 1) = c` | closed |

**R7 · `pow_ne_zero`** changes the **goal**. The lemma is `pow_ne_zero n : a ≠ 0 → a ^ n ≠ 0` (for `ℝ`, and any
type without nonzero nilpotents). As a term: `pow_ne_zero _ (by norm_num)` proves `(-1 : ℝ) ^ d ≠ 0`, the `_`
being `d`. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After `refine pow_ne_zero n ?_` |
|---|---|
| `⊢ a ^ n ≠ 0` | `⊢ a ≠ 0` |

**R8 · `norm_num`** **closes** a numeral (in)equality such as `(-1 : ℝ) ≠ 0`, which the infoview prints as
`-1 ≠ 0`.

| Before | After |
|---|---|
| `⊢ -1 ≠ 0` | closed |

**R9 · `mul_eq_zero`** changes the **context**. The lemma is `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp h` turns a zero
product into the disjunction. Placeholders: `(a b : ℝ)` (any type without zero divisors).

| Before | After `have hab := mul_eq_zero.mp h` |
|---|---|
| `h : a * b = 0 ⊢ G` | `hab : a = 0 ∨ b = 0 ⊢ G` |

**R10 · `Or.resolve_left`** changes the **context**. `Or.resolve_left : A ∨ B → ¬A → B`; dot notation:
`hab.resolve_left ha`. `a ≠ 0` *is* `¬(a = 0)`, so `hd : (-1) ^ d ≠ 0` fits. Placeholders: `(a b : ℝ)`.

| Before | After `have hb := hab.resolve_left ha` |
|---|---|
| `hab : a = 0 ∨ b = 0, ha : a ≠ 0 ⊢ G` | `hb : b = 0 ⊢ G` |

**R11 · `linarith`** **closes** a linear (in)equality that follows from linear hypotheses. A nonlinear term such as
`a * a` or `(↑Λ).det * (↑Λ).det` counts as one unknown, so `x - 1 = 0` gives `x = 1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : a * a - 1 = 0 ⊢ a * a = 1` | closed |

### From the square to the two values

**R12 · `mul_self_eq_one_iff`** changes the **goal**. The lemma is `a * a = 1 ↔ a = 1 ∨ a = -1`. With
`refine mul_self_eq_one_iff.mp ?_` (or `exact mul_self_eq_one_iff.mp h1`) the disjunction is reduced to the
square. Placeholders: `{R : Type} [NonAssocRing R] [NoZeroDivisors R] (a : R)` (a ring with `1`, `-` and no
zero divisors: `ℝ`, `ℂ`, `ℤ` qualify).

| Before | After |
|---|---|
| `⊢ a = 1 ∨ a = -1` | `⊢ a * a = 1` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: an orthogonal matrix.** `hM : Mᵀ * M = 1` for `M : Matrix n n ℝ`. R2 gives `h : (Mᵀ * M).det = det 1`; one
`simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h` (R3, R4, and `Matrix.det_one :
(1 : Matrix n n R).det = 1`) leaves `h : M.det * M.det = 1`, and R12 finishes.

```lean-goal
⊢ M.det = 1 ∨ M.det = -1
```

**W2: cancelling `2 ^ n`.** From `h : x * 2 ^ n * x = 2 ^ n`: R6 proves `h0`, R7 with R8 proves `h2`, R9 → R10
gives `h3 : x * x - 1 = 0`, and R11 closes `x * x = 1`. The goal never changes; the context grows:

| Step | Context gains |
|---|---|
| `have h0 : (2 : ℝ) ^ n * (x * x - 1) = 0 := by linear_combination h` | `h0 : 2 ^ n * (x * x - 1) = 0` |
| `have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)` | `h2 : 2 ^ n ≠ 0` |
| `have h3 := (mul_eq_zero.mp h0).resolve_left h2` | `h3 : x * x - 1 = 0` |

```lean-goal
⊢ x * x = 1
```

---

## Traps

- `Λ` is implicit in R1: `have h := transpose_mul_minkowskiMatrix_mul_self` leaves it as an unsolved
  metavariable. Write `(Λ := Λ)`.
- `rw [Matrix.det_mul] at h` rewrites only one product pattern; `Λᵀ * η * Λ` has two nested products. Use
  `simp only [...] at h` (R3).
- In a `have` about `(-1) ^ d` alone, write the type: `((-1 : ℝ) ^ d) ≠ 0`. A bare `(-1) ^ d ≠ 0` is
  elaborated in `ℤ` (`(-1 : ℤ) ^ d`), and R10 then cannot use it against the real `h0`.
- `simp` leaves `det * (-1) ^ d * det`, a product, not `det ^ 2`; R12 is stated for `a * a`, so keep products.
- You cannot divide `h` by `(-1) ^ d` with `rw`; go through the zero-product form (R6 → R9 → R10).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Λᵀ η Λ = η` as a hypothesis | `transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)` | R1 |
| determinants of both sides of `h : M = N` | `congrArg Matrix.det h` | R2 |
| `det` of products / transposes / `η` in `h` | `simp only [Matrix.det_mul, Matrix.det_transpose, minkowskiMatrix.det_eq_neg_one_pow_d] at h` | R3–R5 |
| restate `h` in factored form | `have h0 : … := by linear_combination h` | R6 |
| `a ^ n ≠ 0` for a numeral `a ≠ 0` | `pow_ne_zero _ (by norm_num)` | R7, R8 |
| `a * b = 0` → `a = 0 ∨ b = 0` | `mul_eq_zero.mp h0` | R9 |
| drop the impossible side of `A ∨ B` | `hab.resolve_left ha` | R10 |
| `x - 1 = 0` → `x = 1` | `linarith` | R11 |
| `a * a = 1` → `a = 1 ∨ a = -1` | `mul_self_eq_one_iff.mp h1` | R12 |
| see the state | infoview | |
