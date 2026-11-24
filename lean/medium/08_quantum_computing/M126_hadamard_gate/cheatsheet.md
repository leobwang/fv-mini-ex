# M126 · The Hadamard gate: cheatsheet

Exercise: [`medium/08_quantum_computing/M126_hadamard_gate.lean`](../../../medium/08_quantum_computing/M126_hadamard_gate.lean).
Lean companion: [`M126_hadamard_gate.lean`](M126_hadamard_gate.lean) in this folder. Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`../../TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices, complex numbers,
real numbers cast into `ℂ`, and `Real.sqrt`.

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
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 matrices with complex entries. Rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `c • M` | scalar `c` times every entry of `M` |
| `↑x` | the real number `x` cast into `ℂ` |
| `√x` | `Real.sqrt x`, a real number |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `star M`, `Mᴴ` | the conjugate transpose: `Mᴴ i j = conj (M j i)` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z` |
| `v ᵥ* M` | row vector `v` times matrix `M` (R12) |
| `case «0».«1»` | the goal for entry (0, 1) |

---

## Part 1 · `hadamard_conj`

Statement: `H * H = 1 ∧ H * X * H = Z ∧ H * Z * H = X ∧ H * Y * H = -Y`. These are four equations between
2×2 complex matrices.

### Splitting the goal and adding facts

**R1 · `refine ⟨?_, ?_, ?_, ?_⟩`** changes the **goal list**: one goal becomes four. `∧` nests to the right, so
`A ∧ B ∧ C ∧ D` is `A ∧ (B ∧ (C ∧ D))`, and the pattern needs one `?_` per conjunct.
Placeholders: `(A B C D : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C ∧ D` | `⊢ A`, `⊢ B`, `⊢ C`, `⊢ D` |

**R2 · `have h : T := proof`** changes the **context**: it adds `h`. The goal stays the same. Placeholders:
`(T G : Prop)`. If you write it as `have h : T := by …`, indent the proof lines further than `have`.

| Before | After |
|---|---|
| `⊢ G` | `h : T ⊢ G` |

### Matrix equation → entries

**R3 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`, which says two matrices are
equal when every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R4 · `fin_cases i`** changes the **goal list and the context**. `i` leaves the context, and there is one goal
for each value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`. Use `fin_cases i <;> fin_cases j` to get all four
entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

### Evaluating an entry

`simp` applies R5–R9 by itself. Pass the names of your definitions (`simp [H, X]`). R10–R12 must be named
explicitly when `simp` gets stuck.

**R5 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. Placeholders:
`D` defined by `def D : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 3, 4]`.

| Before | After |
|---|---|
| `⊢ P D` | `⊢ P !![1, 2; 3, 4]` |

**R6 · entry of a literal** changes the **goal**. `simp` uses `Matrix.of_apply` and `Matrix.cons_val_…` for
this. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 0 1)` | `⊢ P b` |

**R7 · `Matrix.smul_apply`, then `smul_eq_mul`** changes the **goal**: the entry of a scaled matrix becomes a
product of numbers. Placeholders: `(c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After `rw [Matrix.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • M) i j)` | `⊢ P (c • M i j)` | `⊢ P (c * M i j)` |

**R8 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix
`1` become `1` on the diagonal and `0` elsewhere. Placeholders: `(1 : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R9 · `Matrix.neg_apply`** changes the **goal**: the entry of `-M` becomes minus the entry. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((-M) i j)` | `⊢ P (-M i j)` |

**R10 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a
commutative `+` with `0`, as `ℂ` does), `(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R11 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

### Scalars: inverses, casts, square roots

**R13 · `rw [← mul_inv]`** changes the **goal**. The lemma is `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`, and `←` uses
it right to left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)`. Here α has a commutative `*` and
an inverse `⁻¹`; `ℂ` and `ℝ` qualify.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R14 · `rw [← Complex.ofReal_mul]`** changes the **goal**. The lemma is `↑(x * y) = ↑x * ↑y`, and right to
left it moves `*` inside the cast, so a real lemma can apply. Placeholders: `(x y : ℝ)`, with the goal in `ℂ`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R15 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. The lemma is `0 ≤ x → √x * √x = x`, so the goal
is rewritten and a side goal `0 ≤ x` is added. Write `rw [Real.mul_self_sqrt (by norm_num)]` to prove the side
goal immediately. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R16 · `rw [inv_pow]`** changes the **goal**. The lemma is `a⁻¹ ^ n = (a ^ n)⁻¹`. Placeholders:
`{α : Type} [DivisionMonoid α] (a : α) (n : ℕ)`; `ℂ` and `ℝ` qualify.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ ^ n)` | `⊢ P (a ^ n)⁻¹` |

**R17 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `↑(x ^ n) = ↑x ^ n`, and right to left
it moves `^` inside the cast. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑x ^ n)` | `⊢ P ↑(x ^ n)` |

**R18 · `rw [Real.sq_sqrt hx]`** changes the **goal**. The lemma is `0 ≤ x → √x ^ 2 = x`, and here
`hx : 0 ≤ x` is given, so no side goal is added. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

R16–R18 are the `^ 2` route. R13–R15 are the `*` route, which matches
what `simp` leaves (W2).

**R19 · `ring_nf`** changes the **goal**: it rewrites the goal into a normal form for ring expressions. Among
other things, `a * a` becomes `a ^ 2`. Use it when your fact is stated with `^ 2` but the goal has `*`.
Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * a)` | `⊢ P (a ^ 2)` |

**R20 · `norm_num`** **closes** a goal made of numerals. This includes `⁻¹`, `/`, and casts of numerals such
as `(↑3)⁻¹ = 1 / 3`.

**R25 · `rw [mul_right_comm _ b]`** changes the **goal**. The lemma is `mul_right_comm : a * b * c = a * c * b`:
it swaps the last two factors of a product. `*` groups to the left, so `a * b * c` is `(a * b) * c`. Giving the
middle factor `b` makes it move only products with `b` in the middle, and `rw` rewrites every copy of that
product. Use it when a factor sits between the two you want to `rw` together. Placeholders:
`{α : Type} [CommMonoid α] (a b c : α)` (α has a commutative `*`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * b * c)` | `⊢ P (a * c * b)` |

**R26 · `ring`** **closes** an equation that holds in every commutative ring. It treats anything that is not
`+`, `*`, `-`, `^` or a numeral as an unknown, `I`, `√x` and `x⁻¹` included. So it knows neither `I * I = -1`
nor `√2 * √2 = 2`, and it does not use hypotheses. Use it when `norm_num` fails on a goal like
`1 / 2 * I + 1 / 2 * I = I`, where an unknown sits next to the numbers.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `ext i j; fin_cases i <;> fin_cases j` on `A * B = !![2, 2; 0, 3]` gives four entry goals (R3, R4).
`simp [A, B]` closes them all (R5–R11).

**W2: what `simp` leaves when the scalar is a real square root.** `K = (√3)⁻¹ • !![1, 0; 0, 1]`.
`simp [K]` closes the off-diagonal entries and stops on the diagonal ones at a **product**, never a power:

```lean-goal
⊢ (↑√3)⁻¹ * (↑√3)⁻¹ = 3⁻¹
```

**W3: proving that fact.** Apply R13, R14, R15 with `(by norm_num)`, then R20:

```lean-goal
⊢ (↑√3)⁻¹ * (↑√3)⁻¹ = 1 / 3
⊢ (↑√3 * ↑√3)⁻¹ = 1 / 3
⊢ (↑(√3 * √3))⁻¹ = 1 / 3
⊢ (↑3)⁻¹ = 1 / 3
```

---

## Part 2 · `hadamard_unitary`

Statement: `H ∈ Matrix.unitaryGroup (Fin 2) ℂ`. Turn the membership into an equation (R21, R22). That gives a
matrix equation, which you handle with R3–R11 and R13–R20 as in Part 1, plus R12 and R23–R24 for the
conjugate transpose.

**R21 · `rw [Matrix.mem_unitaryGroup_iff]`** changes the **goal**: membership becomes an equation.
Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ M ∈ unitaryGroup (Fin 2) ℂ` | `⊢ M * star M = 1` |

**R22 · `rw [Matrix.star_eq_conjTranspose]`** changes the **goal**: `star M` is written as the conjugate
transpose `Mᴴ`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star M)` | `⊢ P Mᴴ` |

**R23 · `Matrix.conjTranspose_apply`** changes the **goal**: entry `(i, j)` of `Mᴴ` becomes the conjugate of
entry `(j, i)`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (Mᴴ i j)` | `⊢ P (star (M j i))` |

**R24 · `Complex.conj_ofReal`** changes the **goal**: the conjugate of a real number cast into `ℂ` is the
number itself. `simp` applies it by itself. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R12 · `Matrix.vecMul`, `dotProduct`, then R11** change the **goal**: a row vector times a matrix, `v ᵥ* M`,
becomes an explicit sum. Placeholders: `(v : Fin 2 → ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2)`.

| Before | After `simp only [Matrix.vecMul]` | After `simp only [dotProduct]` | After `simp only [Fin.sum_univ_two]` |
|---|---|---|---|
| `⊢ P ((v ᵥ* M) j)` | `⊢ P (v ⬝ᵥ fun i => M i j)` | `⊢ P (∑ x, v x * M x j)` | `⊢ P (v 0 * M 0 j + v 1 * M 1 j)` |

**W4: with `ᴴ`, plain `simp [S]` gets stuck at `v ᵥ* Mᴴ`.** `S = !![1, 0; 0, I]`:

```lean-goal
⊢ (![1, 0] ᵥ* !![1, 0; 0, I]ᴴ) 0 = 1
```

Fix it with R12 after the fact. Better: give `simp` R10 and R11 from the start,
`simp [S, Matrix.mul_apply, Fin.sum_univ_two]`, and it never reaches this form.

---

## Traps

- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").
- In `have h : T := by`, the proof must be indented further than `have`. Otherwise its lines run against the
  outer goal.
- Write cast types out in a `have`: `(Real.sqrt 3 : ℂ)`. A bare `↑√3` with nothing saying `ℂ` stays in `ℝ`, and
  `rw` will not find it in a complex goal.
- `rw [h]` needs the left side of `h` to appear literally. `s * s` and `s ^ 2` are different text (R19).
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B ∧ C ∧ D` | `refine ⟨?_, ?_, ?_, ?_⟩` | R1 |
| add a fact | `have h : T := by …` | R2 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R3, R4 |
| evaluate entries | `simp [names]` | R5–R9 |
| entries of products | `simp [names, Matrix.mul_apply, Fin.sum_univ_two]` | R10, R11 |
| `a⁻¹ * b⁻¹ → (a * b)⁻¹` | `rw [← mul_inv]` | R13 |
| move `*` / `^` inside a real cast | `rw [← Complex.ofReal_mul]` / `rw [← Complex.ofReal_pow]` | R14, R17 |
| `√x * √x → x` / `√x ^ 2 → x` | `rw [Real.mul_self_sqrt (by norm_num)]` / `rw [Real.sq_sqrt (by norm_num)]` | R15, R18 |
| `a * a → a ^ 2` | `ring_nf` | R19 |
| numeric goal | `norm_num` | R20 |
| a factor in the way of `rw [h]` | `rw [mul_right_comm _ b]` | R25 |
| numbers next to an unknown such as `I` | `ring` | R26 |
| unitary → equation | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` | R21, R22 |
| `simp` stuck at `v ᵥ* M` | `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]` | R12 |
| see the state | infoview | |
