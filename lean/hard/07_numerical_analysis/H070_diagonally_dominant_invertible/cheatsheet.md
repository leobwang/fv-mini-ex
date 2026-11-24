# H070 · Diagonally dominant ⇒ invertible: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `refine ⟨x, ?_, ?_⟩`, `rw [h]`, `simp only [...] at h`, `exact`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `by`, `rw`, `simp`, `exact`, `have`, `refine`,
`∧`/`∃`/`¬`, functions as values.
**New here:** Mathlib's vectors `ι → ℝ` and matrices (`*ᵥ`, `⬝ᵥ`, `•`, `det`), finite sums over a
`Finset` (`∑ j ∈ s, f j`, `univ`, `erase`), absolute value `|·|` and its inequalities, the tactics
`linarith`, `by_contra`, `push Not`, `obtain`, `funext`, and `IsEmpty`.

**The mathematics.** `A` is an `n × n` real matrix; row `i` is *strictly diagonally dominant* when
`∑_{j ≠ i} |A i j| < |A i i|`.

- *Levy–Desplanques.* If every row is, then `det A ≠ 0`. Suppose `det A = 0`. Then some `v ≠ 0` has
  `A v = 0`. Pick `i` with `|v i|` maximal, so `|v i| > 0` and `|v j| ≤ |v i|` for all `j`. Row `i` of
  `A v = 0` reads `A i i v i = -∑_{j ≠ i} A i j v j`, so
  `|A i i| |v i| ≤ ∑_{j ≠ i} |A i j| |v j| ≤ (∑_{j ≠ i} |A i j|) |v i| < |A i i| |v i|`, a contradiction.
- *Gershgorin (real form).* If `A v = μ v` with `v ≠ 0`, the same row `i` gives
  `(μ - A i i) v i = ∑_{j ≠ i} A i j v j`, hence `|μ - A i i| |v i| ≤ (∑_{j ≠ i} |A i j|) |v i|`; cancel
  `|v i| > 0`. So the eigenvalue `μ` lies in the interval `[A i i - rᵢ, A i i + rᵢ]`, `rᵢ = ∑_{j ≠ i} |A i j|`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. A
  hypothesis that itself contains `, ` (such as `hmax : ∀ x' ∈ s, …`) is written next to the table.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the example finishes with
  `hG`; it exists only so the new hypothesis can be shown.
- Placeholders are written as Lean binders. `{ι : Type} [Fintype ι]` is any finite index type (the
  exercise uses `Fin n = {0, …, n-1}`); `[DecidableEq ι]` says equality on `ι` can be decided, which
  `s.erase i` needs; `Fin n` has both. Vectors are functions `ι → ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n → ℝ` | a vector in ℝⁿ: a function from the index set `Fin n = {0, …, n-1}` to `ℝ` |
| `Matrix (Fin n) (Fin n) ℝ` | a real `n × n` matrix: a function `Fin n → Fin n → ℝ`; `A i j` is row `i`, column `j` |
| `A *ᵥ v` | `Matrix.mulVec`: matrix times column vector, `(A v)ᵢ = ∑ⱼ A i j * v j` (R2) |
| `v ⬝ᵥ w` | `dotProduct`: `∑ᵢ v i * w i`; `mulVec` is defined through it |
| `μ • v` | scalar multiple of a vector: `(μ • v) i = μ * v i` (R23) |
| `0`, `0 i` | the zero vector `fun _ => 0`, and its `i`-th coordinate (`= 0` by R3) |
| `A.det` | `Matrix.det A`, the determinant |
| `univ` | `Finset.univ`, the finite set of *all* elements of a finite type (here all indices) |
| `univ.erase i` | `Finset.erase univ i`: all indices except `i` |
| `∑ j, f j` | `∑ j ∈ univ, f j`, the sum over all indices |
| `∑ j ∈ s, f j` | `Finset.sum s f`, the sum over the finite set `s` |
| `∑ x, A i x * v x` | the same sum with a bound variable Lean renamed (`x`, `x_1`, `i_1`): names of bound variables do not matter |
| `Finset ι` | a finite set of elements of `ι` (Mathlib's `Finset`); `(univ : Finset (Fin n))` fixes which type's `univ` is meant |
| `∅` | the empty `Finset` |
| `s.Nonempty` | `Finset.Nonempty s`: `∃ x, x ∈ s` |
| `∀ x ∈ s, P x` | `∀ x, x ∈ s → P x`: apply it as `h x hx` with `hx : x ∈ s` (R4 gives `x ∈ univ`) |
| `∃ x ∈ s, P x` | `∃ x, x ∈ s ∧ P x`: `obtain ⟨x, hx, hP⟩` takes it apart (R12) |
| `\|a\|` | `abs a`, the absolute value of a real number; `\|(-a)\|` is `\|-a\|` |
| `IsEmpty ι` | the type `ι` has no elements (true for `Fin 0`) |
| `a ≠ b` | `a = b → False` (R24) |
| `x✝ : j ∈ s` | an anonymous hypothesis (introduced by `fun j _ => …`); usable by `assumption`, not by name |
| `inst✝ : Fintype ι` | an anonymous type-class hypothesis: "`ι` is finite" |

---

## Part 1 · `row_eq` (milestone)

Statement: from `A *ᵥ v = 0`, row `i` with the diagonal term on the left:
`A i i * v i = -∑ j ∈ univ.erase i, A i j * v j`.

**R1 · `have hi := congrFun h i`** changes the **context**. `congrFun : f = g → ∀ a, f a = g a` turns an
equation of functions (vectors) into the equation of their `i`-th values. Placeholders:
`{ι β : Type} (f g : ι → β) (i : ι)`.

| Before | After |
|---|---|
| `h : f = g ⊢ G` | `hi : f i = g i ⊢ G` |

**R2 · `simp only [mulVec, dotProduct]`** changes the **goal** (with `at h`: the **context**): it unfolds
`Matrix.mulVec` and `dotProduct`, so the `i`-th coordinate of `A *ᵥ v` becomes the explicit sum. Lean
renames the bound variable to `x`. In the exercise you apply it `at this`, to the row equation from R1.
Placeholders: `{ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P ((A *ᵥ v) i)` | `⊢ P (∑ x, A i x * v x)` |

**R3 · `Pi.zero_apply`** changes the **context** (with `at h`): `(0 : ι → ℝ) i = 0`, the zero vector's
coordinate is the number `0`. Placeholders: `{ι : Type} (x : ℝ) (i : ι)`.

| Before | After |
|---|---|
| `h : x = 0 i ⊢ G` | `h : x = 0 ⊢ G` |

**R4 · `Finset.mem_univ`** **closes** `i ∈ univ`: `mem_univ i : i ∈ univ`. It is the membership proof
`add_sum_erase` (R5) and `exists_max_image`'s `∀ x ∈ univ, …` (R12) ask for. Placeholders:
`{ι : Type} [Fintype ι] (i : ι)`.

| Before | After |
|---|---|
| `⊢ i ∈ univ` | closed |

**R5 · `rw [← add_sum_erase _ _ (mem_univ i)]`** changes the **goal** (with `at h`: the **context**). The lemma is
`Finset.add_sum_erase (s : Finset ι) (f : ι → β) (h : a ∈ s) : f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`;
right to left it splits the term `a = i` off a sum over `s = univ`. The two `_` are `s` and `f`, found by
`rw`. Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (∑ j, f j)` | `⊢ P (f i + ∑ x ∈ univ.erase i, f x)` |

**R6 · `linarith`** **closes** a goal `t ≤ u`, `t < u`, `t = u` (or `False`) that follows from the
hypotheses by adding them with nonnegative coefficients. Anything that is not `+`, `-` or a numeral
times something, such as `a * x` or a whole `∑ …`, is one unknown. It uses every hypothesis in the
context. Placeholders: `(a x s c : ℝ)`.

| Before | After |
|---|---|
| `h : a * x + s = c ⊢ a * x = c - s` | closed |

---

## Part 2 · `exists_max_coord` (milestone)

Statement: a nonzero vector has a coordinate `i` with `0 < |v i|` and `|v j| ≤ |v i|` for every `j`.
`Fin 0` has no elements, so first show `univ` is nonempty, using `v ≠ 0`.

**R7 · `by_contra hc`** changes the **goal and the context**: to prove `Q`, assume `hc : ¬Q` and prove
`False`. Placeholders: `(Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `hc : ¬Q ⊢ False` |

**R8 · `rw [not_nonempty_iff_eq_empty] at hc`** changes the **context**. The lemma is
`Finset.not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅`; `rw` rewrites with an `↔` like with an `=`.
Placeholders: `{ι : Type} (s : Finset ι)`.

| Before | After |
|---|---|
| `hc : ¬s.Nonempty ⊢ G` | `hc : s = ∅ ⊢ G` |

**R9 · `rw [univ_eq_empty_iff] at hc`** changes the **context**. The lemma is
`Finset.univ_eq_empty_iff : univ = ∅ ↔ IsEmpty ι`. Placeholders: `{ι : Type} [Fintype ι]`.

| Before | After |
|---|---|
| `hc : univ = ∅ ⊢ G` | `hc : IsEmpty ι ⊢ G` |

**R10 · `IsEmpty.false`, `False.elim`** change the **context**, then **close** the goal.
`IsEmpty.false : IsEmpty ι → ι → False`, written `hc.false i`; `hf.elim : Q` for `hf : False` and any `Q`.
In the exercise this proves `v j = 0 j` for each `j` of the empty type `Fin n`. Placeholders:
`{ι : Type} (hc : IsEmpty ι) (i : ι) (Q : Prop)`.

| Before | After `have hf := hc.false i` |
|---|---|
| `hc : IsEmpty ι ⊢ Q` | `hf : False ⊢ Q` |

**R11 · `funext j`** changes the **goal and the context**: two functions are equal when all their values
are. The term form `funext fun j => (proof of v j = w j)` is what you pass to `hv : v ≠ 0` to get `False`
(`exact hv (funext fun j => …)`). Placeholders: `{ι : Type} (v : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ v = 0` | `j : ι ⊢ v j = 0 j` |

`v j = 0 j` and `v j = 0` are the same statement up to unfolding, so a proof of `v j = 0` is accepted.

**R12 · `obtain ⟨i, hi, hmax⟩ := exists_max_image s f hs`** changes the **context**. The lemma is
`Finset.exists_max_image (s : Finset ι) (f : ι → ℝ) : s.Nonempty → ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x`
(any linearly ordered codomain works). `obtain ⟨…⟩` splits the `∃` and the `∧` inside it; writing `-`
for a part throws it away (`⟨i, -, hmax⟩`). Use `f := fun j => |v j|`. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ) (hs : s.Nonempty)`.

| Before | After |
|---|---|
| `hs : s.Nonempty ⊢ G` | `i : ι, hi : i ∈ s ⊢ G` |

and the context gains `hmax : ∀ x' ∈ s, f x' ≤ f i`. With `s = univ`, use it as `hmax j (mem_univ j)` (R4).

**R13 · `push Not at hc`** changes the **context**: it pushes `¬` inward and uses `¬(a < b) ↔ b ≤ a`
(and `¬(a ≤ b) ↔ b < a`, `¬∀ ↔ ∃ ¬`, …). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `hc : ¬0 < a ⊢ G` | `hc : a ≤ 0 ⊢ G` |

**R14 · `abs_nonpos_iff`** changes the **context**: `abs_nonpos_iff : |a| ≤ 0 ↔ a = 0`; `.mp` uses the
`→` direction. Placeholders: `(a : ℝ) (h : |a| ≤ 0)`.

| Before | After `have h0 := abs_nonpos_iff.mp h` |
|---|---|
| `⊢ G` | `h0 : a = 0 ⊢ G` |

**R15 · `h.trans`** (`le_trans : a ≤ b → b ≤ c → a ≤ c`) changes the **goal** when used as
`refine h.trans ?_`: what is left is the second half of the chain. As a term, `h.trans h'` proves `a ≤ c`.
Placeholders: `(a b c : ℝ) (h : a ≤ b)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

---

## Part 3 · `diag_le_offdiag` (milestone)

Statement: with `A *ᵥ v = 0` and `|v j| ≤ |v i|` for all `j`,
`|A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i|`.

**R16 · `abs_mul`** changes the **goal**: `abs_mul : |a * b| = |a| * |b|`. Right to left (`rw [← abs_mul]`)
it merges `|A i i| * |v i|` into `|A i i * v i|`, so `row_eq` can rewrite inside; left to right it splits
one term for R21. Placeholders: `(a b : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ P (|a| * |b|)
⊢ P |a * b|
```

**R17 · `abs_neg`** changes the **goal**: `abs_neg : |-a| = |a|`. Lean prints `|-a|` as `|(-a)|`.
Placeholders: `(a : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ P |(-a)|
⊢ P |a|
```

**R18 · `Finset.sum_mul`** changes the **goal**: `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`, a factor moves
into the sum. Placeholders: `{ι : Type} (s : Finset ι) (f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, f i) * a)` | `⊢ P (∑ i ∈ s, f i * a)` |

**R19 · `refine (abs_sum_le_sum_abs _ _).trans ?_`** changes the **goal**. The lemma is
`Finset.abs_sum_le_sum_abs (f : ι → ℝ) (s : Finset ι) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|` (the triangle
inequality); chained with R15 it leaves the bound for the sum of absolute values. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ) (c : ℝ)`.

Before, then after (`|` cannot sit in a table's code span):

```lean-goal
⊢ |∑ i ∈ s, f i| ≤ c
⊢ ∑ i ∈ s, |f i| ≤ c
```

**R20 · `refine sum_le_sum fun j hj => ?_`** changes the **goal and the context**. The lemma is
`Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`: compare term by term. Write
`fun j _ => ?_` when you do not need `hj` (it then appears as `x✝`). Placeholders:
`{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `j : ι, hj : j ∈ s ⊢ f j ≤ g j` |

**R21 · `mul_le_mul_of_nonneg_left`** changes the **goal list**: `b ≤ c → 0 ≤ a → a * b ≤ a * c`. As
`refine … ?_ ?_` it leaves both premises; as `exact mul_le_mul_of_nonneg_left hbc ha` it closes the goal.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a * b ≤ a * c` | `⊢ b ≤ c`, `⊢ 0 ≤ a` |

**R22 · `abs_nonneg`** **closes** `0 ≤ |a|`: `abs_nonneg a : 0 ≤ |a|`. Placeholders: `(a : ℝ)`.

Before; `exact abs_nonneg a` closes it:

```lean-goal
⊢ 0 ≤ |a|
```

### Worked combinations (not the exercise's objects)

**W1: row `i` of a linear system `A x = b`** (the formula behind the Jacobi iteration), R1, R2, R5, R6:

Goal throughout: `A i i * x i = b i - ∑ j ∈ univ.erase i, A i j * x j`, from `h : A *ᵥ x = b`. The
hypothesis `hi` changes:

| Step | `hi` after it |
|---|---|
| R1 `have hi := congrFun h i` | `hi : (A *ᵥ x) i = b i` |
| R2 `simp only [mulVec, dotProduct] at hi` | `hi : ∑ x_1, A i x_1 * x x_1 = b i` |
| R5 `rw [← add_sum_erase _ _ (mem_univ i)] at hi` | `hi : A i i * x i + ∑ x_1 ∈ univ.erase i, A i x_1 * x x_1 = b i` |
| R6 `linarith` | goal closed |

```lean-goal
⊢ A i i * x i = b i - ∑ j ∈ univ.erase i, A i j * x j
```

**W2: a weighted triangle inequality**, `|∑ j ∈ s, a j * x j| ≤ (∑ j ∈ s, |a j|) * M` when every
`|x j| ≤ M`: R18, then R19 and R20 in one `refine`, then R16, then R21 with R22:

```lean-goal
⊢ |∑ j ∈ s, a j * x j| ≤ (∑ j ∈ s, |a j|) * M
⊢ |∑ j ∈ s, a j * x j| ≤ ∑ i ∈ s, |a i| * M
⊢ |a j * x j| ≤ |a j| * M
⊢ |a j| * |x j| ≤ |a j| * M
```

---

## Part 4 · `eig_row_eq` (milestone)

Statement: from `A *ᵥ v = μ • v`, row `i`: `(μ - A i i) * v i = ∑ j ∈ univ.erase i, A i j * v j`. Same
steps as `row_eq`; the right side `(μ • v) i` needs R23 instead of R3.

**R23 · `Pi.smul_apply`, then `smul_eq_mul`** change the **context** (with `at h`). `Pi.smul_apply`:
`(c • v) i = c • v i` (scale, then take a coordinate = take the coordinate, then scale); `smul_eq_mul`:
`c • a = c * a` for two numbers. Placeholders: `{ι : Type} (c x : ℝ) (v : ι → ℝ) (i : ι)`.

| Before | After `Pi.smul_apply` | After `smul_eq_mul` |
|---|---|---|
| `h : x = (c • v) i ⊢ G` | `h : x = c • v i ⊢ G` | `h : x = c * v i ⊢ G` |

---

## Part 5 · `det_ne_zero_of_diag_dominant`

Statement: strict diagonal dominance of every row gives `A.det ≠ 0`.

**R24 · `intro hab`** on a goal `a ≠ b` changes the **goal and the context**: `a ≠ b` is by definition
`a = b → False`, so `intro` assumes the equation. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `hab : a = b ⊢ False` |

**R25 · `obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet`** changes the **context**. The
lemma is `Matrix.exists_mulVec_eq_zero_iff : (∃ v, v ≠ 0 ∧ M *ᵥ v = 0) ↔ M.det = 0` (over a commutative ring
with no zero divisors, such as `ℝ`); `.mpr` is the direction `←`: a zero determinant gives a nonzero kernel vector. Placeholders:
`{ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hdet : M.det = 0)`.

| Before | After |
|---|---|
| `hdet : M.det = 0 ⊢ G` | `v : ι → ℝ, hv : v ≠ 0, hMv : M *ᵥ v = 0 ⊢ G` |

**R26 · `mul_lt_mul_of_pos_right`** changes the **context** (with `have`):
`b < c → 0 < a → b * a < c * a`. Multiply the dominance inequality `h i` by `|v i| > 0`. Placeholders:
`(a b c : ℝ) (h : b < c) (ha : 0 < a)`.

| Before | After `have h2 := mul_lt_mul_of_pos_right h ha` |
|---|---|
| `ha : 0 < a ⊢ G` | `h2 : b * a < c * a ⊢ G` |

Then `h1 : X ≤ Y` and `h2 : Y < X` (with the same `X`, `Y` written identically) close `False` by `linarith` (R6).

---

## Part 6 · `gershgorin_real`

Statement: `v ≠ 0`, `A *ᵥ v = μ • v` give some `i` with `|μ - A i i| ≤ ∑ j ∈ univ.erase i, |A i j|`.

**R27 · `refine le_of_mul_le_mul_right ?_ hc`** changes the **goal**. The lemma is
`le_of_mul_le_mul_right : a * c ≤ b * c → 0 < c → a ≤ b`: to prove `a ≤ b`, prove it multiplied by a
positive `c`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a ≤ b` | `⊢ a * c ≤ b * c` |

After `refine ⟨i, le_of_mul_le_mul_right ?_ hvi⟩` the goal is
`|μ - A i i| * |v i| ≤ (∑ j ∈ univ.erase i, |A i j|) * |v i|`, and the rest is Part 3 with `eig_row_eq`
in place of `row_eq` (no `abs_neg` this time).

---

## Traps

- `Fin 0` is empty, so `univ : Finset (Fin n)` may be empty and `exists_max_image` needs
  `univ.Nonempty`. Get it from `v ≠ 0` (if `Fin n` is empty, every `v` equals `0`) **before** taking a max.
- `rw [← abs_mul]` before `rw [row_eq …]`: `row_eq` rewrites `A i i * v i`, which appears only inside
  `|A i i * v i|`, not in `|A i i| * |v i|`.
- `rw [sum_mul]` moves `* |v i|` into the sum, so the right side becomes `∑ … |A i j| * |v i|`, with the
  bound variable printed as `i_1`. That is the shape `sum_le_sum` (R20) needs.
- Do not use `gcongr` for the last term-wise step `|A i j| * |v j| ≤ |A i j| * |v i|`: it descends into
  `|·|` and asks for `0 ≤ v j`. Use R21 with `hi j` and R22.
- `linarith` treats `(∑ j ∈ univ.erase i, |A i j|) * |v i|` as one unknown; it closes `False` from
  `h1 : X ≤ Y` and `h2 : Y < X` only when `X` and `Y` are the same expressions in both. Produce `h2` with
  R26 from `h i`, which gives exactly the products `h1` has.
- `exact?`, `apply?`, `rw?`, `try?`, `hint` and the Mathlib theorems `det_ne_zero_of_sum_row_lt_diag`,
  `det_ne_zero_of_sum_col_lt_diag`, `eigenvalue_mem_ball` are banned.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| row `i` of a vector equation `h : f = g` | `have hi := congrFun h i` | R1 |
| `(A *ᵥ v) i` → `∑ j, A i j * v j` | `simp only [mulVec, dotProduct] at hi` | R2 |
| `0 i` → `0` | `Pi.zero_apply` | R3 |
| `(c • v) i` → `c * v i` | `Pi.smul_apply, smul_eq_mul` | R23 |
| `i ∈ univ` | `mem_univ i` | R4 |
| split term `i` off `∑ j, f j` | `rw [← add_sum_erase _ _ (mem_univ i)] at h` | R5 |
| linear arithmetic, sums as unknowns | `linarith` | R6 |
| proof by contradiction | `by_contra hc` | R7 |
| `¬s.Nonempty` → `s = ∅` → `IsEmpty ι` | `rw [not_nonempty_iff_eq_empty, univ_eq_empty_iff] at hc` | R8, R9 |
| anything from an element of an empty type | `(hc.false i).elim` | R10 |
| vector equality pointwise | `funext j` / `funext fun j => …` | R11 |
| index of the largest `f j` on nonempty `s` | `obtain ⟨i, -, hi⟩ := exists_max_image s f hs` | R12 |
| `¬0 < a` → `a ≤ 0` | `push Not at hc` | R13 |
| `\|a\| ≤ 0` → `a = 0` | `abs_nonpos_iff.mp` | R14 |
| chain `a ≤ b ≤ c` | `h.trans h'` / `refine h.trans ?_` | R15 |
| `\|a\| * \|b\|` ↔ `\|a * b\|` | `rw [← abs_mul]` / `rw [abs_mul]` | R16 |
| `\|-a\|` → `\|a\|` | `rw [abs_neg]` | R17 |
| factor into a sum | `rw [sum_mul]` | R18 |
| triangle inequality for a sum | `refine (abs_sum_le_sum_abs _ _).trans ?_` | R19 |
| compare sums term by term | `refine sum_le_sum fun j _ => ?_` | R20 |
| `a * b ≤ a * c` from `b ≤ c`, `0 ≤ a` | `mul_le_mul_of_nonneg_left hbc ha` | R21 |
| `0 ≤ \|a\|` | `abs_nonneg a` | R22 |
| goal `a ≠ b` | `intro hab` | R24 |
| `det = 0` → kernel vector | `Matrix.exists_mulVec_eq_zero_iff.mpr hdet` | R25 |
| multiply `b < c` by `a > 0` | `mul_lt_mul_of_pos_right h ha` | R26 |
| cancel a positive factor in `≤` | `refine le_of_mul_le_mul_right ?_ hc` | R27 |
