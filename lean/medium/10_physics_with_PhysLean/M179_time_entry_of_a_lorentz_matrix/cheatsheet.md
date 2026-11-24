# M179 · Time entry of a Lorentz matrix: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's Lorentz group `LorentzGroup d`
and Minkowski matrix `η`; Mathlib's matrices indexed by a sum type `Fin 1 ⊕ Fin d`, transpose `Mᵀ`,
`diagonal`, finite sums `∑` and the lemmas that evaluate them; the closers `linear_combination` and
`linarith`.

The physics: in `d` space dimensions, `η = diag(1, −1, …, −1)` is the Minkowski metric (signature
`(+, −, …, −)`), indexed by `Fin 1 ⊕ Fin d`: one time index `Sum.inl 0` and `d` space indices `Sum.inr i`.
A Lorentz matrix `Λ` preserves it: `Λᵀ η Λ = η` and, equivalently, `Λ η Λᵀ = η`. Write `Λ⁰₀` for the
time–time entry `Λ (Sum.inl 0) (Sum.inl 0)`, `Λⁱ₀` for `Λ (Sum.inr i) (Sum.inl 0)` (column 0) and `Λ⁰ᵢ` for
`Λ (Sum.inl 0) (Sum.inr i)` (row 0). The `(0, 0)` entries of the two identities read

$$(\Lambda^0{}_0)^2 - \sum_{i} (\Lambda^i{}_0)^2 = 1, \qquad (\Lambda^0{}_0)^2 - \sum_{i} (\Lambda^0{}_i)^2 = 1,$$

so `(Λ⁰₀)² ≥ 1`, and `Λ⁰₀ = 1` forces both sums of squares, hence every `Λⁱ₀` and `Λ⁰ᵢ`, to be `0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`/`refine`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal or hypothesis. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype n]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- In a table, `\|` is a literal `|` (absolute value); Lean writes `|a|`.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 1 ⊕ Fin d` | the index type, a disjoint union: `Sum.inl 0` is the time index, `Sum.inr i` (`i : Fin d`) the `i`-th space index |
| `Matrix m n α` | functions `m → n → α`; `M i j` is the entry in row `i`, column `j` |
| `LorentzGroup d`, `𝓛 d` | the **set** of real matrices on `Fin 1 ⊕ Fin d` with `Λ * dual Λ = 1`, where `dual Λ = η Λᵀ η`; `𝓛 d` is how it prints |
| `Λ : ↑(𝓛 d)` | `Λ` is an element of that set used as a type (a subtype): a matrix paired with a proof it is in the set |
| `Λ.1`, `↑Λ` | the underlying matrix of `Λ`; you write `Λ.1`, the infoview prints `↑Λ` |
| `η` | `minkowskiMatrix`, `diag(1, −1, …, −1)`. Notation from `open minkowskiMatrix` |
| `Mᵀ` | transpose: `Mᵀ i j = M j i` (R5) |
| `diagonal c` | the diagonal matrix with diagonal `c : n → α`: entry `(i, j)` is `c i` if `i = j`, else `0` (R7) |
| `Sum.elim f g` | the function on `α ⊕ β` that is `f` on `Sum.inl a` and `g` on `Sum.inr b` (R11) |
| `Sum.elim 1 (-1)` | the diagonal of `η`: `1` at the time index, `-1` at every space index |
| `1 a`, `(-1) i` | the constant function `1` (or `-1`) applied to `a`; `simp` turns it into the number (R11) |
| `∑ x, f x` | the finite sum of `f x` over every `x` of a finite type, i.e. `∑ x ∈ Finset.univ, f x` |
| `Finset.univ` | the finite set of all elements of a finite type (`[Fintype ι]`) |
| `∑ a₁, …`, `∑ x, …` | the same sums; Lean renames bound variables freely |
| `∑ j, f j * if j = l then c j else 0` | `f j * (if … )`: `if` extends to the right, so Lean drops the brackets |
| `-∑ x, f x * g x` | `-(∑ x, f x * g x)`: the minus applies to the whole sum (`∑` extends to the right) |
| `∀ i ∈ Finset.univ, Q i` | `∀ i, i ∈ Finset.univ → Q i`; use it as `h i (Finset.mem_univ i)` (R21) |
| `a ^ 2`, `1 ^ 2` | squares (`HPow`, natural-number exponent); `1 ^ 2` appears after `rw [h1]` (R19) |
| `\|a\|` | absolute value of `a : ℝ` |
| `case refine_1`, `case refine_2` | the names of the first and second goals after `refine` (R16) |

---

## Part 1 · `time_entry`

Statement: for `Λ : LorentzGroup d`, `1 ≤ |Λ⁰₀|`, and if `Λ⁰₀ = 1` then for every `i : Fin d`,
`Λⁱ₀ = 0` and `Λ⁰ᵢ = 0`.

### One entry of the defining identities

**R1 · `congrFun (congrFun h i) j`** changes the **context**: from a matrix equation `h : M = N` it gives the
entry equation. `congrFun : f = g → ∀ x, f x = g x`; a matrix is a function of two arguments, so apply it
twice. Use it as `have hij := congrFun (congrFun h i) j`. Placeholders: `{m n α : Type}
(M N : Matrix m n α) (h : M = N) (i : m) (j : n)`.

| Before | After |
|---|---|
| `h : M = N ⊢ G` | `hij : M i j = N i j ⊢ G` |

**R2 · `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self`** changes the **context**. The lemma is
`Λᵀ * η * Λ = η` (Lorentz matrices preserve `η`). Its `Λ` is implicit (in `{…}`), so Lean cannot guess it
from nothing: name it, `transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)`. Placeholders: `{d : ℕ}
(Λ : LorentzGroup d)`.

| Before | After |
|---|---|
| `⊢ G` | `h : (↑Λ)ᵀ * η * ↑Λ = η ⊢ G` |

**R3 · `LorentzGroup.mul_minkowskiMatrix_mul_transpose`** changes the **context**: the same with the
transpose on the right, `Λ * η * Λᵀ = η`. Its `(0, 0)` entry is about row 0 instead of column 0.

| Before | After |
|---|---|
| `⊢ G` | `h : ↑Λ * η * (↑Λ)ᵀ = η ⊢ G` |

### Evaluating the entry

You never apply R4–R11 one by one in the solution: `simp [Matrix.mul_apply, Fintype.sum_sum_type,
minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at h` does all of them. Name R4, R6, R7, R9; `simp`
uses R5, R8, R10, R11 by itself. The entries show what each piece does, so you can read what `simp`
leaves. Every one of them also works inside a hypothesis with `… at h`.

**R4 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{il} = \sum_j M_{ij} N_{jl}$. Placeholders: `{m n p α : Type} [Fintype n] [Mul α] [AddCommMonoid α]`
(`n` finite so the sum makes sense, as `Fin 1 ⊕ Fin d` is; `α` has `*` and a commutative `+` with `0`, as
`ℝ` does), `(M : Matrix m n α) (N : Matrix n p α) (i : m) (l : p)`. In `Λᵀ * η * Λ = (Λᵀ * η) * Λ` it
fires twice: a sum inside a sum.

| Before | After |
|---|---|
| `⊢ P ((M * N) i l)` | `⊢ P (∑ j, M i j * N j l)` |

**R5 · `Matrix.transpose_apply`** changes the **goal**: `Mᵀ i j = M j i`. Placeholders:
`{m n α : Type} (M : Matrix m n α) (i : n) (j : m)`.

| Before | After |
|---|---|
| `⊢ P (Mᵀ i j)` | `⊢ P (M j i)` |

**R6 · `minkowskiMatrix.as_diagonal`** changes the **goal**: `η = diagonal (Sum.elim 1 (-1))`. Placeholders:
`{d : ℕ} (i j : Fin 1 ⊕ Fin d)`. (`minkowskiMatrix.inl_0_inl_0 : η (Sum.inl 0) (Sum.inl 0) = 1` is the
`(0, 0)` entry directly; `simp` uses it for the right-hand side.)

| Before | After |
|---|---|
| `⊢ P (η i j)` | `⊢ P (diagonal (Sum.elim 1 (-1)) i j)` |

**R7 · `Matrix.diagonal_apply`** changes the **goal**: `diagonal c i j = if i = j then c i else 0`.
Placeholders: `{n α : Type} [DecidableEq n] [Zero α] (c : n → α) (i j : n)` (`i = j` must be decidable and
`α` needs a `0`; true for `Fin 1 ⊕ Fin d` and `ℝ`).

| Before | After |
|---|---|
| `⊢ P (diagonal c i j)` | `⊢ P (if i = j then c i else 0)` |

**R8 · `mul_ite`, `mul_zero`, `Finset.sum_ite_eq'`, `Finset.mem_univ`** change the **goal**: a sum whose terms
are zero except at `j = l` becomes its `l`-th term. `mul_ite` moves the `*` into both branches,
`Finset.sum_ite_eq' : (∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`, and
`Finset.mem_univ` settles `l ∈ Finset.univ`. Placeholders: `{n : Type} [Fintype n] [DecidableEq n]
(f c : n → ℝ) (l : n)`.

| Before | After `simp only [mul_ite, mul_zero]` | After `simp only [Finset.sum_ite_eq']` | After `simp only [Finset.mem_univ, if_true]` |
|---|---|---|---|
| `⊢ P (∑ j, f j * if j = l then c j else 0)` | `⊢ P (∑ x, if x = l then f x * c x else 0)` | `⊢ P (if l ∈ Finset.univ then f l * c l else 0)` | `⊢ P (f l * c l)` |

**R9 · `Fintype.sum_sum_type`** changes the **goal**: a sum over `α ⊕ β` splits into the `inl` part and the
`inr` part. Here: the time term plus the sum over space. Placeholders: `{α β M : Type} [Fintype α]
[Fintype β] [AddCommMonoid M] (f : α ⊕ β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ a₁, f (Sum.inl a₁) + ∑ a₂, f (Sum.inr a₂))` |

**R10 · `Fin.sum_univ_one`** changes the **goal**: a sum over `Fin 1` is its only term `f 0`. `simp` gets
there through `Finset.univ_unique` and `Finset.sum_singleton`. Placeholders: `{M : Type}
[AddCommMonoid M] (f : Fin 1 → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, f a)` | `⊢ P (f 0)` |

**R11 · `Sum.elim_inl`, `Sum.elim_inr`, then `Pi.one_apply`, `Pi.neg_apply`** change the **goal**: they evaluate
the diagonal of `η`. `Sum.elim f g (Sum.inl a) = f a`, `Sum.elim f g (Sum.inr b) = g b`; then the constant
functions `1`, `-1` applied to an index become the numbers. Placeholders: `{d : ℕ} (a : Fin 1) (i : Fin d)`.

| Before | After `simp only [Sum.elim_inl, Sum.elim_inr]` | After `simp only [Pi.one_apply, Pi.neg_apply]` |
|---|---|---|
| `⊢ P (Sum.elim 1 (-1) (Sum.inl a)) (Sum.elim 1 (-1) (Sum.inr i))` | `⊢ P (1 a) ((-1) i)` | `⊢ P 1 (-1)` |

**W1** (`M` with `Mᵀ * M = 1`, not a Lorentz matrix): after R1 and
`simp [Matrix.mul_apply, Fintype.sum_sum_type] at h`, the `(0, 0)` entry is a **product** form, never `^ 2`,
the space sum split off by R9:

```lean
h :
  M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 0) (Sum.inl 0) +
      ∑ a₂, M (Sum.inr a₂) (Sum.inl 0) * M (Sum.inr a₂) (Sum.inl 0) =
    1
```

With `η` in the middle (`Λᵀ * η * Λ`) the space terms pick up the `-1` of R11, and `simp` pulls that sign
out of the sum (`mul_neg`, `Finset.sum_neg_distrib : ∑ x ∈ s, -f x = -∑ x ∈ s, f x`), so it writes them as
`-∑ x, …`. For `hc` it leaves exactly

```lean
hc :
  ↑Λ (Sum.inl 0) (Sum.inl 0) * ↑Λ (Sum.inl 0) (Sum.inl 0) +
      -∑ x, ↑Λ (Sum.inr x) (Sum.inl 0) * ↑Λ (Sum.inr x) (Sum.inl 0) =
    1
```

and `hr` is the same with `↑Λ (Sum.inl 0) (Sum.inr x)` in the sum. **W2** shows `η` on its own: from `M * η = c • 1`, the same `simp` with R6, R7 leaves
`h : M (Sum.inl 0) (Sum.inl 0) = c`.

### From the entry to squares

**R12 · `simp only [_root_.sq]`** changes the **goal**: `sq : a ^ 2 = a * a`, rewritten everywhere, also under
`∑`. Use it on the goal `a ^ 2 = 1 + ∑ …` so it has the product form `simp` left in `h`. The `_root_.`
prefix is required: `open minkowskiMatrix` makes a bare `sq` mean `minkowskiMatrix.sq : η * η = 1`.
Placeholders: `{d : ℕ} (a : ℝ) (f : Fin d → ℝ)`, `P : ℝ → ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P (a ^ 2) (∑ i, f i ^ 2)` | `⊢ P (a * a) (∑ x, f x * f x)` |

**R13 · `linear_combination h`** **closes** an equation `lhs = rhs` when `lhs - rhs` equals
`h.lhs - h.rhs` as a ring identity (more generally `linear_combination c₁ * h₁ + c₂ * h₂`). It treats
`∑ x, f x * f x` as one unknown, so the sum in the goal must be written exactly as in `h` (R12).
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : a + -b = c ⊢ a = c + b` | closed |

**R14 · `apply Finset.sum_nonneg`** changes the **goal**: `Finset.sum_nonneg : (∀ i ∈ s, 0 ≤ f i) →
0 ≤ ∑ i ∈ s, f i`. As a term, `Finset.sum_nonneg (fun i _ => …)` (the `_` is the unused proof of
`i ∈ s`). Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ∑ i, f i` | `⊢ ∀ i ∈ Finset.univ, 0 ≤ f i` |

**R15 · `sq_nonneg a`** **closes** `0 ≤ a ^ 2`. With `_` for `a`, Lean finds it from the goal.

| Before | After |
|---|---|
| `⊢ 0 ≤ a ^ 2` | closed |

### Splitting, and `1 ≤ |Λ⁰₀|`

**R16 · `refine ⟨?_, fun h1 i => ?_⟩`** changes the **goal list**: `A ∧ (B → ∀ i, C i)` becomes two goals. The
second `?_` sits inside `fun h1 i => …`, so its goal has `h1 : B` and `i : ι` in the context: `intro` done
inside the `refine`. Placeholders: `{ι : Type} (A B : Prop) (C : ι → Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ (B → ∀ (i : ι), C i)` | `⊢ A`, `h1 : B, i : ι ⊢ C i` |

**R17 · `refine (one_le_sq_iff_one_le_abs a).mp ?_`** changes the **goal**. The lemma is
`one_le_sq_iff_one_le_abs a : 1 ≤ a ^ 2 ↔ 1 ≤ |a|`; `.mp` is its left-to-right direction, so the goal
`1 ≤ |a|` is replaced by `1 ≤ a ^ 2`. Placeholders: `{α : Type} [Ring α] [LinearOrder α]
[IsStrictOrderedRing α] (a : α)` (an ordered ring; `ℝ` qualifies). Before and after:

```lean-goal
⊢ 1 ≤ |a|
⊢ 1 ≤ a ^ 2
```

**R18 · `linarith`** **closes** a linear equation or inequality that follows from the hypotheses by adding
multiples of them. Nonlinear pieces such as `a ^ 2` and `∑ i, f i ^ 2` are treated as unknowns, so give it the
facts about them (`h1`, `h2`) in the context. Placeholders: `{d : ℕ} (a : ℝ) (f : Fin d → ℝ)`.

| Before | After |
|---|---|
| `⊢ 1 ≤ a ^ 2` (with `h1 : a ^ 2 = 1 + ∑ i, f i ^ 2`, `h2 : 0 ≤ ∑ i, f i ^ 2`) | closed |

### `Λ⁰₀ = 1` ⇒ the rest of row 0 and column 0 vanishes

**R19 · `rw [h] at h₁ h₂`** changes the **context**: it rewrites `a` to `b` in both hypotheses at once.
Placeholders: `(a b : ℝ) (h : a = b)`, `P Q : ℝ → Prop`.

| Before | After |
|---|---|
| `h₁ : P a, h₂ : Q a ⊢ G` | `h₁ : P b, h₂ : Q b ⊢ G` |

**R20 · `rw [Finset.sum_eq_zero_iff_of_nonneg hf]`** changes the **goal** (with `at h`, the hypothesis). The
lemma is `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`: a sum of nonnegative terms is
zero iff every term is. Pass the nonnegativity as `(fun i _ => sq_nonneg _)` (R15). Placeholders:
`{ι : Type} [Fintype ι] (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i ^ 2 = 0` | `⊢ ∀ i ∈ Finset.univ, f i ^ 2 = 0` |

**R21 · `Finset.mem_univ i : i ∈ Finset.univ`** is the membership proof a `∀ i ∈ Finset.univ, …` hypothesis
asks for. With `h : ∀ i ∈ Finset.univ, Q i`, `have hi := h i (Finset.mem_univ i)` changes the **context**.
Placeholders: `{ι : Type} [Fintype ι] (Q : ι → Prop) (i : ι)`.

| Before | After |
|---|---|
| `i : ι ⊢ G` | `hi : Q i ⊢ G` |

**R22 · `refine (pow_eq_zero_iff two_ne_zero).mp ?_`** changes the **goal**. The lemma is
`pow_eq_zero_iff : n ≠ 0 → (a ^ n = 0 ↔ a = 0)` and `two_ne_zero : 2 ≠ 0`; `.mp` turns `a ^ 2 = 0` into
`a = 0`. As a term: `(pow_eq_zero_iff two_ne_zero).mp hi`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a = 0` | `⊢ a ^ 2 = 0` |

**W3** chains R20 → R21 → R22 on `∑ i, (f i - g i) ^ 2 = 0` to get `f i = g i`.

---

## Traps

- `open minkowskiMatrix` shadows Mathlib's `sq`: `simp only [sq]` uses `minkowskiMatrix.sq : η * η = 1` and
  makes no progress. Write `_root_.sq` (R12) or `pow_two`.
- `simp … at h` leaves products `a * a` and a negated sum `-∑ x, …`; a goal stated with `^ 2` does not match
  it textually. Convert the goal with R12 first, then `linear_combination h` (R13).
- `transpose_mul_minkowskiMatrix_mul_self` takes `Λ` implicitly. Without `(Λ := Λ)` Lean cannot tell which
  Lorentz matrix you mean and the `have` fails to elaborate.
- You write `Λ.1 (Sum.inl 0) (Sum.inl 0)`; the infoview shows `↑Λ (Sum.inl 0) (Sum.inl 0)`. Same term.
- `linarith` needs the nonnegativity of the sum as a hypothesis (R14, R15); it does not know `∑ … ^ 2 ≥ 0`.
- After `rw [h1] at col` the time entry reads `1 ^ 2`; `linarith` normalises `1 ^ 2` to `1` itself.
- `Finset.sum_eq_zero_iff_of_nonneg` is an `↔` with a hypothesis: give the hypothesis as an argument
  (`(fun i _ => sq_nonneg _)`), or `rw` leaves it as an extra goal.
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES). After `refine ⟨?_, …⟩`, close both goals.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation → one entry | `have hij := congrFun (congrFun h i) j` | R1 |
| `Λᵀ η Λ = η` / `Λ η Λᵀ = η` | `transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)` / `mul_minkowskiMatrix_mul_transpose (Λ := Λ)` | R2, R3 |
| evaluate a `(0, 0)` entry of a product with `η` | `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at h` | R4–R11 |
| `(M * N) i l` → `∑ j, M i j * N j l` | `Matrix.mul_apply` | R4 |
| `Mᵀ i j` → `M j i` | `Matrix.transpose_apply` | R5 |
| `η` → `diagonal (Sum.elim 1 (-1))` | `minkowskiMatrix.as_diagonal` | R6 |
| `diagonal c i j` → `if i = j then c i else 0` | `Matrix.diagonal_apply` | R7 |
| sum over `Fin 1 ⊕ Fin d` → time + space | `Fintype.sum_sum_type` | R9 |
| `a ^ 2` → `a * a` (with `open minkowskiMatrix`) | `simp only [_root_.sq]` | R12 |
| equation that is a multiple of `h` | `linear_combination h` | R13 |
| `0 ≤ ∑ i, f i ^ 2` | `Finset.sum_nonneg (fun i _ => sq_nonneg _)` | R14, R15 |
| split `A ∧ (B → ∀ i, C i)` | `refine ⟨?_, fun h1 i => ?_⟩` | R16 |
| `1 ≤ \|a\|` from `1 ≤ a ^ 2` | `(one_le_sq_iff_one_le_abs _).mp (by linarith)` | R17, R18 |
| linear arithmetic | `linarith` | R18 |
| rewrite in two hypotheses | `rw [h] at h₁ h₂` | R19 |
| zero sum of squares → each term zero | `rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h` | R20 |
| use `∀ i ∈ Finset.univ, Q i` at `i` | `h i (Finset.mem_univ _)` | R21 |
| `a ^ 2 = 0` → `a = 0` | `(pow_eq_zero_iff two_ne_zero).mp` | R22 |
| see the state | infoview | |
