# H105 · Orthochronous transformations are closed under products: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). Medium M179 (the `(0,0)` entry of `Λᵀ η Λ = η`) is the
same computation as milestones 1 and 2 here, but it is not required. **New here:** physlib's Lorentz
group `𝓛 d` and Minkowski matrix `η`, Mathlib's matrices indexed by `Fin 1 ⊕ Fin d`, finite sums `∑`,
Cauchy–Schwarz for finite sums, `generalize`, `linear_combination` and `nlinarith`.

**The mathematics.** Index time by `0` and space by `i = 1…d`. A real `(1+d)×(1+d)` matrix `Λ` is a
Lorentz transformation when `Λᵀ η Λ = η` (equivalently `Λ η Λᵀ = η`), with `η = diag(1, -1, …, -1)`. It
is orthochronous when `Λ⁰₀ ≥ 0`. Write `a = Λ⁰₀`, `b = Λ'⁰₀`, `s = ∑ᵢ Λ⁰ᵢ Λ'ⁱ₀`,
`A = ∑ᵢ (Λ⁰ᵢ)²` (row 0 of `Λ`), `B = ∑ᵢ (Λ'ⁱ₀)²` (column 0 of `Λ'`). Then

- `(ΛΛ')⁰₀ = a b + s` (milestone 3, `mul_time`);
- `a² = 1 + A` from the `(0,0)` entry of `Λ η Λᵀ = η` (milestone 2, `row_sq`), and `b² = 1 + B` from the
  `(0,0)` entry of `Λ'ᵀ η Λ' = η` (milestone 1, `col_sq`);
- Cauchy–Schwarz: `s² ≤ A B = (a² − 1)(b² − 1) < a² b²`, so `|s| < a b` and `a b + s > 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`/`simp`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of the expression" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal. Many entries here change a *hypothesis* `h` (`rw [l] at h`,
  `simp [...] at h`) or add one (`have h := lemma`); in the guide a hypothesis `k : … → G` then consumes it.
- Placeholders are written as Lean binders. `{n : Type}` is any type; a bracket such as `[Fintype n]` is a
  requirement on `n` (a *type class*: here, that `n` is finite, so `∑ j : n` makes sense). `Fin k`,
  `Fin 1 ⊕ Fin d` meet `[Fintype _]` and `[DecidableEq _]`; `ℝ` meets every bracket on values used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 1 ⊕ Fin d` | the index type of spacetime: `Sum.inl 0` is time, `Sum.inr i` (`i : Fin d`) is space axis `i` |
| `Matrix m n ℝ` | real matrices with rows indexed by `m`, columns by `n`; `M i j` is the entry, a function application |
| `𝓛 d` | `LorentzGroup d`: the *set* of matrices `Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ` that preserve `η` |
| `Λ : ↑(𝓛 d)` | `Λ` is an element of that set (a *subtype*: a matrix bundled with the proof that it is Lorentz) |
| `↑Λ` | the underlying matrix of `Λ`; you write it `Λ.1`. `↑Λ (Sum.inl 0) (Sum.inl 0)` is `Λ⁰₀` |
| `↑Λ (Sum.inl 0) (Sum.inr i)`, `↑Λ (Sum.inr i) (Sum.inl 0)` | `Λ⁰ᵢ` (row 0) and `Λⁱ₀` (column 0) |
| `↑(Λ * Λ')` | the matrix of the group product; R15 rewrites it to `↑Λ * ↑Λ'` |
| `η` | `minkowskiMatrix`, the metric `diag(1, -1, …, -1)` (needs `open minkowskiMatrix`) |
| `Mᵀ`, `(↑Λ)ᵀ` | transpose: `Mᵀ i j = M j i` (R6) |
| `diagonal v` | the diagonal matrix with `v i` at `(i, i)`, `0` elsewhere (R8) |
| `Sum.elim f g` | the function on `α ⊕ β` that is `f` on `Sum.inl _` and `g` on `Sum.inr _` (R11) |
| `1`, `-1` as functions | the constant functions `fun _ => 1`, `fun _ => -1` (`Pi.one_apply`, `Pi.neg_apply`) |
| `∑ x, f x` | the sum of `f x` over every `x` of a finite type (`Finset.univ`) |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι` |
| `Finset.univ` | the finite set of all elements of a finite type |
| `a₁`, `a₂`, `x` under `∑` | bound variables named by a lemma (R4) or by `simp`; the name does not matter |
| `IsOrthochronous Λ` | by definition `0 ≤ ↑Λ (Sum.inl 0) (Sum.inl 0)` (R16) |
| `inst✝ : Fintype n` | an anonymous type-class instance from a `[Fintype n]` binder |
| `a✝ : i ∈ s` | an anonymous hypothesis, introduced with `intro i _` (R19) |

---

## Part 1 · `col_sq` (milestone 1)

Statement: `Λ⁰₀² = 1 + ∑ᵢ (Λⁱ₀)²`. Take the `(0,0)` entry of `Λᵀ η Λ = η`, let `simp` evaluate both sides,
then match it against the goal.

### A matrix identity → one scalar equation

**R1 · `have h := transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)`** changes the **context**. The lemma
is `LorentzGroup.transpose_mul_minkowskiMatrix_mul_self : (↑Λ)ᵀ * η * ↑Λ = η`, with `Λ` implicit, so you
name it: `(Λ := Λ)`. Placeholders: `{d : ℕ} (Λ : LorentzGroup d)`.

| Before | After |
|---|---|
| `⊢ G` | `h : (↑Λ)ᵀ * η * ↑Λ = η ⊢ G` |

**R2 · `congrFun (congrFun h i) j`** changes the **context**. `congrFun : f = g → ∀ a, f a = g a`. A matrix
is a function of the row, returning a function of the column, so two applications give one entry.
Placeholders: `{n : Type} (M N : Matrix n n ℝ) (h : M = N) (i j : n)`.

| Before | After `have hij := congrFun (congrFun h i) j` |
|---|---|
| `h : M = N ⊢ G` | `hij : M i j = N i j ⊢ G` |

### Evaluating the entry

You do not apply R3–R11 one by one: `simp [Matrix.mul_apply, Fintype.sum_sum_type,
minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at h` (R3, R4, R7, R8) applies all of them: R5, R6,
R9–R11 are `simp` lemmas already (`simp` does R5 with `Finset.univ_unique`, `Finset.sum_singleton`), and
naming them again only earns an "unused simp argument" warning. `simp` also uses `mul_neg`, `neg_mul`
(`a * -b = -(a * b)`, `-a * b = -(a * b)`) and `Finset.sum_neg_distrib` (`∑ -f = -∑ f`), which is where the
`-∑` below comes from. The entries are listed so you can read what `simp` did, and fix it when it stops early.
R3–R5 and R10 are shown on the goal (`rw [l]`); in the milestones they act on `h` (`rw [l] at h` or
`simp [l] at h`), with the same before and after.

**R3 · `rw [Matrix.mul_apply]`** changes the **goal** (with `at h`: the **context**): an entry of a
product becomes a sum over the middle index, `(M N)ᵢₗ = ∑ⱼ Mᵢⱼ Nⱼₗ`. Placeholders:
`{n : Type} [Fintype n] (M N : Matrix n n ℝ) (i l : n)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i l)` | `⊢ P (∑ j, M i j * N j l)` |

**R4 · `rw [Fintype.sum_sum_type]`** changes the **goal** (with `at h`: the **context**). The lemma is
`∑ x, f x = ∑ a₁, f (Sum.inl a₁) + ∑ a₂, f (Sum.inr a₂)`: a sum over `Fin 1 ⊕ Fin d` splits into the time
part and the space part. Placeholders: `{d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ a₁, f (Sum.inl a₁) + ∑ a₂, f (Sum.inr a₂))` |

**R5 · `rw [Fin.sum_univ_one]`** changes the **goal** (with `at h`: the **context**). The lemma is `∑ i : Fin 1, f i = f 0`: the
time part has one term. `simp` gets the same result with `Finset.univ_unique` and `Finset.sum_singleton`.
Placeholders: `(f : Fin 1 → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0)` |

**R6 · `rw [Matrix.transpose_apply] at h`** changes the **context**: `Mᵀ i j = M j i`.
Placeholders: `{n : Type} (M : Matrix n n ℝ) (i j : n)`.

| Before | After |
|---|---|
| `h : P (Mᵀ i j) ⊢ G` | `h : P (M j i) ⊢ G` |

**R7 · `rw [minkowskiMatrix.as_diagonal] at h`** changes the **context**. The lemma is
`η = diagonal (Sum.elim 1 (-1))`: `1` on the time index, `-1` on each space index. Placeholders:
`{d : ℕ}` (the size of `η`). For the right-hand side `η (Sum.inl 0) (Sum.inl 0)`, `simp` may instead use
physlib's `minkowskiMatrix.inl_0_inl_0 : η (Sum.inl 0) (Sum.inl 0) = 1`; the result is the same `1`.

| Before | After |
|---|---|
| `h : P η ⊢ G` | `h : P (diagonal (Sum.elim 1 (-1))) ⊢ G` |

**R8 · `rw [Matrix.diagonal_apply] at h`** changes the **context**. The lemma is
`diagonal v i j = if i = j then v i else 0`. Placeholders: `{n : Type} [DecidableEq n] (v : n → ℝ) (i j : n)`
(`DecidableEq n`: equality of indices can be decided, so the `if` makes sense).

| Before | After |
|---|---|
| `h : P (diagonal v i j) ⊢ G` | `h : P (if i = j then v i else 0) ⊢ G` |

**R9 · `rw [mul_ite] at h`, then `rw [mul_zero] at h`** change the **context**. `mul_ite :
c * (if p then x else y) = if p then c * x else c * y` and `mul_zero : c * 0 = 0`. They put the sum's
terms into the shape R10 needs. Placeholders: `(c x : ℝ) (p : Prop) [Decidable p]`.

| Before | After `rw [mul_ite] at h` | After `rw [mul_zero] at h` |
|---|---|---|
| `h : P (c * if p then x else 0) ⊢ G` | `h : P (if p then c * x else c * 0) ⊢ G` | `h : P (if p then c * x else 0) ⊢ G` |

**R10 · `rw [Finset.sum_ite_eq']`, then `simp only [Finset.mem_univ, if_true]`** change the **goal**
(with `at h`: the **context**). `Finset.sum_ite_eq' : (∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`: of all
terms only `x = a` survives. Here `s = Finset.univ`, so `a ∈ s` is true (`Finset.mem_univ`). This is how the
`diagonal` disappears from a product with `η`. Placeholders:
`{n : Type} [Fintype n] [DecidableEq n] (a : n) (b : n → ℝ)`.

| Before | After `rw` | After `simp only` |
|---|---|---|
| `⊢ P (∑ x, if x = a then b x else 0)` | `⊢ P (if a ∈ Finset.univ then b a else 0)` | `⊢ P (b a)` |

**R11 · `simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Pi.neg_apply] at h`** changes the
**context**: the diagonal of `η` evaluated. `Sum.elim_inl : Sum.elim f g (Sum.inl x) = f x`, `Sum.elim_inr`
likewise for `g`; `Pi.one_apply : (1 : α → ℝ) x = 1`, `Pi.neg_apply : (-f) x = -f x`. Placeholders:
`{d : ℕ} (i : Fin d)`, `P : ℝ → ℝ → Prop`.

| Before | After |
|---|---|
| `h : P (Sum.elim 1 (-1) (Sum.inl 0)) (Sum.elim 1 (-1) (Sum.inr i)) ⊢ G` | `h : P 1 (-1) ⊢ G` |

After all of these, the `(0,0)` entry of `Λᵀ η Λ = η` reads (in the infoview; `x` is a bound variable)

```text
hc : ↑Λ (Sum.inl 0) (Sum.inl 0) * ↑Λ (Sum.inl 0) (Sum.inl 0) +
       -∑ x, ↑Λ (Sum.inr x) (Sum.inl 0) * ↑Λ (Sum.inr x) (Sum.inl 0) = 1
```

that is, `(Λ⁰₀)² − ∑ᵢ (Λⁱ₀)² = 1`, written with `*`, not `^ 2`.

### Closing the milestone equation

**R12 · `simp only [_root_.sq]`** changes the **goal**. `sq : a ^ 2 = a * a`, so every `^ 2`, also under a
`∑`, becomes a product, the form `simp` left in `h`. With `open minkowskiMatrix`, bare `sq` is ambiguous:
it also names `minkowskiMatrix.sq : η * η = 1`. `_root_.sq` (or `pow_two`) names the algebra lemma.
Placeholders: `{n : Type} [Fintype n] (a : ℝ) (f : n → ℝ)`, `P : ℝ → ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P (a ^ 2) (∑ i, f i ^ 2)` | `⊢ P (a * a) (∑ x, f x * f x)` |

**R13 · `linear_combination h`** **closes** an equation `L = R` when `L − R` equals `h.lhs − h.rhs` as a
polynomial identity (sums `∑ …` count as unknowns). `linear_combination c * h` scales `h` by `c`.
Placeholders: `(a s t : ℝ)`.

| Before | After |
|---|---|
| `h : a * a + -s = t ⊢ a * a = t + s` | closed |

### Worked combination (W1, an orthogonal matrix, not a Lorentz one)

**W1.** `M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ` with `hM : Mᵀ * M = 1`. R2 on `hM`, then
`simp [Matrix.mul_apply, Fintype.sum_sum_type] at h` (R3–R6, and `1 i i = 1`) turns `h` into

```text
h : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 0) (Sum.inl 0) +
      ∑ a₂, M (Sum.inr a₂) (Sum.inl 0) * M (Sum.inr a₂) (Sum.inl 0) = 1
```

R12 makes the goal match it, and R13 closes:

```lean-goal
⊢ M (Sum.inl 0) (Sum.inl 0) ^ 2 + ∑ i, M (Sum.inr i) (Sum.inl 0) ^ 2 = 1
⊢ M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 0) (Sum.inl 0) + ∑ x, M (Sum.inr x) (Sum.inl 0) * M (Sum.inr x) (Sum.inl 0) = 1
```

**W2.** `(η * η) (Sum.inr i) (Sum.inr i) = 1` closes with one
`simp [Matrix.mul_apply, as_diagonal, Matrix.diagonal_apply]` (R3, R7, R8–R11): `(-1) * (-1) = 1`.

---

## Part 2 · `row_sq` (milestone 2)

Statement: `Λ⁰₀² = 1 + ∑ᵢ (Λ⁰ᵢ)²` (row 0 instead of column 0). The same steps as Part 1, starting from the
other form of the Lorentz condition.

**R14 · `have h := mul_minkowskiMatrix_mul_transpose (Λ := Λ)`** changes the **context**. The lemma is
`LorentzGroup.mul_minkowskiMatrix_mul_transpose : ↑Λ * η * (↑Λ)ᵀ = η`. Its `(0,0)` entry involves row 0
of `Λ`; R1's involves column 0. Placeholders: `{d : ℕ} (Λ : LorentzGroup d)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ↑Λ * η * (↑Λ)ᵀ = η ⊢ G` |

Then R2, the same `simp … at h` (R3–R11), R12, R13.

---

## Part 3 · `mul_time` (milestone 3)

Statement: `(ΛΛ')⁰₀ = Λ⁰₀ Λ'⁰₀ + ∑ᵢ Λ⁰ᵢ Λ'ⁱ₀`. Turn the group product into a matrix product, expand
the entry, split the sum.

**R15 · `rw [lorentzGroupIsGroup_mul_coe]`** changes the **goal**. The lemma is
`lorentzGroupIsGroup_mul_coe : ↑(A * B) = ↑A * ↑B`: the matrix of a product in `𝓛 d` is the matrix
product. Placeholders: `{d : ℕ} (A B : LorentzGroup d)`,
`P : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P ↑(A * B)` | `⊢ P (↑A * ↑B)` |

Then R3, R4, R5: one `simp [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]` does
all of it (R5 is automatic). With `rw` instead, list R15, R3, R4, R5 in that order.

**W3.** Another entry of a product, `↑(A * B) (Sum.inr i) (Sum.inl 0)`, closes with that same `simp`.

---

## Part 4 · `time_orientation_mul`

Statement: `IsOrthochronous Λ → IsOrthochronous Λ' → IsOrthochronous (Λ * Λ')`. Unfold, rewrite with
milestone 3, collect the facts (milestones 1, 2, Cauchy–Schwarz, two sums of squares `≥ 0`), turn the five
big terms into variables, then `nlinarith`.

**R16 · `unfold IsOrthochronous at *`** changes the **goal and the context**: every `IsOrthochronous X`
becomes its definition `0 ≤ ↑X (Sum.inl 0) (Sum.inl 0)`. Placeholders: `{d : ℕ} (Λ Λ' : LorentzGroup d)`.

| Before | After |
|---|---|
| `h : IsOrthochronous Λ ⊢ IsOrthochronous Λ'` | `h : 0 ≤ ↑Λ (Sum.inl 0) (Sum.inl 0) ⊢ 0 ≤ ↑Λ' (Sum.inl 0) (Sum.inl 0)` |

Then `rw [mul_time]` (milestone 3) and `have ha := row_sq Λ`, `have hb := col_sq Λ'` (milestones as
facts; TACTIC_STATES, "Adding facts").

**R17 · `have cs := Finset.sum_mul_sq_le_sq_mul_sq s f g`** changes the **context**: it adds
Cauchy–Schwarz, `cs : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2`. Placeholders:
`{ι : Type} (s : Finset ι) (f g : ι → ℝ)` (the lemma holds in any ordered commutative semiring; `ℝ` is
one). The guide shows the statement as a goal that the lemma closes. With `s := Finset.univ` and `fun`
arguments the sums are `∑ i, …` with the `fun` applied (second row), exactly how the terms look in the
exercise's goal (`have cs` prints them that way too).

| Goal | After `exact Finset.sum_mul_sq_le_sq_mul_sq …` |
|---|---|
| `⊢ (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2` | closed (`s f g`) |
| `⊢ (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i, v i ^ 2` | closed (`Finset.univ (fun i => u i) (fun i => v i)`) |

**R18 · `have h := sq_nonneg a`** changes the **context**: `sq_nonneg a : 0 ≤ a ^ 2`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ a ^ 2 ⊢ G` |

**R19 · `apply Finset.sum_nonneg`** changes the **goal**. `Finset.sum_nonneg : (∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i`.
After `intro i _`, R18 finishes. As one term: `Finset.sum_nonneg (fun i _ => sq_nonneg _)`. You need these
facts (`0 ≤ A`, `0 ≤ B`) because `nlinarith` cannot see inside a sum. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ)`.

| Before | After `apply Finset.sum_nonneg` | After `intro i _` |
|---|---|---|
| `⊢ 0 ≤ ∑ i ∈ s, f i ^ 2` | `⊢ ∀ i ∈ s, 0 ≤ f i ^ 2` | `i : ι, a✝ : i ∈ s ⊢ 0 ≤ f i ^ 2` |

**R20 · `generalize e = x at *`** changes the **goal and the context**: every copy of the term `e`, in the
goal and in all hypotheses, is replaced by a new variable `x : ℝ`, forgetting what `x` was. Then the facts
are plain polynomial (in)equalities in a few unknowns. Write `e` exactly as it is printed (up to `↑Λ` =
`Λ.1`). Placeholders: `{n : ℕ} (f : Fin n → ℝ)`, `P : ℝ → Prop`.

| Before | After `generalize ∑ i, f i = x at *` |
|---|---|
| `⊢ P (∑ i, f i)` (with `h : 0 ≤ ∑ i, f i`) | `x : ℝ, h : 0 ≤ x ⊢ P x` |

Generalize the *largest* terms first only when one contains another; here the five terms (`a`, `b`, `s`,
`A`, `B`) are disjoint, so any order works.

**R21 · `nlinarith [t₁, …]`** **closes** an inequality that follows from the hypotheses by multiplying pairs of
them (and the extra facts `tᵢ` you list) and then adding them up with nonnegative coefficients
(`linarith`). Give it the products it will not find by itself, e.g. `nlinarith [mul_nonneg h h']`.
For a two-step argument, prove the intermediate inequality first with its own `nlinarith`
(`have key : … := by nlinarith`). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hy : 0 ≤ y, h : x ^ 2 ≤ y ^ 2 ⊢ x ≤ y` | closed |
| `hx : 0 ≤ x, hy : 0 ≤ y ⊢ 0 ≤ x * y + x` | closed by `nlinarith [mul_nonneg hx hy]` |

**R22 · `mul_nonneg`** changes the **context** (or serves as a hint term for R21):
`mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`. Placeholders: `(a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)`.

| Before | After `have hab := mul_nonneg ha hb` |
|---|---|
| `ha : 0 ≤ a, hb : 0 ≤ b ⊢ G` | `hab : 0 ≤ a * b ⊢ G` |

### Worked combination (W4: Cauchy–Schwarz gives an AM–GM bound)

**W4.** `∑ fᵢ gᵢ ≤ (∑ fᵢ² + ∑ gᵢ²) / 2` for `f g : Fin n → ℝ`: R17 for `cs`, R19 for `0 ≤ A`, `0 ≤ B`, then
three `generalize`s (R20), then `nlinarith [sq_nonneg (A - B)]` (R21). The goals along the way:

```lean-goal
⊢ ∑ i, f i * g i ≤ (∑ i, f i ^ 2 + ∑ i, g i ^ 2) / 2
⊢ s ≤ (∑ i, f i ^ 2 + ∑ i, g i ^ 2) / 2
⊢ s ≤ (A + ∑ i, g i ^ 2) / 2
⊢ s ≤ (A + B) / 2
```

| Before `nlinarith` | After |
|---|---|
| `hA : 0 ≤ A, hB : 0 ≤ B, cs : s ^ 2 ≤ A * B ⊢ s ≤ (A + B) / 2` | closed |

---

## Traps

- With `open minkowskiMatrix`, bare `sq` is ambiguous (`minkowskiMatrix.sq : η * η = 1`): write
  `_root_.sq` or `pow_two` (R12). `sq_nonneg` is not affected.
- `simp … at h` leaves `x * x`, never `x ^ 2`; the milestones are stated with `^ 2`. `linear_combination`
  identifies `a ^ 2` with `a * a` outside a sum, but to it `∑ i, f i ^ 2` and `∑ x, f x * f x` are two
  different unknowns, so without R12 it fails with `ring failed`. The bound variable's name does not matter.
- `transpose_mul_minkowskiMatrix_mul_self` takes `Λ` implicitly: `transpose_mul_minkowskiMatrix_mul_self Λ`
  is an error; write `(Λ := Λ)` (R1, R14).
- Column vs row: `Λᵀ η Λ = η` (R1) gives `Λ⁰₀² = 1 + ∑ (Λⁱ₀)²` (column 0); `Λ η Λᵀ = η` (R14) gives row 0. The
  product `(ΛΛ')⁰₀` pairs row 0 of `Λ` with column 0 of `Λ'`, so use `row_sq Λ` and `col_sq Λ'`.
- `nlinarith` treats each `∑ i, …` as one unknown. `generalize` (R20) makes that explicit and the
  hypotheses readable; do it after all the `have`s that mention the terms, or the later `have`s still
  speak about the old terms.
- `generalize … at *` also rewrites the hypotheses `h`, `h'`, so they become `0 ≤ a`, `0 ≤ b`.
- One `nlinarith` for the whole inequality is too much: first `have key : s ^ 2 < (a * b) ^ 2 := by nlinarith`,
  then `nlinarith [mul_nonneg h h']` (the step `s² < (ab)²`, `ab ≥ 0 ⇒ 0 ≤ ab + s`).
- `exact?`, `apply?`, `hint` and the physlib lemmas that already state the result
  (`LorentzGroup.isOrthochronous_mul`, `toVector`, …) are BANNED.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| Lorentz condition, column form / row form | `have h := transpose_mul_minkowskiMatrix_mul_self (Λ := Λ)` / `mul_minkowskiMatrix_mul_transpose (Λ := Λ)` | R1, R14 |
| one entry of a matrix equation | `have hc := congrFun (congrFun h i) j` | R2 |
| evaluate the entry | `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc` | R3–R11 |
| `x ^ 2 → x * x` | `simp only [_root_.sq]` | R12 |
| goal = hypothesis up to ring algebra | `linear_combination hc` | R13 |
| matrix of a group product | `lorentzGroupIsGroup_mul_coe` (with R3–R5 in one `simp`) | R15 |
| orthochronous → inequality | `unfold IsOrthochronous at *` | R16 |
| Cauchy–Schwarz | `have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => …) (fun i => …)` | R17 |
| `0 ≤ ∑ i, f i ^ 2` | `Finset.sum_nonneg (fun i _ => sq_nonneg _)` | R18, R19 |
| big term → variable | `generalize e = x at *` | R20 |
| polynomial inequality | `nlinarith [mul_nonneg h h']` | R21, R22 |
| see the state | infoview | |
