# M145 · No-signalling: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices over arbitrary finite
index types, finite sums `∑`, the Kronecker product `⊗ₖ`, the conjugate transpose `ᴴ`, and physlib's
partial trace `Matrix.traceLeft`.

**The physics.** A joint state of Alice (index type `d₁`) and Bob (`d₂`) is a matrix
`M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ`. Alice applies a channel with Kraus operators `K i : Matrix d₁ d₁ ℂ`
(`i : ι`, completeness `∑ i, (K i)ᴴ * K i = 1`) to her half only: `M ↦ ∑ i, (K i ⊗ₖ 1) * M * (K i ⊗ₖ 1)ᴴ`.
Bob's reduced state is the partial trace over Alice, $\mathrm{Tr}_A M$, entry
$(\mathrm{Tr}_A M)_{xy} = \sum_k M_{(k,x),(k,y)}$. The theorem: $\mathrm{Tr}_A$ of the new state equals
$\mathrm{Tr}_A M$, so nothing Alice does locally is visible to Bob.

**The proof idea.** Mirror "a Kraus map preserves the trace" (M144) with `traceLeft` in place of `trace`:
`traceLeft` is linear (milestone 1), and cyclic for operators acting on Alice's factor only,
`((A ⊗ₖ 1) * N).traceLeft = (N * (A ⊗ₖ 1)).traceLeft` (milestone 2). Rotate every term, merge
`(K i)ᴴ ⊗ₖ 1 * (K i ⊗ₖ 1)` into `((K i)ᴴ * K i) ⊗ₖ 1`, pull `M` out of the sum, and use `hK`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{m n : Type}` are any types, used as matrix index types.
  `[Fintype m]` says `m` is finite (needed to sum over it, so for `*` of matrices and for `traceLeft`);
  `[DecidableEq n]` says equality on `n` is decidable (needed for the identity matrix `1` and for
  `if i = j`). In the exercise, `d₁ d₂ ι` have both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix m n ℂ` | complex matrices with rows indexed by `m`, columns by `n`: functions `m → n → ℂ`; `A i j` is an entry |
| `d₁ × d₂` | the type of pairs `(a, b)`; `p.1`, `p.2` are the two components. Alice's index is the first |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how Lean prints `A ⊗ₖ B`, the Kronecker product: `(A ⊗ₖ B) (a, b) (c, e) = A a c * B b e` |
| `Aᴴ` | conjugate transpose: `Aᴴ i j = star (A j i)`, `star` = complex conjugation |
| `1` | the identity matrix of whatever type the context needs: `1 i j = if i = j then 1 else 0` |
| `N.traceLeft` | physlib's partial trace over the FIRST factor: `N.traceLeft x y = ∑ i, N (i, x) (i, y)` |
| `of (fun i₁ j₁ => …)` | `Matrix.of`: a function turned into a matrix; `of f i j = f i j` |
| `∑ x, f x` | sum over every element of a finite type (the finset `Finset.univ`) |
| `∑ x ∈ s, f x` | sum over the elements of the finset `s`; `∑ x, f x` is `∑ x ∈ Finset.univ, f x` |
| `if c then a else b` | needs a `Decidable c` instance; `if i = j` uses `DecidableEq` |
| `x_1`, `x_2`, `i₂`, `x✝` | names Lean invents for bound variables or nameless hypotheses (you cannot type `x✝`) |
| `inst✝ : Fintype d₁` | an instance argument from the statement: `d₁` is finite |

---

## Part 1 · milestone `traceLeft_sum`

Your own lemma, before the spec: `(∑ i, f i).traceLeft = ∑ i, (f i).traceLeft` for
`f : ι → Matrix (d₁ × d₂) (d₁ × d₂) ℂ` (the partial trace is additive). Proof: R1; ONE
`simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]` (R2 and R3 together); then R4.

**R1 · `ext x y`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when
every entry is. Any index types work. Placeholders: `{m n : Type} (A B : Matrix m n ℂ)`.

| Before | After |
|---|---|
| `⊢ A = B` | `x : m, y : n ⊢ A x y = B x y` |

**R2 · `simp only [Matrix.traceLeft]`, then `simp only [Matrix.of_apply]`** changes the **goal**: an entry
of a partial trace becomes a sum over the traced-out index. `traceLeft` is defined as
`Matrix.of fun i₁ j₁ ↦ ∑ i₂, m (i₂, i₁) (i₂, j₁)`; `of_apply : of f i j = f i j`. Use one call,
`simp only [Matrix.traceLeft, Matrix.of_apply]`, and add the other entry lemmas the goal needs (R3, or
R5–R12) to that same call. Placeholders:
`{k m n : Type} [Fintype k] (N : Matrix (k × m) (k × n) ℂ) (x : m) (y : n)`.

| Before | After `simp only [Matrix.traceLeft]` | After `simp only [Matrix.of_apply]` |
|---|---|---|
| `⊢ P (N.traceLeft x y)` | `⊢ P (of (fun i₁ j₁ => ∑ i₂, N (i₂, i₁) (i₂, j₁)) x y)` | `⊢ P (∑ i₂, N (i₂, x) (i₂, y))` |

**R3 · `Matrix.sum_apply`** changes the **goal**. The lemma is `(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j`: an
entry of a sum of matrices is the sum of the entries. Placeholders:
`{m n ι : Type} [Fintype ι] (f : ι → Matrix m n ℂ) (x : m) (y : n)`.

| Before | After |
|---|---|
| `⊢ P ((∑ c, f c) x y)` | `⊢ P (∑ c, f c x y)` |

**R4 · `Finset.sum_comm`** changes the **goal**. The lemma is
`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`. `rw [Finset.sum_comm]` swaps the first double sum it
finds; `exact Finset.sum_comm` closes a goal whose two sides differ only by that swap. Placeholders:
`{m ι : Type} [Fintype m] [Fintype ι] (g : ι → m → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∑ y, g x y)` | `⊢ P (∑ y, ∑ x, g x y)` |

**W1 (same pattern, on the full trace).** `(∑ i, f i).trace = ∑ i, (f i).trace`: after
`simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]` the goal is

```lean-goal
⊢ ∑ x, ∑ c, f c x x = ∑ x, ∑ x_1, f x x_1 x_1
```

and `exact Finset.sum_comm` closes it (the bound-variable names do not matter).

---

## Part 2 · milestone `traceLeft_cyc`

Your own lemma, before the spec: for `A : Matrix d₁ d₁ ℂ` and `N : Matrix (d₁ × d₂) (d₁ × d₂) ℂ`,
`((A ⊗ₖ 1) * N).traceLeft = (N * (A ⊗ₖ 1)).traceLeft` with `1 : Matrix d₂ d₂ ℂ`. In indices both sides
are $\sum_{k,j} A_{kj} N_{(j,x),(k,y)}$. Proof: R1; one `simp only [...]` with R2, R5–R12 (all at once);
R4 on the left side; then R13 twice and R14.

**R5 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle
index, $(AB)_{ik} = \sum_j A_{ij} B_{jk}$. Placeholders: `{l m n : Type} [Fintype m] (A : Matrix l m ℂ)
(B : Matrix m n ℂ) (i : l) (k : n)`. For `d₁ × d₂`-indexed matrices the middle index `j` is a pair.

| Before | After |
|---|---|
| `⊢ P ((A * B) i k)` | `⊢ P (∑ j, A i j * B j k)` |

**R6 · `Fintype.sum_prod_type`** changes the **goal**. The lemma is `∑ x, f x = ∑ x, ∑ y, f (x, y)` for
`x` ranging over a pair type: it splits the pair so that R7 sees explicit pairs `(x, y)`. Placeholders:
`{m n : Type} [Fintype m] [Fintype n] (f : m × n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ p, f p)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R7 · `Matrix.kroneckerMap_apply`** changes the **goal**. The lemma is
`kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2)`; `simp only` also evaluates `f` and the projections
of explicit pairs. Placeholders: `{m n : Type} (A : Matrix m m ℂ) (B : Matrix n n ℂ) (a c : m) (b e : n)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (a, b) (c, e))` | `⊢ P (A a c * B b e)` |

**R8 · `Matrix.one_apply`** changes the **goal**: an entry of the identity becomes an `if`.
The lemma is `1 i j = if i = j then 1 else 0`. Placeholders: `{n : Type} [DecidableEq n] (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

**R9 · `mul_ite`, then `ite_mul`** changes the **goal**: an `if` inside a product moves outside it.
`mul_ite : a * (if c then b else d) = if c then a * b else a * d`; `ite_mul` is the same with the `if` on
the left of `*`. Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After `rw [mul_ite]` | After `rw [ite_mul]` |
|---|---|---|
| `⊢ P ((a * if c then 1 else 0) * b)` | `⊢ P ((if c then a * 1 else a * 0) * b)` | `⊢ P (if c then a * 1 * b else a * 0 * b)` |

**R10 · `mul_one`, `mul_zero`, `zero_mul`** change the **goal**: `a * 1 = a`, `a * 0 = 0`, `0 * a = 0`.
Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if c then a * 1 * b else a * 0 * b)` | `⊢ P (if c then a * b else 0)` |

**R11 · `Finset.sum_ite_eq`, `Finset.sum_ite_eq'`** change the **goal**: a sum whose terms vanish except at
one index collapses. `sum_ite_eq : (∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`, and
`sum_ite_eq'` is the same for `if x = a`. Give `simp` both: which one applies depends on the side of `=`
the summation variable is on. Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (a : n) (f : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, if a = x then f x else 0) (∑ x, if x = a then f x else 0)` | `⊢ P (if a ∈ Finset.univ then f a else 0) (if a ∈ Finset.univ then f a else 0)` |

**R12 · `Finset.mem_univ`, `if_true`** change the **goal**: `a ∈ Finset.univ` is true, and
`if True then t else e = t`. Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (a : n) (t e : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then t else e)` | `⊢ P t` |

**W2 (R8 → R9 → R10 → R11/R12 on `∑ j, 1 i j * v j = v i`).** Each `simp only` call gives:

```lean-goal
⊢ ∑ j, 1 i j * v j = v i
⊢ ∑ x, (if i = x then 1 else 0) * v x = v i
⊢ (∑ x, if i = x then v x else 0) = v i
```

and `simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]` closes the last one. In `traceLeft_cyc`,
the single `simp only` with R2, R5–R12 removes both `1`-factors this way and leaves two double sums;
the left one has its sums in the other order (R4).

**R13 · `refine Finset.sum_congr rfl fun x _ => ?_`** changes the **goal and the context**: two sums over the
same finset are equal if their terms are. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`.
Use it twice for a double sum. Placeholders: `{n : Type} [Fintype n] (f g : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ ∑ x, f x = ∑ x, g x` | `x : n, x✝ : x ∈ Finset.univ ⊢ f x = g x` |

**R14 · `mul_comm`** changes the **goal** (or closes it). The lemma is `a * b = b * a`; `exact mul_comm _ _`
closes `a * b = b * a`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

---

## Part 3 · `no_signalling`

Statement: `(∑ i, (K i ⊗ₖ 1) * M * (K i ⊗ₖ 1)ᴴ).traceLeft = M.traceLeft`. Uses both milestones with `rw` /
`simp_rw` (a lemma you proved is used like a library lemma).

**R15 · `Matrix.mul_assoc`** changes the **goal**. The lemma is `A * B * C = A * (B * C)` (`*` groups to the
left). Use it so that a product has the shape `(A ⊗ₖ 1) * N` that `traceLeft_cyc` expects.
Placeholders: `{n : Type} [Fintype n] (A B C : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (A * B * C)` | `⊢ P (A * (B * C))` |

**R16 · `simp_rw [l]`** changes the **goal**: like `rw [l]`, but it also rewrites under binders such as
`∑ i, …`, where the term mentions the bound variable `i` (`rw` fails there: "Did not find an occurrence
of the pattern"). `simp_rw [l₁, l₂, …]` applies each lemma in turn, as often as it matches.
The bound variable may be renamed (`i` → `x`). Placeholders:
`{n ι : Type} [Fintype n] [Fintype ι] (A C : Matrix n n ℂ) (B : ι → Matrix n n ℂ)`.

| Before | After `simp_rw [Matrix.mul_assoc]` |
|---|---|
| `⊢ P (∑ i, A * B i * C)` | `⊢ P (∑ x, A * (B x * C))` |

**R17 · `Matrix.conjTranspose_kronecker`** changes the **goal**. The lemma is `(A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ`.
Placeholders: `{m n : Type} (A : Matrix m m ℂ) (B : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B)ᴴ` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) Aᴴ Bᴴ)` |

**R18 · `Matrix.conjTranspose_one`** changes the **goal**: `1ᴴ = 1`. Placeholders:
`{n : Type} [DecidableEq n]`, `1 : Matrix n n ℂ`.

| Before | After |
|---|---|
| `⊢ P 1ᴴ` | `⊢ P 1` |

**R19 · `rw [← Matrix.mul_kronecker_mul]`** changes the **goal**. The lemma is
`(A * A') ⊗ₖ (B * B') = A ⊗ₖ B * A' ⊗ₖ B'` (the mixed-product property); right to left it merges a product
of two Kronecker products. Placeholders:
`{m n : Type} [Fintype m] [Fintype n] (A A' : Matrix m m ℂ) (B B' : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B * kroneckerMap (fun x1 x2 => x1 * x2) A' B')` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) (A * A') (B * B'))` |

**R20 · `Matrix.one_mul`** changes the **goal**: `1 * A = A`. After R19 the Bob factor is `1 * 1`.
Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (1 * A)` | `⊢ P A` |

**W3 (R16 with R17 → R18 → R19, then R20).** On `∑ i, (A i ⊗ₖ 1)ᴴ * (B ⊗ₖ 1) = ∑ i, ((A i)ᴴ * B) ⊗ₖ 1`,
one `simp_rw` per lemma gives:

```lean-goal
⊢ ∑ x, kroneckerMap (fun x1 x2 => x1 * x2) (A x)ᴴ 1ᴴ * kroneckerMap (fun x1 x2 => x1 * x2) B 1 = ∑ i, kroneckerMap (fun x1 x2 => x1 * x2) ((A i)ᴴ * B) 1
⊢ ∑ x, kroneckerMap (fun x1 x2 => x1 * x2) (A x)ᴴ 1 * kroneckerMap (fun x1 x2 => x1 * x2) B 1 = ∑ i, kroneckerMap (fun x1 x2 => x1 * x2) ((A i)ᴴ * B) 1
⊢ ∑ x, kroneckerMap (fun x1 x2 => x1 * x2) ((A x)ᴴ * B) (1 * 1) = ∑ i, kroneckerMap (fun x1 x2 => x1 * x2) ((A i)ᴴ * B) 1
```

and `simp_rw [Matrix.one_mul]` closes it.

**R21 · `rw [← Matrix.mul_sum]`** changes the **goal**. The lemma is `A * ∑ i ∈ s, f i = ∑ i ∈ s, A * f i`;
right to left it pulls a common left factor out of a sum. Placeholders:
`{n ι : Type} [Fintype n] [Fintype ι] (A : Matrix n n ℂ) (f : ι → Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, A * f i)` | `⊢ P (A * ∑ a, f a)` |

Mathlib has no lemma `∑ i, f i ⊗ₖ B = (∑ i, f i) ⊗ₖ B`, so the step "`∑ i, ((K i)ᴴ * K i) ⊗ₖ 1 = 1`"
is a `have` you prove entry by entry: R22, `rw [← hK]`, R23, then `simp` with R3, R7, R24.

**R22 · `rw [← Matrix.one_kronecker_one]`** changes the **goal**. The lemma is `1 ⊗ₖ 1 = 1`; right to left
it writes the identity on a pair type as a Kronecker product, so that `rw [← hK]` can then replace Alice's
`1` by `∑ i, (K i)ᴴ * K i`. Placeholders: `{m n : Type} [DecidableEq m] [DecidableEq n]`.

| Before | After |
|---|---|
| `⊢ P 1` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) 1 1)` |

**R23 · `ext ⟨a, b⟩ ⟨c, e⟩`** changes the **goal and the context**: R1 for matrices indexed by pairs, with
each index split into its components by the pattern. Placeholders:
`{m n : Type} (A B : Matrix (m × n) (m × n) ℂ)`.

| Before | After |
|---|---|
| `⊢ A = B` | `a : m, b : n, c : m, e : n ⊢ A (a, b) (c, e) = B (a, b) (c, e)` |

**R24 · `Finset.sum_mul`** changes the **goal**. The lemma is `(∑ i ∈ s, f i) * b = ∑ i ∈ s, f i * b`.
After R3 and R7 the right side of the `have` is `(∑ i, …) * 1 (a, b).2 (c, e).2`; R24 distributes it.
Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℂ) (b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) * b)` | `⊢ P (∑ i, f i * b)` |

**W4 (R23, then `simp`).** For `∑ i, 1 ⊗ₖ f i = 1 ⊗ₖ ∑ i, f i` (the identity on the left this time),
`ext ⟨a, b⟩ ⟨c, e⟩` gives

```lean-goal
⊢ (∑ i, kroneckerMap (fun x1 x2 => x1 * x2) 1 (f i)) (a, b) (c, e) = kroneckerMap (fun x1 x2 => x1 * x2) 1 (∑ i, f i) (a, b) (c, e)
```

and `simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]` closes it. `Finset.mul_sum`
(`b * ∑ i, f i = ∑ i, b * f i`) is the mirror of R24 for a factor on the left.

**R25 · `Matrix.mul_one`** changes the **goal**: `A * 1 = A`. Placeholders:
`{n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (A * 1)` | `⊢ P A` |

---

## Traps

- `⊗ₖ` is printed as `kroneckerMap (fun x1 x2 => x1 * x2) A B`. You may still type `A ⊗ₖ B` (it needs
  `open scoped Kronecker`, which the file has).
- `traceLeft_cyc` needs `N`'s first operator on the LEFT: `(A ⊗ₖ 1) * N`. In
  `(K i ⊗ₖ 1) * M * (K i ⊗ₖ 1)ᴴ` the product groups as `((K i ⊗ₖ 1) * M) * …`, so regroup with R15
  first; after the rotation regroup again, so that `(K i ⊗ₖ 1)ᴴ * (K i ⊗ₖ 1)` sits together for R17–R19.
- `rw` cannot rewrite inside `∑ i, …` when the term contains `i`: use `simp_rw` (R16).
- In `traceLeft_sum`, give R2 and R3 to ONE `simp only [...]`. With `simp only [Matrix.traceLeft,
  Matrix.of_apply]` first and `Matrix.sum_apply` afterwards, the right side keeps an unevaluated
  `of (fun i₁ j₁ => …) x y`: `of_apply` only fires after `sum_apply` has exposed it, and then
  `rw [Finset.sum_comm]` leaves an unsolved goal.
- In `traceLeft_cyc`, give all of R2, R5–R12 to ONE `simp only [...]`. In separate calls the order
  matters: R7 needs the explicit pairs that R6 creates, and some projections `(x, y).2` stay unreduced
  until R8 turns the `1`-entries into `if`s.
- `rw [← hK]` replaces every `1` of type `Matrix d₁ d₁ ℂ` by `∑ i, (K i)ᴴ * K i`. Do R22 first so that the
  goal's `1` (of type `Matrix (d₁ × d₂) (d₁ × d₂) ℂ`) becomes `1 ⊗ₖ 1` and Alice's `1` appears.
- The milestones are your own lemmas: put them after `namespace M145` and before the spec, outside the
  `BEGIN SPEC`/`END SPEC` regions, with their own type arguments (`{d₁ d₂ : Type} [Fintype d₁] …`).
- `have h : T` with no `:= …` makes `T` your next goal (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation → one entry | `ext x y` | R1 |
| … with pair indices | `ext ⟨a, b⟩ ⟨c, e⟩` | R23 |
| entry of `N.traceLeft` → `∑ i, N (i, x) (i, y)` | `simp only [Matrix.traceLeft, Matrix.of_apply]` | R2 |
| entry of a sum of matrices | `Matrix.sum_apply` | R3 |
| swap two sums | `rw [Finset.sum_comm]` / `exact Finset.sum_comm` | R4 |
| entry of a product | `Matrix.mul_apply` | R5 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R6 |
| entry of `A ⊗ₖ B` | `Matrix.kroneckerMap_apply` | R7 |
| entry of `1` | `Matrix.one_apply` | R8 |
| `if` out of a product, clean up | `mul_ite, ite_mul, mul_one, mul_zero, zero_mul` | R9, R10 |
| collapse `∑ x, if a = x then f x else 0` | `Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true` | R11, R12 |
| term-by-term equality of sums | `refine Finset.sum_congr rfl fun x _ => ?_` | R13 |
| `a * b = b * a` | `mul_comm` | R14 |
| regroup a matrix product | `Matrix.mul_assoc` | R15 |
| rewrite under `∑ i, …` | `simp_rw [l₁, l₂]` | R16 |
| `(A ⊗ₖ B)ᴴ`, `1ᴴ` | `Matrix.conjTranspose_kronecker`, `Matrix.conjTranspose_one` | R17, R18 |
| merge `A ⊗ₖ B * A' ⊗ₖ B'` | `← Matrix.mul_kronecker_mul` | R19 |
| `1 * A`, `A * 1` | `Matrix.one_mul`, `Matrix.mul_one` | R20, R25 |
| `∑ i, A * f i → A * ∑ i, f i` | `rw [← Matrix.mul_sum]` | R21 |
| `1` on a pair type → `1 ⊗ₖ 1` | `rw [← Matrix.one_kronecker_one]` | R22 |
| `(∑ i, f i) * b` → `∑ i, f i * b` | `Finset.sum_mul` | R24 |
| see the state | infoview | |
