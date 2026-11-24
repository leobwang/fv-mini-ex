# M166 · Zero-field transfer matrix: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have`, `induction … with`, `rw`, `simp`, `exact`.
**New here:** Mathlib's 2×2 matrices (`Matrix (Fin 2) (Fin 2) ℝ`, literals `!![…]`, products, powers
`M ^ n`, the trace), the real functions `Real.exp`, `Real.cosh`, `Real.sinh`, and the tactics `ext`,
`fin_cases`, `ring`.

**The physics in one line.** For an Ising ring of `n` spins with coupling `J` at inverse temperature `β`,
`K = βJ`, the partition function is `Z = tr Tⁿ` with transfer matrix `T = [[e^K, e^{-K}], [e^{-K}, e^K]]`.
`T` has eigenvalues `c = e^K + e^{-K} = 2 cosh K` (eigenvector `(1, 1)`) and `s = e^K - e^{-K} = 2 sinh K`
(eigenvector `(1, -1)`), so `tr Tⁿ = cⁿ + sⁿ`. The Lean proof avoids eigenvectors: it proves the closed form

  `Tⁿ = [[(cⁿ + sⁿ)/2, (cⁿ - sⁿ)/2], [(cⁿ - sⁿ)/2, (cⁿ + sⁿ)/2]]`

by induction on `n`, entry by entry, and reads the trace off it.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℝ` | 2×2 matrices with real entries. Rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `M * N`, `M ^ n` | matrix product, `n`-th matrix power (`M ^ 0 = 1`, `M ^ (n + 1) = M ^ n * M`) |
| `1` (a matrix) | the identity matrix: `1 i i = 1`, `1 i j = 0` for `i ≠ j` |
| `Matrix.trace A`, printed `A.trace` | the trace `A 0 0 + A 1 1` |
| `∑ j, f j` | the sum of `f j` over all `j : Fin 2` |
| `Real.exp x`, `Real.cosh x`, `Real.sinh x` | `eˣ`, `(eˣ + e⁻ˣ)/2`, `(eˣ - e⁻ˣ)/2` |
| `↑n` | the natural number `n` cast into `ℝ` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases`: `⟨0, ⋯⟩` is the element `0` of `Fin 2` together with a hidden proof `⋯` of `0 < 2` |
| `case zero`, `case succ`, `ih : …` | the `n = 0` and `n + 1` goals of the induction; `ih` is the closed form at `n` |
| `case succ.«0».«1»` | the `n + 1` case of the induction, entry (0, 1) |
| `noncomputable def T0` | a definition Lean can reason about but not run (real numbers cannot be computed exactly); no effect on proofs |
| `-K`, `2 * Real.cosh K` | negation and product of real numbers |

---

## Part 1 · `trace_pow`

Statement: for every real `K` and natural `n`, `Matrix.trace (T0 K ^ n) = (2 * Real.cosh K) ^ n +
(2 * Real.sinh K) ^ n`, where `T0 K = !![Real.exp K, Real.exp (-K); Real.exp (-K), Real.exp K]`.

Do not induct on the trace: `tr Tⁿ⁺¹` is not a function of `tr Tⁿ`. Prove the closed form of the whole
matrix `T0 K ^ n` as a milestone `key`, then take its trace.

### The milestone and the induction

**R1 · `have key : M ^ n = C := by …`** changes the **context**: it adds `key`, and the goal is unchanged.
Once `key` is proved, `rw [key]` replaces the power by the closed form. Placeholders:
`{α : Type} [Monoid α] (M C : α) (n : ℕ)`; a `Monoid` has `*`, `1` and `^ n`, and `Matrix (Fin 2) (Fin 2) ℝ`
is one. Indent the `by` block further than `have`.

| Before | After `have key` | After `rw [key]` |
|---|---|---|
| `⊢ P (M ^ n)` | `key : M ^ n = C ⊢ P (M ^ n)` | `⊢ P C` |

**R2 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list**: one goal for `n = 0`,
one for `n + 1` with the induction hypothesis `ih` in the context. Placeholders: `(P : ℕ → Prop)`. Do the
induction *inside* `key`, so that `ih` is the closed form at `n`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

### Matrix equation → entries

**R3 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`, which says two matrices are
equal when every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R4 · `fin_cases i`** changes the **goal list and the context**. `i` leaves the context, and there is one goal
for each value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`. `fin_cases i <;> fin_cases j` gives all four
entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

### The base case `n = 0` (plain `simp` does all of R5–R8 and R11)

**R5 · `pow_zero`** changes the **goal**. The lemma is `a ^ 0 = 1`; for a matrix the `1` is the identity
matrix, for a real number it is the number `1`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (M ^ 0)` | `⊢ P 1` |

**R6 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix
become `1` on the diagonal and `0` elsewhere. Placeholders: `(1 : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R7 · `add_self_div_two`** changes the **goal**. The lemma is `(a + a) / 2 = a`: with `n = 0` the diagonal
entry `(c⁰ + s⁰)/2` becomes `(1 + 1)/2` and then `1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((a + a) / 2)` | `⊢ P a` |

**R8 · `sub_self`, then `zero_div`** change the **goal**. The lemmas are `a - a = 0` and `0 / b = 0`: the
off-diagonal entry `(c⁰ - s⁰)/2` becomes `0`. Placeholders: `(a b : ℝ)`.

| Before | After `rw [sub_self]` | After `rw [zero_div]` |
|---|---|---|
| `⊢ P ((a - a) / b)` | `⊢ P (0 / b)` | `⊢ P 0` |

### The step `n → n + 1`

**R9 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`. `rw` fixes
`a` and `n` at the first match and rewrites only that instance: on `T0 K ^ (n + 1) = !![… c ^ (n + 1) …]` it
rewrites the matrix power and leaves the real powers alone. Then `rw [ih]` replaces `T0 K ^ n` by the closed
form. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (n : ℕ)`, `P` of two arguments.

| Before | After |
|---|---|
| `⊢ P (M ^ (n + 1)) (x ^ (n + 1))` | `⊢ P (M ^ n * M) (x ^ (n + 1))` |

To expand the real powers `c ^ (n + 1) = c ^ n * c` as well, pass `pow_succ` to `simp`, which rewrites every
instance.

**R10 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. In the exercise the
name is `T0`. Placeholders: `D` defined by `noncomputable def D (x : ℝ) := !![x, 0; 0, Real.exp x]`.

| Before | After |
|---|---|
| `⊢ P (D x)` | `⊢ P !![x, 0; 0, Real.exp x]` |

**R11 · entry of a literal** changes the **goal**. `simp` uses `Matrix.of_apply` and `Matrix.cons_val_…` for
this by itself. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

**R12 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. `simp` does **not** do this by itself; name it. Placeholders:
`{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a commutative `+` with `0`, as `ℝ` does),
`(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R13 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Name it.
Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R14 · `Real.cosh_eq`** changes the **goal**. The lemma is `cosh x = (exp x + exp (-x)) / 2`. Placeholders:
`(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cosh x)` | `⊢ P ((Real.exp x + Real.exp (-x)) / 2)` |

**R15 · `Real.sinh_eq`** changes the **goal**. The lemma is `sinh x = (exp x - exp (-x)) / 2`. Placeholders:
`(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.sinh x)` | `⊢ P ((Real.exp x - Real.exp (-x)) / 2)` |

Why unfold `cosh` and `sinh`: the entries of `T0 K` are written with `Real.exp`, the closed form with
`cosh`/`sinh`. Only after R14, R15 are both sides polynomials in the same two unknowns `Real.exp K` and
`Real.exp (-K)`.

**R16 · `ring`** **closes** an equation that holds in every commutative ring. It treats `Real.exp K` and
`Real.exp (-K)` as unrelated unknowns, so it does not know `exp K * exp (-K) = 1`; the step identity
`(a + b)/2 · u + (a - b)/2 · v = (a (u + v) + b (u - v))/2` (with `a = cⁿ`, `b = sⁿ`, `u = e^K`, `v = e^{-K}`)
never needs it. After `simp`, all four entry goals are left, so write `simp [...] <;> ring`.

### The trace

**R17 · `rw [Matrix.trace_fin_two]`** changes the **goal**. The lemma is `A.trace = A 0 0 + A 1 1`.
Placeholders: `{α : Type} [AddCommMonoid α] (A : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ P A.trace` | `⊢ P (A 0 0 + A 1 1)` |

**R18 · `add_halves`** changes the **goal**. The lemma is `a / 2 + a / 2 = a`: the two diagonal entries
`(cⁿ + sⁿ)/2` add up to `cⁿ + sⁿ`. `simp` applies it by itself after R11. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / 2 + a / 2)` | `⊢ P a` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1.** `!![a, 0; 0, b] ^ n = !![a ^ n, 0; 0, b ^ n]`: R2; base case R3, R4, `simp`; step `rw [pow_succ, ih]`
(R9), R3, R4, `simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]` (R12, R13, R9 on the real powers).

**W2.** `!![1, 1; 0, 1] ^ n = !![1, ↑n; 0, 1]`: the same, but `simp` leaves one entry, `1 + ↑n = ↑n + 1`,
which `ring` closes. In the exercise `simp` leaves all four entries, hence `<;> ring`.

**W3.** Trace of a literal, R17 then `simp` (R11):

```lean-goal
⊢ !![a, b; c, d].trace = a + d
⊢ !![a, b; c, d] 0 0 + !![a, b; c, d] 1 1 = a + d
```

**W4.** `cosh x + sinh x = exp x`: R14, R15, then R16:

```lean-goal
⊢ Real.cosh x + Real.sinh x = Real.exp x
⊢ (Real.exp x + Real.exp (-x)) / 2 + (Real.exp x - Real.exp (-x)) / 2 = Real.exp x
```

---

## Traps

- Inducting on the statement about the trace fails: the hypothesis `tr Tⁿ = cⁿ + sⁿ` says nothing about
  the entries of `Tⁿ`, which you need to compute `Tⁿ⁺¹ = Tⁿ T`. Generalise to the whole matrix (`key`).
- `rw [pow_succ]` rewrites only the matrix power (R9); the real powers `c ^ (n + 1)` are expanded by
  `simp [..., pow_succ]`.
- Without `Matrix.mul_apply` and `Fin.sum_univ_two` in the `simp` list, the entries of `Tⁿ * T` stay
  unevaluated.
- Without `Real.cosh_eq`, `Real.sinh_eq` in the `simp` list, `ring` sees `Real.cosh K` and `Real.exp K` as
  unrelated unknowns and fails.
- In `have key : … := by`, the proof (and the `induction`) must be indented further than `have`.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| closed form of `M ^ n` as a fact | `have key : M ^ n = !![…] := by …` | R1 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R2 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R3, R4 |
| base case entries | `simp` | R5–R8, R11 |
| `M ^ (n + 1) → M ^ n * M`, then the hypothesis | `rw [pow_succ, ih]` | R9 |
| entries of `M ^ n * T` | `simp [T, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]` | R10–R13, R9 |
| `cosh`, `sinh` → `exp` | `Real.cosh_eq`, `Real.sinh_eq` (in the `simp` list) | R14, R15 |
| polynomial identity in `exp K`, `exp (-K)` | `<;> ring` | R16 |
| trace of a 2×2 matrix | `rw [Matrix.trace_fin_two]` | R17 |
| `a / 2 + a / 2 → a` | `simp` (uses `add_halves`) | R18 |
| see the state | infoview | |
