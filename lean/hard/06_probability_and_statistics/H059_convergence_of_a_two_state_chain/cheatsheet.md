# H059 · Convergence of a 2-state chain: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `simp`, `exact`, `have`, `constructor`, induction on `ℕ`.
**New here:** Mathlib's 2×2 real matrices (entries, products, powers, scalar multiples), the absolute value
on `ℝ`, `field_simp` / `linarith`, and limits of sequences written with filters (`Tendsto … atTop (𝓝 L)`).

## The math in one paragraph

`P = !![1 - a, a; b, 1 - b]` is the transition matrix of a chain on states `{0, 1}`: `P i j` is the
probability of moving from `i` to `j` in one step, so `(Pⁿ) i j` is the probability after `n` steps.
`Π = Pinf a b` has both rows equal to `π = (b, a) / (a + b)`. Two facts carry the whole proof:
`P Π = Π` (every row of `Π` is stationary: `π P = π`, and the columns of `Π` are constant) and
`P (1 - Π) = λ (1 - Π)` with `λ = 1 - a - b`, the second eigenvalue of `P`. By induction they give
`Pⁿ = Π + λⁿ (1 - Π)`. If `0 < a + b < 2` then `|λ| < 1`, so `λⁿ → 0` and each entry `(Pⁿ) i j → Π i j = π j`,
whatever the start state `i`. (The bounds `0 ≤ a, b ≤ 1` only make `P` stochastic; the proof never uses them.)

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. (In the guide `P` is this placeholder, not the exercise's matrix.)
- `G` is an arbitrary goal (`G : Prop`) when an entry only adds a hypothesis.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Ring α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℝ` | 2×2 matrices with real entries; rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![p, q; r, s]` | the matrix with rows `p q` and `r s` (`;` separates rows) |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `![x, y]` | the vector (function `Fin 2 → ℝ`) with `![x, y] 0 = x`, `![x, y] 1 = y` |
| `1` (a matrix) | the identity matrix; `1 i j` is `1` if `i = j`, else `0` |
| `s • M` | the scalar `s : ℝ` times every entry of `M` |
| `A * B`, `A ^ n` | matrix product and power (`A ^ n` = `A * ⋯ * A`, `n` factors; `A ^ 0 = 1`); `*` is **not** commutative |
| `∑ j, f j` | the finite sum `f 0 + f 1` over all `j : Fin 2` (`Finset.sum Finset.univ f`); appears after R5 |
| `x⁻¹` | the inverse `1 / x` of `x : ℝ` (`simp` turns `1 / x` into `x⁻¹`; W1) |
| `\|x\|` | absolute value of `x : ℝ` |
| `Tendsto f atTop (𝓝 L)` | `f n → L` as `n → ∞`. `Filter.Tendsto f F G` says "`f` maps filter `F` into filter `G`"; `atTop` is the filter of eventually-large `n`, `𝓝 L` the filter of neighbourhoods of `L` (`open Filter Topology` makes the short names work) |
| `fun x => f x + g x` | the sequence `n ↦ f n + g n`; the bound name (`x`, `n`) does not matter |
| `P fun n => …` | `P` applied to a `fun`; Lean drops the parentheses |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `hx.ne'` | dot notation: `LT.lt.ne' hx`, turning `hx : 0 < x` into `x ≠ 0` |
| `case succ`, `case «0».«1»` | the label of the goal: induction step; entry (0, 1) |

---

## Part 1 · `P_mul_Pinf` (MILESTONE 1)

Statement: for `a + b ≠ 0`, `P a b * Pinf a b = Pinf a b`. A 2×2 matrix equation; each entry is a fraction
identity such as `(1 - a) * (b / (a + b)) + a * (b / (a + b)) = b / (a + b)`.

**R1 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when every
entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R2 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context and there is one goal per
value `0, 1`. Placeholders: `(P : Fin 2 → Prop) (i : Fin 2)`. `fin_cases i <;> fin_cases j` gives all four entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

**R3 · `simp only [Q]`** changes the **goal**: a defined name applied to arguments is replaced by its body at
those arguments (`P a b` becomes `!![1 - a, a; b, 1 - b]`). Placeholders: `Q` defined by
`def Q (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, 1; 0, c]`, `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Q c)` | `⊢ P !![c, 1; 0, c]` |

**R4 · entry of a literal** changes the **goal**: `simp` evaluates `!![…] i j` at concrete indices
(`Matrix.of_apply`, `Matrix.cons_val_…`). Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

**R5 · `Matrix.mul_apply`** changes the **goal**: `(M * N) i k = ∑ j, M i j * N j k`. Placeholders:
`{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a commutative `+` with `0`; `ℝ` qualifies),
`(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R6 · `Fin.sum_univ_two`** changes the **goal**: `∑ i, f i = f 0 + f 1` for `i : Fin 2`. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R7 · `field_simp`** changes the **goal**: it multiplies an equation through by its denominators, leaving a
polynomial equation. It needs each denominator to be known nonzero: a hypothesis `hc : c ≠ 0` in the context
(for this problem, `hab : a + b ≠ 0`). Placeholders: `(x y c : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ x + y / c = x` | `⊢ x * c + y = x * c` |

**R8 · `ring`** **closes** an equation that holds in every commutative ring (`ℝ` here). It uses no hypotheses
and fails on anything with a variable denominator, so run it after `field_simp`.

| Before | After |
|---|---|
| `⊢ x * (1 - y + y) = x` | no goals |

---

## Part 2 · `P_mul_one_sub` (MILESTONE 2)

Statement: for `a + b ≠ 0`, `P a b * (1 - Pinf a b) = (1 - a - b) • (1 - Pinf a b)`. First distribute and use
MILESTONE 1 at the matrix level, then go entrywise as in Part 1.

**R9 · `rw [mul_sub]`** changes the **goal**. Lemma `mul_sub : a * (b - c) = a * b - a * c`. Placeholders:
`{α : Type} [Ring α] (a b c : α)`; `ℝ` and `Matrix (Fin 2) (Fin 2) ℝ` are rings.

| Before | After |
|---|---|
| `⊢ P (a * (b - c))` | `⊢ P (a * b - a * c)` |

**R10 · `rw [mul_one]`** changes the **goal**. Lemma `mul_one : a * 1 = a` (for matrices, `1` is the identity).
Placeholders: `{α : Type} [Ring α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

After R9, R10, `rw [P_mul_Pinf a b hab]` replaces `P a b * Pinf a b` by `Pinf a b`; the goal becomes
`P a b - Pinf a b = (1 - a - b) • (1 - Pinf a b)`. Then R1, R2, and `simp [P, Pinf]`, which uses R4 and R11–R13.

**R11 · `Matrix.sub_apply`** changes the **goal**: `(M - N) i j = M i j - N i j`. Placeholders:
`(M N : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M - N) i j)` | `⊢ P (M i j - N i j)` |

**R12 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix are
`1` on the diagonal and `0` off it. `simp` applies them. Placeholders: `(1 : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R13 · `Matrix.smul_apply`, then `smul_eq_mul`** change the **goal**: `(s • M) i j = s • M i j`, and for real
numbers `s • x = s * x`. Placeholders: `(s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2)`.

| Before | After `rw [Matrix.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((s • M) i j)` | `⊢ P (s • M i j)` | `⊢ P (s * M i j)` |

The four entry goals then look like `1 - a - b / (a + b) = (1 - a - b) * (1 - b / (a + b))`: R7, then R8.

---

## Part 3 · `abs_lt_one` (MILESTONE 3)

Statement: `0 < a + b → a + b < 2 → |1 - a - b| < 1`. This is the hypothesis R25 needs.

**R14 · `rw [abs_lt]`** changes the **goal**. Lemma `abs_lt : |a| < b ↔ -b < a ∧ a < b`: an absolute-value bound
becomes two linear ones. Placeholders: `(x r : ℝ)`. Before, then after (a block, since `|` cannot sit in a table):

```lean-goal
⊢ |x| < r
⊢ -r < x ∧ x < r
```

Then `constructor` (TACTIC_STATES, "Structure") gives the two inequalities.

**R15 · `linarith`** **closes** a goal that is a linear consequence (sums and constant multiples) of the
hypotheses' inequalities. Placeholders: `(x y : ℝ) (h : 0 < x + y)`.

| Before | After |
|---|---|
| `h : 0 < x + y ⊢ 1 - x - y < 1` | no goals |

---

## Part 4 · `pow_formula`

Statement: for `a + b ≠ 0` and every `n : ℕ`, `P a b ^ n = Pinf a b + (1 - a - b) ^ n • (1 - Pinf a b)`.
Induction on `n`; the step uses MILESTONES 1 and 2 and never looks at entries.

**R16 · `induction n with`** changes the **goal list and the context**: the goal `P n` becomes `P 0` and, in the
`succ` case, `P (n + 1)` with the induction hypothesis `ih : P n`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.
Below, the `zero` case is closed inline and `| succ n ih => ?_` leaves the `succ` goal open (`?_` = "prove this
next"), so only the `succ` goal is left.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `ih : P n ⊢ P (n + 1)` |

**R17 · `pow_zero`** changes the **goal**: `a ^ 0 = 1`. Placeholders: `(A : Matrix (Fin 2) (Fin 2) ℝ)` (any monoid).

| Before | After |
|---|---|
| `⊢ P (A ^ 0)` | `⊢ P 1` |

**R18 · `one_smul`** changes the **goal**: `1 • M = M`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 • M)` | `⊢ P M` |

**R19 · `add_sub_cancel`** changes the **goal**: `a + (b - a) = b`. Placeholders:
`{α : Type} [AddCommGroup α] (a b : α)` (α has `+`, `-`, `0`, commutative; `ℝ` and matrices qualify).

| Before | After |
|---|---|
| `⊢ P (a + (b - a))` | `⊢ P b` |

The base case is `P a b ^ 0 = Pinf a b + (1 - a - b) ^ 0 • (1 - Pinf a b)`: plain `simp` closes it with R17–R19.

**R20 · `rw [pow_succ']`** changes the **goal**: `a ^ (n + 1) = a * a ^ n` (one factor peeled off on the
**left**, which is where `P a b *` must sit for the milestones). Placeholders:
`(A : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (A ^ (n + 1))` | `⊢ P (A * A ^ n)` |

**R21 · `rw [mul_add]`** changes the **goal**: `a * (b + c) = a * b + a * c`. Placeholders:
`{α : Type} [Ring α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R22 · `rw [mul_smul_comm]`** changes the **goal**: `A * s • B = s • (A * B)`; the scalar moves out of a matrix
product (`A * s • B` means `A * (s • B)`). Placeholders: `(s : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (A * s • B)` | `⊢ P (s • (A * B))` |

**R23 · `rw [smul_smul]`** changes the **goal**: `r • s • M = (r * s) • M` (two scalars merge into one).
Placeholders: `(r s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (r • s • M)` | `⊢ P ((r * s) • M)` |

**R24 · `pow_succ`** changes the **goal**: `a ^ (n + 1) = a ^ n * a` (factor on the **right**). After R23 the
scalar is `(1 - a - b) ^ n * (1 - a - b)`; `rw [pow_succ]` turns the right side's `(1 - a - b) ^ (n + 1)` into
that same product, and `rw` closes the goal by `rfl`. Placeholders: `(r : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (r ^ (n + 1))` | `⊢ P (r ^ n * r)` |

---

## Part 5 · `converges`

Statement: if `0 < a + b < 2`, then for all `i j : Fin 2`,
`Tendsto (fun n : ℕ => (P a b ^ n) i j) atTop (𝓝 (![b / (a + b), a / (a + b)] j))`: entry `(i, j)` of `Pⁿ` tends to
`π j`. Plan: get `λⁿ → 0` (R25 with MILESTONE 3), rewrite `Pⁿ` by `pow_formula` under the `fun` (R26, R27),
split the entry (R28, R13), build the limit of `Π i j + λⁿ * (1 - Π) i j` (R29–R32), and match it (R33, R34).

**R25 · `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`** changes the **context** (with `have`). Lemma:
`|r| < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`, i.e. `rⁿ → 0`. Placeholders: `(r : ℝ) (hr : |r| < 1)`.

| Before | After `have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr` |
|---|---|
| `⊢ G` | `h0 : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R26 · `hx.ne'`** changes the **context** (with `have`), or is passed directly as an argument
(`pow_formula a b hab.ne'`). `LT.lt.ne' : a < b → b ≠ a`, so from `hx : 0 < x` it gives `x ≠ 0`.
Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ G` | `hne : x ≠ 0 ⊢ G` |

**R27 · `simp_rw [h]`** changes the **goal**: it rewrites with `h` everywhere, **including under `fun n => …`**,
where the bound `n` stops `rw`. Use it for `pow_formula` (an equation for every `n`) and for the `_apply` lemmas
inside the sequence. Placeholders: `(A B : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (hAB : ∀ n, A n = B n) (i j : Fin 2)`,
`(P : (ℕ → ℝ) → Prop)`.

| Before | After `simp_rw [hAB]` |
|---|---|
| `⊢ P fun n => A n i j` | `⊢ P fun n => B n i j` |

**R28 · `Matrix.add_apply`** changes the **goal**: `(M + N) i j = M i j + N i j`. Placeholders:
`(M N : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M + N) i j)` | `⊢ P (M i j + N i j)` |

After R27 with `pow_formula`, R28, R13, the goal is
`Tendsto (fun n => Pinf a b i j + (1 - a - b) ^ n * (1 - Pinf a b) i j) atTop (𝓝 (![…] j))`.

**R29 · `tendsto_const_nhds`** changes the **context**: `Tendsto (fun _ => c) F (𝓝 c)` for any filter `F`.
Lean must be told `c` (and finds `F` from where the term is used): write `tendsto_const_nhds (x := c)`.
Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Tendsto (fun x => c) atTop (𝓝 c) ⊢ G` |

**R30 · `Filter.Tendsto.add`** changes the **context**: from `f → x` and `g → y`, `hf.add hg : f + g → x + y`.
Placeholders: `(f g : ℕ → ℝ) (x y : ℝ)`.

| Before | After `have h := hf.add hg` |
|---|---|
| `hf : Tendsto f atTop (𝓝 x), hg : Tendsto g atTop (𝓝 y) ⊢ G` | `h : Tendsto (fun x => f x + g x) atTop (𝓝 (x + y)) ⊢ G` |

**R31 · `Filter.Tendsto.mul`** changes the **context**: `hf.mul hg : f * g → x * y`. Same placeholders.
`h0.mul (tendsto_const_nhds (x := c))` is "`λⁿ * c → 0 * c`".

| Before | After `have h := hf.mul hg` |
|---|---|
| `hf : Tendsto f atTop (𝓝 x), hg : Tendsto g atTop (𝓝 y) ⊢ G` | `h : Tendsto (fun x => f x * g x) atTop (𝓝 (x * y)) ⊢ G` |

**R32 · `rw [zero_mul, add_zero] at h`** changes the **context**: it rewrites hypothesis `h` instead of the goal
(`zero_mul : 0 * a = 0`, `add_zero : a + 0 = a`). Placeholders: `(f : ℕ → ℝ) (x y : ℝ)`.

| Before | After |
|---|---|
| `h : Tendsto f atTop (𝓝 (x + 0 * y)) ⊢ Tendsto f atTop (𝓝 x)` | `h : Tendsto f atTop (𝓝 x) ⊢ Tendsto f atTop (𝓝 x)` |

**R33 · `convert h using 2`** changes the **goal list**: it closes the goal with `h` except where the two differ,
and leaves one equation per difference. `using 2` stops two levels down (inside `Tendsto f atTop (…)`, then
inside `𝓝 (…)`), so the leftover is an equation of limits, not of filters. It closes leftovers that are `rfl` or a
hypothesis by itself. Placeholders: `(f : ℕ → ℝ) (x y : ℝ) (h : Tendsto f atTop (𝓝 y))`.

| Before | After |
|---|---|
| `h : Tendsto f atTop (𝓝 y) ⊢ Tendsto f atTop (𝓝 x)` | `⊢ x = y` |

In the exercise the leftover is `![b / (a + b), a / (a + b)] j = Pinf a b i j`: R2 on `i` and on `j`, then
`simp [Pinf]` (R3, R4, R34). It holds for both `i` because both rows of `Pinf` are `π`.

**R34 · entry of a vector literal** changes the **goal**: `simp` evaluates `![x, y] 0 = x`, `![x, y] 1 = y`
(`Matrix.cons_val_zero`, `Matrix.cons_val_one`). Placeholders: `{α : Type} (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (![x, y] 1)` | `⊢ P y` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: entrywise identity with a denominator.** `S c = !![c, 0; 0, c]`, `hc : c ≠ 0`, goal
`S c * !![1 / c, 0; 0, 1 / c] = 1`. R1, R2, then `simp [S, Matrix.mul_apply, Fin.sum_univ_two]` closes the
off-diagonal entries and leaves on the diagonal

```lean-goal
⊢ c * c⁻¹ = 1
```

which `field_simp` (R7) closes using `hc`.

**W2: a power identity by induction.** From `hA : A * E = E`, prove `A ^ n * E = E`:

```lean-goal
⊢ A ^ n * E = E
```

`induction n with` (R16); `zero`: `simp` (R17, `one_mul`); `succ`: `rw [pow_succ', mul_assoc, ih, hA]` (R20).
Same shape as `pow_formula`: peel `A` off on the left, use the IH, then a one-step identity.

**W3: a limit `c + (1/2)ⁿ · d → c`.** `hr : |1 / 2| < 1` by R14 and `norm_num`; then R25, and R29–R31 in one term
`(tendsto_const_nhds (x := c)).add (h0.mul (tendsto_const_nhds (x := d)))`; then R32:

| Step | State |
|---|---|
| start | `⊢ Tendsto (fun n => c + (1 / 2) ^ n * d) atTop (𝓝 c)` |
| R25 | `h0 : Tendsto (fun n => (1 / 2) ^ n) atTop (𝓝 0) ⊢ Tendsto (fun n => c + (1 / 2) ^ n * d) atTop (𝓝 c)` |
| R29–R31 | `h : Tendsto (fun x => c + (1 / 2) ^ x * d) atTop (𝓝 (c + 0 * d)) ⊢ Tendsto (fun n => c + (1 / 2) ^ n * d) atTop (𝓝 c)` |
| R32 | `h : Tendsto (fun x => c + (1 / 2) ^ x * d) atTop (𝓝 c) ⊢ Tendsto (fun n => c + (1 / 2) ^ n * d) atTop (𝓝 c)` |

Then `exact h` (the bound names `x`, `n` do not matter). In the exercise the limit of `h` is an entry of
`Pinf`, not literally the goal's `![…] j`, hence R33 instead of `exact`.

---

## Traps

- Only `0 < a + b < 2` is used. `ha ha1 hb hb1` (`0 ≤ a ≤ 1`, `0 ≤ b ≤ 1`) just make `P` stochastic, so the
  solution gets unused-variable warnings for them; that is expected.
- `field_simp` needs `a + b ≠ 0` in the context. In `converges` you have `hab : 0 < a + b`: pass `hab.ne'` (R26).
- `rw [pow_formula a b hab.ne']` fails inside `fun n => (P a b ^ n) i j` (`n` is bound): use `simp_rw` (R27).
- `pow_succ'` (`a * a ^ n`) and `pow_succ` (`a ^ n * a`) differ by the side of the extra factor. For matrices
  the side matters: the milestones have `P a b *` on the **left**.
- Matrix `*` is not commutative: never `mul_comm` a matrix product. Move scalars with `mul_smul_comm` (R22).
- `simp` on the base case: `P a b ^ 0` is `1`, and `simp` closes the whole goal (R17–R19); do not unfold `P`.
- `convert h` without `using` may dig too deep and leave goals like `HAdd.hAdd … = …`; use `using 2` (R33).
- `tendsto_const_nhds` alone has an unknown constant: give it as `tendsto_const_nhds (x := …)` (R29).
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R1, R2 |
| evaluate entries of products | `simp [P, Pinf, Matrix.mul_apply, Fin.sum_univ_two]` | R3–R6 |
| entries of `-`, `1`, `•` | `simp [P, Pinf]` | R11–R13 |
| clear denominators, then finish | `field_simp` then `ring` | R7, R8 |
| `A * (1 - B) → A - A * B` | `rw [mul_sub, mul_one]` | R9, R10 |
| `\|x\| < r` → two inequalities | `rw [abs_lt]; constructor <;> linarith` | R14, R15 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R16 |
| base case `A ^ 0 = …` | `simp` | R17–R19 |
| `A ^ (n+1) → A * A ^ n` | `rw [pow_succ']` | R20 |
| distribute, move scalar, merge scalars | `rw [mul_add, mul_smul_comm, …, smul_smul, pow_succ]` | R21–R24 |
| `\|r\| < 1 ⟹ rⁿ → 0` | `tendsto_pow_atTop_nhds_zero_of_abs_lt_one h` | R25 |
| `0 < x ⟹ x ≠ 0` | `hx.ne'` | R26 |
| rewrite under `fun n =>` | `simp_rw [lemma, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]` | R27, R28, R13 |
| limit of `c + rⁿ * d` | `(tendsto_const_nhds (x := c)).add (h0.mul (tendsto_const_nhds (x := d)))` | R29–R31 |
| clean the limit value | `rw [zero_mul, add_zero] at h` | R32 |
| goal and `h` differ only in the limit | `convert h using 2` | R33 |
| `![x, y] 1 → y` | `simp` | R34 |
| see the state | infoview | |
