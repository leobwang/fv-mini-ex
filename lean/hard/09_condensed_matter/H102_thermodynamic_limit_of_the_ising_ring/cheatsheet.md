# H102 · Thermodynamic limit of the Ising ring: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). H097 (`Z = tr Tᴺ` for the ring) and M166 (the
eigenvalues of `T0`) are the physics behind the statement but are not required: milestone 1 proves what
is needed from scratch. **New here:** Mathlib's 2×2 matrices and their trace, `Real.exp`, `cosh`, `sinh`,
`Real.log`, absolute value `|·|`, and limits of sequences written with filters (`Tendsto`, `atTop`, `𝓝`,
`=ᶠ[atTop]`, `filter_upwards`).

**The maths in one line.** With `λ₊ = 2 cosh K`, `λ₋ = 2 sinh K` (the two eigenvalues of `T0 K`),
$Z_N = \operatorname{tr} T_0^N = λ_+^N + λ_-^N$, and $|λ_-| < λ_+$ because $\cosh^2 K = \sinh^2 K + 1$. With
$r = λ_-/λ_+$, $|r| < 1$:

$$\frac{\log Z_N}{N} = \frac{\log\big(λ_+^N (1 + r^N)\big)}{N} = \log λ_+ + \frac{\log(1 + r^N)}{N}
\xrightarrow{N\to\infty} \log λ_+ + \frac{\log 1}{\infty} = \log λ_+ .$$

The second equality needs $N \ne 0$; at $N = 0$ Lean's left side is $\log 2 / 0 = 0$ (division by zero is
`0` in Lean), so the two sequences agree only for $N \ge 1$, which is all a limit needs.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- `G : Prop` with `k : … → G` marks an entry that changes the **context**: the new fact is `h`, and `k` only
  closes the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A state containing `|·|` cannot sit in a Markdown table (`|` splits cells). Such states are given as a
  `lean-goal` block instead: the first line is the goal before the step, the next line the goal after.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℝ` | 2×2 real matrices; rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `M ^ n`, `M * N` | matrix power and matrix product |
| `M.trace`, `M.diag` | `Matrix.trace M = ∑ i, M i i`; `M.diag i = M i i` |
| `∑ i, f i` | the finite sum over all `i` of the index type (here `Fin 2`) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `rexp x` | `Real.exp x` (`eˣ`) |
| `cosh x`, `sinh x` | `Real.cosh`, `Real.sinh` (`open Real` drops the prefix) |
| `log x` | `Real.log x`, the natural log; Lean sets `log 0 = 0` and `log (-x) = log x` |
| `\|x\|` | the absolute value of `x` (`abs x`) |
| `x / 0` | `0`: division is total in Lean, so `x / 0 = 0` for every `x` |
| `↑N` | the natural number `N` cast into `ℝ` |
| `Nat.cast` | the cast function `ℕ → ℝ`, `n ↦ ↑n` |
| `atTop` | the filter "`N → ∞`" on `ℕ` (`Filter.atTop`) |
| `𝓝 a` | the filter of neighbourhoods of `a`: "`→ a`" (`nhds a`; needs `open Topology`) |
| `Tendsto f atTop (𝓝 a)` | $f(N) \to a$ as $N \to \infty$ (`Filter.Tendsto`) |
| `Tendsto g atTop atTop` | $g(N) \to +\infty$ |
| `f =ᶠ[atTop] g` | `f N = g N` for all large `N` (`Filter.EventuallyEq`) |
| `∀ᶠ N in atTop, Q N` | `Q N` holds for all large `N`: there is `N₀` with `Q N` for every `N ≥ N₀` (`Filter.Eventually`) |
| `r : ℝ := e` | a local definition made by `set`: `r` abbreviates `e` |
| `case zero`, `case succ` | the goals for `n = 0` and `n + 1` after `induction` (or `rcases N with _ \| N`) |
| `case succ.«0».«1»` | after `fin_cases i <;> fin_cases j` in that case: the goal for entry (0, 1) |
| `hf.const_add b` | dot notation: `hf : Tendsto …`, so this is `Filter.Tendsto.const_add b hf` (Lean looks the name up in the namespace of `hf`'s type). Likewise `h.ne'`, `h.congr'`, `h.log` |
| `n✝`, `a✝` | inaccessible names (made by a tactic); `rename_i` names them |

---

## Part 1 · `trace_pow` (milestone)

Statement: `Matrix.trace (T0 K ^ n) = (2 * cosh K) ^ n + (2 * sinh K) ^ n`. The trace of `T0 K ^ (n + 1)` is
not a function of the trace of `T0 K ^ n`, so do not induct on the trace: prove a closed form for the whole
matrix `T0 K ^ n` by induction (a `have key`, see the skeleton), then take its trace.

**R1 · `induction n with`** changes the **goal list**: the goal `P n` becomes the case `P 0` and the step
`P (n + 1)` with the induction hypothesis `ih : P n`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`. Write the two
cases as `| zero => …` and `| succ n ih => …`, each on its own line after `induction n with`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `pow_zero`** changes the **goal**: `x ^ 0 = 1`. `simp` applies it by itself. Placeholders:
`{α : Type} [Monoid α] (x : α)` (α has an associative `*` with `1`: numbers and square matrices qualify).

| Before | After |
|---|---|
| `⊢ P (x ^ 0)` | `⊢ P 1` |

**R3 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: entries of the identity matrix `1`
become `1` on the diagonal and `0` elsewhere. `simp` applies them by itself. Placeholders:
`(1 : Matrix (Fin 2) (Fin 2) ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 0 0) ∧ P (1 0 1)` | `⊢ P 1 ∧ P 0` |

**R4 · entry of a literal** changes the **goal**. `simp` uses `Matrix.of_apply` and `Matrix.cons_val_…` for
this. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 0 1)` | `⊢ P b` |

**R5 · `pow_succ`** changes the **goal**: `a ^ (n + 1) = a ^ n * a` (the new factor on the right).
Placeholders: `{α : Type} [Monoid α] (a : α) (n : ℕ)`. In the step, `rw [pow_succ, ih]` turns
`T0 K ^ (n + 1)` into `(closed form for n) * T0 K`. Inside `simp [..., pow_succ]` it also splits
`(2 * cosh K) ^ (n + 1)` so that `ring` can match the two sides.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R6 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (α has `*` and a
commutative `+` with `0`, as `ℝ` does), `(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R7 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R8 · `Real.cosh_eq`, `Real.sinh_eq`** change the **goal**: `cosh x = (exp x + exp (-x)) / 2` and
`sinh x = (exp x - exp (-x)) / 2`. After them every entry is a polynomial in `rexp K`, `rexp (-K)` and the
two `n`-th powers, and `ring` closes it (no `exp K * exp (-K) = 1` is needed). Placeholders: `(x : ℝ)`.

| Before | After `rw [Real.cosh_eq]` | After `rw [Real.sinh_eq]` |
|---|---|---|
| `⊢ P (cosh x) (sinh x)` | `⊢ P ((rexp x + rexp (-x)) / 2) (sinh x)` | `⊢ P ((rexp x + rexp (-x)) / 2) ((rexp x - rexp (-x)) / 2)` |

**R9 · `Matrix.trace`, `Matrix.diag_apply`** change the **goal**: the trace becomes the sum of the diagonal.
Then R7 gives `M 0 0 + M 1 1`; `simp [Matrix.trace, Fin.sum_univ_two]` does all of it (W2).
Placeholders: `{α : Type} [AddCommMonoid α] (M : Matrix (Fin 2) (Fin 2) α)`.

| Before | After `rw [Matrix.trace]` | After `simp only [Matrix.diag_apply]` |
|---|---|---|
| `⊢ P M.trace` | `⊢ P (∑ i, M.diag i)` | `⊢ P (∑ x, M x x)` |

**W1: the same induction on another matrix.** `!![1, 1; 0, 1] ^ n = !![1, ↑n; 0, 1]`. After `induction n`,
the zero case closes with `ext i j; fin_cases i <;> fin_cases j <;> simp` (R2–R4). The step, after R1 and
`rw [pow_succ, ih]` (R5):

```lean-goal
⊢ !![1, ↑n; 0, 1] * !![1, 1; 0, 1] = !![1, ↑(n + 1); 0, 1]
```

`ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]` (R6, R7) leaves one entry,
which `ring` closes:

```lean-goal
⊢ 1 + ↑n = ↑n + 1
```

In `trace_pow` the same `simp` also needs `T0`, R8 and `pow_succ`, and leaves four such goals: use `<;> ring`.

---

## Part 2 · `abs_lam_minus_lt` (milestone)

Statement: `|2 * sinh K| < 2 * cosh K`, i.e. `|λ₋| < λ₊`. Pull the `2` out of `|·|`, then it is
`|s| < c` from `c² = s² + 1` and `c > 0`.

**R10 · `abs_mul`** changes the **goal**: `|a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R11 · `abs_two`** changes the **goal**: `|2| = 2`. `rw [abs_mul, abs_two]` turns `|2 * s|` into `2 * |s|`.

```lean-goal
⊢ P |2|
⊢ P 2
```

**R12 · `Real.cosh_sq`** changes the **context**: `Real.cosh_sq x : cosh x ^ 2 = sinh x ^ 2 + 1`.
Placeholders: `(x : ℝ)`.

| Before | After `have h := Real.cosh_sq x` |
|---|---|
| `⊢ G` | `h : cosh x ^ 2 = sinh x ^ 2 + 1 ⊢ G` |

**R13 · `Real.cosh_pos`** changes the **context**: `Real.cosh_pos x : 0 < cosh x`. Placeholders: `(x : ℝ)`.

| Before | After `have hc := Real.cosh_pos x` |
|---|---|
| `⊢ G` | `hc : 0 < cosh x ⊢ G` |

**R14 · `abs_nonneg`, `sq_abs`** change the **context**: `abs_nonneg a : 0 ≤ |a|` and
`sq_abs a : |a| ^ 2 = a ^ 2`. `have h1 := abs_nonneg a; have h2 := sq_abs a` adds both. Usually you pass
them straight to `nlinarith` (R15) instead: they tell it how `|a|` relates to `a`. Placeholders: `(a : ℝ)`.

**R15 · `nlinarith [t₁, t₂]`** **closes** a polynomial inequality. It adds the facts `tᵢ` to the
hypotheses, multiplies pairs of hypotheses together, and searches for a linear combination. `|s|` counts as
an unknown, so it needs R14 to relate `|s|` to `s`. Example: `0 ≤ a`, `a < b` give `a ^ 2 < b ^ 2` with
`nlinarith [mul_self_nonneg (b - a)]` (`mul_self_nonneg x : 0 ≤ x * x`).

| Before | After |
|---|---|
| `ha : 0 ≤ a, hab : a < b ⊢ a ^ 2 < b ^ 2` | no goals |

---

## Part 3 · `limit_lemma` (milestone)

Statement: for `0 < lp` and `|lm| < lp`, `Tendsto (fun N : ℕ => log (lp ^ N + lm ^ N) / N) atTop (𝓝 (log lp))`.
Build the limit of the nice sequence `log lp + log (1 + r ^ N) / N` from library limits (R28–R33), then
move it to the given sequence, which equals it for `N ≥ 1` (R34–R39).

### Facts about `r = lm / lp`

**R16 · `set r := e with hr`** changes the **context and the goal**: it adds the local definition
`r : ℝ := e` and `hr : r = e`, and replaces every `e` in the goal and context by `r`. `set` only replaces
`e` literally (`lm / lp`), so `lm ^ N` in the goal stays as it is. Placeholders: `(a b : ℝ)`.

| Before | After `set r := a / b with hr` |
|---|---|
| `h : P (a / b) ⊢ P (a / b)` | `r : ℝ := a / b, h : P r, hr : r = a / b ⊢ P r` |

**R17 · `abs_div`** changes the **goal**: `|a / b| = |a| / |b|`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R18 · `abs_of_pos`** changes the **goal**: `abs_of_pos : 0 < a → |a| = a`. Placeholders: `(a : ℝ) (ha : 0 < a)`.

```lean-goal
⊢ P |a|
⊢ P a
```

**R19 · `div_lt_one`** changes the **goal**: `div_lt_one : 0 < b → (a / b < 1 ↔ a < b)`; `rw` with an `↔`
replaces the left statement by the right. Placeholders: `(a b : ℝ) (hb : 0 < b)`. `rw [hr, abs_div,
abs_of_pos h0, div_lt_one h0]` turns `|r| < 1` into `|lm| < lp`.

| Before | After `rw [div_lt_one hb]` |
|---|---|
| `⊢ a / b < 1` | `⊢ a < b` |

**R20 · `rcases N with _ | N`** changes the **goal list**: one goal for `N = 0`, one for `N + 1` (the new `N`
is the predecessor). Placeholders: `(P : ℕ → Prop) (N : ℕ)`. For `0 < 1 + r ^ N`: the `0` case is
`0 < 1 + r ^ 0`, closed by `norm_num`; the other needs R21–R25.

| Before | After |
|---|---|
| `N : ℕ ⊢ P N` | `⊢ P 0`, `N : ℕ ⊢ P (N + 1)` |

**R21 · `pow_lt_one₀`** changes the **context**: `pow_lt_one₀ : 0 ≤ a → a < 1 → n ≠ 0 → a ^ n < 1`.
Use it with `a = |r|` and `abs_nonneg r` (R14) for the first argument. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After `have h := pow_lt_one₀ h0 h1 hn` |
|---|---|
| `⊢ G` | `h : a ^ n < 1 ⊢ G` |

**R22 · `omega`** **closes** a linear goal over `ℕ` or `ℤ`, such as the side condition `N + 1 ≠ 0` of R21:
`pow_lt_one₀ (abs_nonneg r) hr1 (by omega)`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ n + 1 ≠ 0` | no goals |

**R23 · `neg_abs_le`** changes the **context**: `neg_abs_le a : -|a| ≤ a`. `have h := neg_abs_le (r ^ (N + 1))`
adds `h : -|r ^ (N + 1)| ≤ r ^ (N + 1)`. Placeholders: `(a : ℝ)`.

**R24 · `rw [abs_pow] at h`** changes the **context**: `abs_pow : |a ^ n| = |a| ^ n`, and `at h` rewrites the
hypothesis `h` instead of the goal. After it, `h : -|a| ^ n ≤ a ^ n` mentions the same `|a| ^ n` as R21's fact.
Placeholders: `(a : ℝ) (n : ℕ)`. The hypothesis states contain `|·|`, so they are not in a table; the
same rewrite on the goal (second example of R24 in `guide.lean`):

```lean-goal
⊢ P |a ^ n|
⊢ P (|a| ^ n)
```

**R25 · `linarith`** **closes** a linear (in)equality that follows from the hypotheses by adding them with
nonnegative coefficients. Nonlinear pieces such as `|r| ^ (N + 1)` and `r ^ (N + 1)` count as unknowns, so
`|r| ^ (N + 1) < 1` (R21) and `-|r| ^ (N + 1) ≤ r ^ (N + 1)` (R24) give `0 < 1 + r ^ (N + 1)`.

| Before | After |
|---|---|
| `h1 : x < 1, h2 : -x ≤ y ⊢ 0 < 1 + y` | no goals |

**R26 · `div_pow`** changes the **goal**: `(a / b) ^ n = a ^ n / b ^ n`. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a / b) ^ n)` | `⊢ P (a ^ n / b ^ n)` |

**R27 · `field_simp`** changes the **goal** (and often **closes** it): it multiplies out every denominator it
can prove nonzero, from hypotheses such as `hb : b ≠ 0` or `0 < b` in the context, and normalises. In
`heq` it needs `lp ^ N ≠ 0`, which it gets from `h0 : 0 < lp`. Placeholders: `(a b : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (b * (1 + a / b))` | `⊢ P (b + a)` |

### Library limits

A limit fact is a term: you build it with `have h := …` (context) and use it with `exact`/`simpa`.

**R28 · `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`** changes the **context**:
`|r| < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`. Placeholders: `(r : ℝ) (hr : |r| < 1)`.

| Before | After `have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr` |
|---|---|
| `⊢ G` | `h : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R29 · `Filter.Tendsto.const_add`** changes the **context**: from `hf : Tendsto f l (𝓝 a)` it gives
`hf.const_add b : Tendsto (fun n => b + f n) l (𝓝 (b + a))`. Placeholders: `(f : ℕ → ℝ) (a b : ℝ)`. Note
`𝓝 (b + a)`: the limit is not simplified (`1 + 0` stays `1 + 0` until R31).

| Before | After `have h := hf.const_add b` |
|---|---|
| `hf : Tendsto f atTop (𝓝 a) ⊢ G` | `h : Tendsto (fun x => b + f x) atTop (𝓝 (b + a)) ⊢ G` |

**R30 · `Filter.Tendsto.log`** changes the **context**: from `hf : Tendsto f l (𝓝 x)` and `hx : x ≠ 0` it
gives `hf.log hx : Tendsto (fun n => log (f n)) l (𝓝 (log x))` (continuity of `log` away from `0`).
Placeholders: `(f : ℕ → ℝ) (x : ℝ)`. With `x = 1 + 0`, prove `hx` by `(by norm_num)`.

| Before | After `have h := hf.log hx` |
|---|---|
| `hf : Tendsto f atTop (𝓝 x), hx : x ≠ 0 ⊢ G` | `h : Tendsto (fun x => log (f x)) atTop (𝓝 (log x)) ⊢ G` |

**R31 · `simpa using e`** **closes** the goal when `simp` brings the type of `e` and the goal to the same
form: here `log 1` becomes `0` (in the exercise also `1 + 0` becomes `1`, and `log lp + 0` becomes `log lp`).

| Before | After |
|---|---|
| `h : Tendsto (fun n => log (f n)) atTop (𝓝 (log 1)) ⊢ Tendsto (fun n => log (f n)) atTop (𝓝 0)` | no goals |

**R32 · `tendsto_natCast_atTop_atTop`** changes the **context**: `Tendsto (Nat.cast : ℕ → ℝ) atTop atTop`,
i.e. `↑n → ∞`. Inside R33 Lean finds `R := ℝ` itself; in a bare `have` write `(R := ℝ)`.

| Before | After `have h := tendsto_natCast_atTop_atTop (R := ℝ)` |
|---|---|
| `⊢ G` | `h : Tendsto Nat.cast atTop atTop ⊢ G` |

**R33 · `Filter.Tendsto.div_atTop`** changes the **context**: from `hf : Tendsto f l (𝓝 a)` and
`hg : Tendsto g l atTop` it gives `hf.div_atTop hg : Tendsto (fun n => f n / g n) l (𝓝 0)` (bounded over
unbounded → 0). Placeholders: `(f g : ℕ → ℝ) (a : ℝ)`. Then R29 adds `log lp` in front.

| Before | After `have h := hf.div_atTop hg` |
|---|---|
| `hf : Tendsto f atTop (𝓝 a), hg : Tendsto g atTop atTop ⊢ G` | `h : Tendsto (fun x => f x / g x) atTop (𝓝 0) ⊢ G` |

**W3: `log (3 + (1/2)ᴺ) / N → 0`.** R28 with `h1 : |1/2| < 1`, then `.const_add 3` (R29) gives
`Tendsto (fun x => 3 + (1 / 2) ^ x) atTop (𝓝 (3 + 0))`; `simpa using h2.log (by norm_num)` (R30, R31)
gives `log (3 + (1/2)ᴺ) → log 3`, and `h3.div_atTop tendsto_natCast_atTop_atTop` (R33, R32) closes:

```lean-goal
⊢ Tendsto (fun N => log (3 + (1 / 2) ^ N) / ↑N) atTop (𝓝 0)
```

### Moving a limit to a sequence that agrees for large `N`

**R34 · `refine h.congr' ?_`** changes the **goal**: `Filter.Tendsto.congr' : f =ᶠ[l] g → Tendsto f l b →
Tendsto g l b`, so with `h` the limit of `f`, the goal `Tendsto g …` becomes "`f` and `g` agree for all
large `N`". Placeholders: `(f g : ℕ → ℝ) (a : ℝ)`. `congr'` (with the prime) only needs agreement
eventually; `Tendsto.congr` needs it for every `N`, which fails at `N = 0`.

| Before | After `refine hf.congr' ?_` |
|---|---|
| `hf : Tendsto f atTop (𝓝 a) ⊢ Tendsto g atTop (𝓝 a)` | `⊢ f =ᶠ[atTop] g` |

**R35 · `filter_upwards [eventually_ge_atTop 1] with N hN`** changes the **goal and the context**: an
"eventually" goal (`=ᶠ[atTop]`, `∀ᶠ N in atTop, …`) becomes the statement for one `N`, with the fact
`eventually_ge_atTop 1 : ∀ᶠ N in atTop, 1 ≤ N` given as `hN`. Placeholders: `(f g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f =ᶠ[atTop] g` | `N : ℕ, hN : 1 ≤ N ⊢ f N = g N` |

**R36 · `positivity`** **closes** `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from `+`, `*`, `^`, `exp`,
`cosh`, casts and variables with hypotheses such as `0 < x` or `1 ≤ N` in the context. Uses here:
`(N : ℝ) ≠ 0` from `hN : 1 ≤ N`, `lp ^ N ≠ 0` from `h0 : 0 < lp`, and `0 < 2 * cosh K` in the main theorem.
Placeholders: `(N : ℕ) (hN : 1 ≤ N)`, and `(x : ℝ) (hx : 0 < x)` in the second example.

| Before | After |
|---|---|
| `hN : 1 ≤ N ⊢ ↑N ≠ 0` | no goals |

**R37 · `Real.log_mul`** changes the **goal**: `Real.log_mul : x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y`.
Placeholders: `(x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`. Give both side conditions inline:
`Real.log_mul (by positivity) (hpos N).ne'`.

| Before | After `rw [Real.log_mul hx hy]` |
|---|---|
| `⊢ P (log (x * y))` | `⊢ P (log x + log y)` |

**R38 · `h.ne'`** changes the **context** (as a term): `LT.lt.ne'` turns `h : 0 < a` into `a ≠ 0`
(`h.ne` gives `0 ≠ a`). `(hpos N).ne'` applies `hpos` at `N` first. Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After `have h := ha.ne'` |
|---|---|
| `ha : 0 < a ⊢ G` | `h : a ≠ 0 ⊢ G` |

**R39 · `Real.log_pow`** changes the **goal**: `Real.log_pow n x : log (x ^ n) = ↑n * log x`.
Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (log (x ^ n))` | `⊢ P (↑n * log x)` |

After `rw [heq, Real.log_mul …, Real.log_pow]` the goal is
`log lp + log (1 + r ^ N) / ↑N = (↑N * log lp + log (1 + r ^ N)) / ↑N`, and `field_simp` (R27) closes it
once `(N : ℝ) ≠ 0` is in the context.

**W4: a junk value at `N = 0`.** `Tendsto (fun N : ℕ => (N : ℝ) / N) atTop (𝓝 1)` is true, but `0 / 0 = 0`, so
`N / N = 1` fails at `N = 0`. Start from the constant sequence `1` (`tendsto_const_nhds`) and apply R34, R35:

| Before | After `refine tendsto_const_nhds.congr' ?_` | After `filter_upwards [eventually_ge_atTop 1] with N hN` |
|---|---|---|
| `⊢ Tendsto (fun N => ↑N / ↑N) atTop (𝓝 1)` | `⊢ (fun x => 1) =ᶠ[atTop] fun N => ↑N / ↑N` | `N : ℕ, hN : 1 ≤ N ⊢ 1 = ↑N / ↑N` |

Then `have hN' : (N : ℝ) ≠ 0 := by positivity` (R36) and `field_simp` (R27):

| Before | After `have hN' : (N : ℝ) ≠ 0 := by positivity` |
|---|---|
| `hN : 1 ≤ N ⊢ 1 = ↑N / ↑N` | `hN' : ↑N ≠ 0 ⊢ 1 = ↑N / ↑N` |

---

## Part 4 · `free_energy_per_spin`

Statement: `Tendsto (fun N : ℕ => log (Matrix.trace (T0 K ^ N)) / N) atTop (𝓝 (log (2 * cosh K)))`.
Rewrite the trace with milestone 1 under `fun N =>`, then it is milestone 3 with `lp = 2 * cosh K`,
`lm = 2 * sinh K`, whose hypotheses are R36 and milestone 2.

**R40 · `simp_rw [e]`** changes the **goal**: it rewrites with `e` also under a binder such as `fun N =>`,
where `rw` fails to find the pattern (the term mentions the bound variable `N`).
Placeholders: `(u v : ℕ → ℝ) (e : ∀ n, u n = v n)`.

| Before | After |
|---|---|
| `⊢ P fun N => u N / ↑N` | `⊢ P fun N => v N / ↑N` |

---

## Traps

- `trace_pow` by induction on the trace alone fails: `tr (T^(n+1))` is not a function of `tr (Tⁿ)`.
  Induct on the closed form of the whole matrix (`have key`), then take the trace.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.
- After `induction n with`, each case starts with `|` on its own line (`| zero => …`, `| succ n ih => …`),
  at the column of `induction` or deeper; the names after `succ` are yours to choose. Without them the
  step's variables print as `n✝`, `a✝`; name them with `rename_i n ih` (R1, second example).
- `ring` fails on the succ entries until `T0`, `cosh`, `sinh` are unfolded: `simp` must get `T0`,
  `Real.cosh_eq`, `Real.sinh_eq` (R8), or `ring` sees `cosh K` and `rexp K` as unrelated unknowns.
- At `N = 0` the quotient is junk: `x / 0 = 0` in Lean, so `log lp + log (1 + r ^ 0) / 0 = log lp` but
  `log (lp ^ 0 + lm ^ 0) / 0 = 0`. The two sequences agree only for `N ≥ 1`: use `congr'` (R34) with
  `eventually_ge_atTop 1` (R35), never a pointwise `funext`.
- `Tendsto.log` needs the limit to be nonzero (`1 + 0 ≠ 0`), and `Real.log_mul` needs both factors
  nonzero: prove `0 < 1 + r ^ N` for every `N` first (`hpos`), then use `(hpos N).ne'` (R38).
- `set r := lm / lp` does not rewrite `lm ^ N`; `heq` must be proved with `rw [hr, div_pow]` (R26) and
  `field_simp` (R27).
- `rw` cannot rewrite under `fun N =>` when the rewritten term contains `N`: use `simp_rw` (R40).
- Lean's `log` is total: `log 0 = 0`, `log (-x) = log x`. Lemmas such as `Real.log_mul` therefore carry
  `≠ 0` side conditions; `Real.log_pow` does not.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R1 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | TACTIC_STATES |
| `M ^ 0`, entries of `1`, of `!![…]` | `simp` | R2–R4 |
| `M ^ (n + 1) → M ^ n * M` | `rw [pow_succ]` | R5 |
| entries of a product | `simp [Matrix.mul_apply, Fin.sum_univ_two]` | R6, R7 |
| `cosh`, `sinh` → `exp` | `simp [Real.cosh_eq, Real.sinh_eq]` | R8 |
| trace of a 2×2 matrix | `simp [Matrix.trace, Fin.sum_univ_two]` | R9, R7 |
| `\|2 * s\| → 2 * \|s\|` | `rw [abs_mul, abs_two]` | R10, R11 |
| `cosh² = sinh² + 1`, `cosh > 0` | `have := Real.cosh_sq K`, `have := Real.cosh_pos K` | R12, R13 |
| polynomial inequality with `\|s\|` | `nlinarith [abs_nonneg s, sq_abs s]` | R14, R15 |
| name a subterm | `set r := lm / lp with hr` | R16 |
| `\|a / b\| < 1 → \|a\| < b` | `rw [abs_div, abs_of_pos h, div_lt_one h]` | R17–R19 |
| split `N = 0` / `N + 1` | `rcases N with _ \| N` | R20 |
| `aⁿ < 1` | `pow_lt_one₀ h0 h1 (by omega)` | R21, R22 |
| `-\|a\| ≤ a`, `\|aⁿ\| = \|a\|ⁿ` | `neg_abs_le a`, `rw [abs_pow] at h` | R23, R24 |
| linear consequence | `linarith` | R25 |
| `(a / b)ⁿ`, clear denominators | `rw [div_pow]`, `field_simp` | R26, R27 |
| `rⁿ → 0` | `tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr` | R28 |
| `b + f → b + a`, `log f → log a`, `f / g → 0` | `h.const_add b`, `h.log hx`, `h.div_atTop hg` | R29, R30, R33 |
| clean up `1 + 0`, `log 1`, `x + 0` | `simpa using h` | R31 |
| `↑N → ∞` | `tendsto_natCast_atTop_atTop` | R32 |
| limit of a sequence equal for `N ≥ 1` | `refine h.congr' ?_; filter_upwards [eventually_ge_atTop 1] with N hN` | R34, R35 |
| `0 < e`, `e ≠ 0` | `positivity`, `h.ne'` | R36, R38 |
| `log (x * y)`, `log (xⁿ)` | `rw [Real.log_mul hx hy, Real.log_pow]` | R37, R39 |
| rewrite under `fun N =>` | `simp_rw [trace_pow]` | R40 |
| see the state | infoview | |
