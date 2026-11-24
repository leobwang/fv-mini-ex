# H066 · Central differences are second order: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The idea of M111 / H065 (one Taylor expansion, read off
its coefficients) helps but is not needed: every Mathlib name used below is explained here.
**New here:** Mathlib's derivatives on `ℝ` (`deriv`, `iteratedDeriv`, and their "within a set" versions),
smoothness classes `ContDiff`, Taylor polynomials `taylorWithinEval` and Taylor's theorem with Lagrange
remainder, unordered intervals `uIcc`, absolute values `|·|`, and the tactics `linarith`, `linear_combination`,
`field_simp`, `positivity`, `gcongr`, `calc`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`obtain`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop` or `P : Set ℝ → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal or hypothesis.
- Placeholders are written as Lean binders: `(a b : ℝ)`, `(f : ℝ → ℝ)`, `(n : ℕ)`, `(s : Set ℝ)`.
  All the lemmas here are stated in Mathlib for general fields or ordered groups; every entry uses them
  on `ℝ`, which is all this exercise needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `deriv f x` | the derivative $f'(x)$ (Mathlib gives `0` where `f` is not differentiable) |
| `iteratedDeriv k f x` | the $k$-th derivative $f^{(k)}(x)$; `iteratedDeriv 1 f = deriv f` (R17) |
| `iteratedDerivWithin k f s x` | the $k$-th derivative computed using only the values of `f` on the set `s`; equal to `iteratedDeriv k f x` under R12's conditions |
| `derivWithin f s x` | `iteratedDerivWithin 1 f s x` after `simp`/`norm_num` rewrote it (W4: a trap) |
| `ContDiff ℝ n f` | $f$ is $n$ times continuously differentiable on all of $\mathbb{R}$ ($C^n$) |
| `ContDiffOn ℝ n f s`, `ContDiffAt ℝ n f x` | $C^n$ on the set `s` / near the point `x` |
| `↑n` in `ContDiff ℝ (↑n) f` | the order `n : ℕ` cast into `WithTop ℕ∞` = $\{0,1,2,\dots,\infty,\omega\}$, the type of smoothness orders; a numeral such as `3` there already lives in `WithTop ℕ∞` |
| `uIcc a b` | `Set.uIcc a b` = $[\min(a,b), \max(a,b)]$, the closed interval between `a` and `b` in either order |
| `Icc a b`, `uIoo a b` | $[a, b]$; the open interval between `a` and `b` in either order |
| `Set ℝ`, `a ∈ s` | a set of reals (a predicate `ℝ → Prop`); `a` belongs to `s` |
| `UniqueDiffOn ℝ s` | at every point of `s`, derivatives within `s` are unique (true for a non-degenerate interval, R4) |
| `taylorWithinEval f n s x₀ x` | the degree-$n$ Taylor polynomial of `f` at `x₀`, built from `iteratedDerivWithin k f s x₀`, evaluated at `x` |
| `↑(n + 1).factorial`, `Nat.factorial 1` | $(n+1)!$ as a natural number, cast `↑` into `ℝ` |
| `r • v` | scalar times vector; on `ℝ` it is plain `r * v` (`norm_num` rewrites it, R18) |
| `|a|` | absolute value of `a : ℝ` |
| `case inl`, `case inr` | the left / right case of an `∨` after `rcases` (R1) |
| `case hbc` | the goal `gcongr` left for you (R27) |

---

## Part 1 · `central_difference_error`

Statement: if $f \in C^3$, $h > 0$ and $|f'''(y)| \le M$ for all $y$, then
$\left|\frac{f(x+h) - f(x-h)}{2h} - f'(x)\right| \le \frac{M h^2}{6}$.
The milestones split it: `uniqueDiffOn_uIcc` (an interval with distinct endpoints has unique derivatives) →
`taylor2` (Taylor of degree 2 with remainder $f'''(\xi) h^3/6$, for a step $h$ of either sign) →
`central_error_eq` (subtract the expansions at $h$ and $-h$) → the bound.

### Milestone `uniqueDiffOn_uIcc`: two orders, two intervals

**R1 · `rcases hab.lt_or_gt with h | h`** changes the **goal list and the context**: `Ne.lt_or_gt` turns
`hab : a ≠ b` into `a < b ∨ b < a`, and `rcases … with h | h` makes one goal per side, each with its own `h`.
Placeholders: `(a b : ℝ) (P : Prop)`.

| Before | After |
|---|---|
| `hab : a ≠ b ⊢ P` | `h : a < b ⊢ P`, `h : b < a ⊢ P` |

**R2 · `rw [uIcc_of_le hab]`** changes the **goal**. `Set.uIcc_of_le : a ≤ b → uIcc a b = Icc a b`.
From `h : a < b` write `h.le` to get `a ≤ b`. Placeholders: `(a b : ℝ) (hab : a ≤ b) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (uIcc a b)` | `⊢ P (Icc a b)` |

**R3 · `rw [uIcc_of_ge hba]`** changes the **goal**. `Set.uIcc_of_ge : b ≤ a → uIcc a b = Icc b a`: the
endpoints come out swapped. Placeholders: `(a b : ℝ) (hba : b ≤ a) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (uIcc a b)` | `⊢ P (Icc b a)` |

**R4 · `exact uniqueDiffOn_Icc hab`** **closes** the goal. `uniqueDiffOn_Icc : a < b → UniqueDiffOn ℝ (Icc a b)`
(strict: a one-point interval has no unique derivative). Placeholders: `(a b : ℝ) (hab : a < b)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ UniqueDiffOn ℝ (Icc a b)` | no goals |

### Milestone `taylor2`: one expansion

Taylor's theorem needs `x ≠ x + h`; prove it from `hh : h ≠ 0` with R5 → R6 → R7.

**R5 · `intro e`** on `a ≠ b` changes the **context and the goal**: `a ≠ b` means `a = b → False`, so
`intro` names the equation and the goal becomes `False`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `e : a = b ⊢ False` |

**R6 · `apply hc`** with `hc : c ≠ 0` changes the **goal**: `hc : c = 0 → False` ends in `False`, so `apply`
reduces `False` to `c = 0`. Placeholders: `(c : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ False` | `⊢ c = 0` |

**R7 · `linarith`** **closes** a goal `t ≤ u`, `t < u`, `t = u`, `t ≠ u` (or `False`) that follows from the
hypotheses by adding up linear (in)equalities with nonnegative coefficients. Products of two unknowns, and
terms such as `f x` or `|a|`, count as atoms. Use it for the side goals `h ≠ 0` and `-h ≠ 0` from `hh : 0 < h`
in `central_error_eq` (write `(by linarith)` in the argument position). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `e : a + b = a ⊢ b = 0` | no goals |
| `hc : 0 < c ⊢ -c ≠ 0` | no goals |

**R8 · `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf`** changes the **context**.
The lemma (Taylor with Lagrange remainder) says: for `x₀ ≠ x` and `f` of class $C^{n+1}$ on `uIcc x₀ x`,

$$\exists\, \xi \in \operatorname{uIoo}(x_0, x),\quad f(x) - T_n(x) = \frac{f^{(n+1)}(\xi)\,(x - x_0)^{n+1}}{(n+1)!},$$

with $T_n$ = `taylorWithinEval f n (uIcc x₀ x) x₀`. `obtain` names `ξ`, `-` throws away `ξ ∈ uIoo …` (not
needed here), `hξ` is the equation. Choose the degree and the points with named arguments:
`(n := 2) (x₀ := x) (x := x + h)`. Placeholders: `(f : ℝ → ℝ) (n : ℕ) (a b : ℝ) (hne : a ≠ b)`.

| Before | After |
|---|---|
| `hf : ContDiffOn ℝ (↑n + 1) f (uIcc a b) ⊢ P` | `ξ : ℝ, hξ : f b - taylorWithinEval f n (uIcc a b) a b = iteratedDeriv (n + 1) f ξ * (b - a) ^ (n + 1) / ↑(n + 1).factorial ⊢ P` |

**R9 · `hf.contDiffOn`** (`ContDiff.contDiffOn : ContDiff ℝ n f → ContDiffOn ℝ n f s`) **closes** the goal: $C^n$
everywhere gives $C^n$ on any set. In the exercise `hf : ContDiff ℝ 3 f` is accepted where R8 wants
`ContDiffOn ℝ (↑2 + 1) f _`: Lean checks `3 = ↑2 + 1` by computation. Placeholders: `(f : ℝ → ℝ) (n : ℕ) (s : Set ℝ)`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ (↑n) f ⊢ ContDiffOn ℝ (↑n) f s` | no goals |

Then `refine ⟨ξ, ?_⟩` (TACTIC_STATES) picks this `ξ` for the goal's `∃ ξ`.

**R10 · `rw [taylorWithinEval_succ]`** changes the **goal** (with `at hξ`: the **context**). The lemma peels the top
term off a Taylor polynomial:

$$T_{n+1}(x) = T_n(x) + \big(((n+1)\cdot n!)^{-1} (x - x_0)^{n+1}\big) \cdot f^{(n+1)}_{s}(x_0),$$

where $f^{(k)}_s(x_0)$ is `iteratedDerivWithin k f s x₀`. On the numeral degree `2` Lean matches `2 = 1 + 1`, so
the new term is written with `1 + 1` and `Nat.factorial 1`. Rewrite once per degree (twice for degree 2, then
R11). Placeholders: `(f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (taylorWithinEval f 2 s a b)` | `⊢ P (taylorWithinEval f 1 s a b + (((↑1 + 1) * ↑(Nat.factorial 1))⁻¹ * (b - a) ^ (1 + 1)) • iteratedDerivWithin (1 + 1) f s a)` |

**R11 · `rw [taylor_within_zero_eval] at hξ`** changes the **context**: `taylorWithinEval f 0 s a b = f a`
(the degree-0 polynomial is the constant $f(a)$). Placeholders: as in R10.

| Before | After |
|---|---|
| `hξ : P (taylorWithinEval f 0 s a b) ⊢ P (f a)` | `hξ : P (f a) ⊢ P (f a)` |

### Coefficients: `iteratedDerivWithin` → `iteratedDeriv`

The Taylor coefficients come as `iteratedDerivWithin k f (uIcc x (x + h)) x`. For `+h` and `-h` the sets differ,
so the two expansions cannot cancel until every coefficient is the plain `iteratedDeriv k f x`. State each as a
`have` (`d1`, `d2`, and `d3` for degree 3) and prove it with R12 (its three arguments from milestone
`uniqueDiffOn_uIcc`, R13 + R14 + R15, R16); for `k = 1` add R17.

**R12 · `rw [iteratedDerivWithin_eq_iteratedDeriv hs hf ha]`** changes the **goal**. The lemma:
`UniqueDiffOn ℝ s → ContDiffAt ℝ n f a → a ∈ s → iteratedDerivWithin n f s a = iteratedDeriv n f a`.
Placeholders: `(f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `hs : UniqueDiffOn ℝ s, hf : ContDiffAt ℝ (↑n) f a, ha : a ∈ s ⊢ P (iteratedDerivWithin n f s a)` | `⊢ P (iteratedDeriv n f a)` |

**R13 · `hf.contDiffAt`** (`ContDiff.contDiffAt : ContDiff ℝ n f → ContDiffAt ℝ n f a`) **closes** the goal.
Placeholders: `(f : ℝ → ℝ) (n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `hf : ContDiff ℝ (↑n) f ⊢ ContDiffAt ℝ (↑n) f a` | no goals |

**R14 · `apply hf.of_le`** (`ContDiffAt.of_le : ContDiffAt ℝ n f a → m ≤ n → ContDiffAt ℝ m f a`) changes the
**goal**: a $C^n$ function is $C^m$ for $m \le n$; what is left is the order inequality. As a term:
`hf.contDiffAt.of_le (by norm_num)`. Placeholders: `(f : ℝ → ℝ) (m n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `hf : ContDiffAt ℝ (↑n) f a ⊢ ContDiffAt ℝ (↑m) f a` | `⊢ ↑m ≤ ↑n` |

**R15 · `norm_num`** **closes** an order between numerals in `WithTop ℕ∞`, such as the side goal of R14.

| Before | After |
|---|---|
| `⊢ ↑2 ≤ 3` | no goals |

**R16 · `left_mem_uIcc`** (`Set.left_mem_uIcc : a ∈ uIcc a b`) **closes** the goal. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ∈ uIcc a b` | no goals |

**R17 · `rw [iteratedDeriv_one]`** changes the **goal**: `iteratedDeriv 1 f = deriv f`. The statement of
`taylor2` uses `deriv f x`, so the `k = 1` coefficient needs this extra step. Placeholders: `(f : ℝ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (iteratedDeriv 1 f a)` | `⊢ P (deriv f a)` |

### Cleaning up and closing

**R18 · `norm_num [Nat.factorial] at hξ`** changes the **context**: it evaluates casts of numerals (`↑1 + 1 = 2`),
factorials (`Nat.factorial` unfolds because it is listed), `r • v = r * v`, and simplifies `a + c - a` to `c`.
Only run it after the `d`-rewrites (W4). Placeholders: `(a c d : ℝ)`.

| Before | After |
|---|---|
| `hξ : P ((((↑1 + 1) * ↑(Nat.factorial 1))⁻¹ * (a + c - a) ^ (1 + 1)) • d) ⊢ P (1 / 2 * c ^ 2 * d)` | `hξ : P (1 / 2 * c ^ 2 * d) ⊢ P (1 / 2 * c ^ 2 * d)` |

**R19 · `linear_combination hξ`** **closes** an equation `lhs = rhs` when `lhs - rhs` equals
`hξ.lhs - hξ.rhs` up to `ring`. Use it when the cleaned `hξ` is the goal rearranged.
Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `hξ : a - (b + c) = d ⊢ a = b + c + d` | no goals |

### Milestone `central_error_eq`: two expansions

Apply `taylor2` at `h` and at `-h` (`obtain ⟨ξ₂, h2⟩ := taylor2 f hf x (-h) (by linarith)`). The second one is
about `f (x + -h)`; the goal says `f (x - h)`.

**R20 · `rw [← sub_eq_add_neg] at h2`** changes the **context**. `sub_eq_add_neg : a - b = a + -b`, used right
to left. Placeholders: `(f : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `h : P (f (a + -b)) ⊢ P (f (a - b))` | `h : P (f (a - b)) ⊢ P (f (a - b))` |

Then `rw [h1, h2]` replaces `f (x + h)` and `f (x - h)` in the goal by their expansions.

**R21 · `field_simp`** changes the **goal**: it multiplies out every denominator, turning `A / B = C` into
`A = B * C` (in its own normal form). It must know each denominator is nonzero: it finds `hc : 0 < c` or
`c ≠ 0` in the context. Then `ring` (TACTIC_STATES) closes the polynomial identity. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ a / (2 * c) = b` | `⊢ a = 2 * c * b` |

### The main bound

**R22 · `rw [abs_mul]`** changes the **goal**: `abs_mul : |a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

A table cell cannot hold `|` here, so the states are listed one per line, before then after:

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R23 · `rw [abs_of_pos]`** changes the **goal list**: `abs_of_pos : 0 < a → |a| = a`, so the goal is rewritten and
a side goal `0 < a` is added. Write `rw [abs_of_pos (by positivity)]` to close it on the spot. Placeholders: `(a : ℝ)`.

Before, then the two goals after:

```lean-goal
⊢ P |a|
⊢ P a
⊢ 0 < a
```

**R24 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` where `e` is built from `+ * / ^`, numerals and
atoms it knows to be positive (from hypotheses such as `hc : 0 < c`). Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 < c ^ 2 / 7` | no goals |

**R25 · `have h12 := abs_add_le a b`** changes the **context**: the triangle inequality
`abs_add_le : |a + b| ≤ |a| + |b|`. Placeholders: `(a b : ℝ)`.

The goal `⊢ P` is unchanged; the context gains the line

```lean
h12 : |a + b| ≤ |a| + |b|
```

**R26 · `calc`** turns the **goal** `a ≤ c` into a chain `a ≤ b`, `_ = c`, each step with its own `:= proof`
(here `:= by gcongr; …` and `:= by ring`). Each `_` stands for the previous right-hand side. Indent the `_` lines
further than `calc`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a ≤ b, h₂ : b = c ⊢ a ≤ c` | no goals |

**R27 · `gcongr`** changes the **goal**: for `c * a ≤ c * b` it keeps the common factor and asks for `a ≤ b`; the
side goal `0 ≤ c` it proves itself with `positivity`. Works through `+`, `*`, `/` and more. Placeholders:
`(a b c d : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ c * a ≤ c * b` | `⊢ a ≤ b` |

**R28 · `linarith [t₁, t₂]`** **closes** the goal like R7, after adding the facts `t₁, t₂` (here instances of a
`∀`-hypothesis, `hM ξ₁` and `hM ξ₂`, plus `h12`, which is already in the context). `linarith` treats each
`|…|` as an unknown, so `h12 : |a + b| ≤ |a| + |b|`, `|a| ≤ M`, `|b| ≤ M` chain to `|a + b| ≤ M + M`.
Placeholders: `(g : ℝ → ℝ) (M a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ g a + g b ≤ M + M` (with `hM : ∀ (y : ℝ), g y ≤ M`) | no goals |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a degree-1 expansion** $f(b) = f(a) + (b-a) f'(a) + f''(\xi)(b-a)^2/2$, chaining R8 → `refine` → `hu`
(R2, R4) → `d1` (R12 with R13, R14, R15, R16, then R17) → R10, R11, `d1` at `hξ` → R18 → R19.
The states of `hξ`:

| Step | `hξ` |
|---|---|
| after R8 | `hξ : f b - taylorWithinEval f 1 (uIcc a b) a b = iteratedDeriv (1 + 1) f ξ * (b - a) ^ (1 + 1) / ↑(1 + 1).factorial ⊢ f b = f a + (b - a) * deriv f a + iteratedDeriv 2 f ξ * (b - a) ^ 2 / 2` |
| after R18 | `hξ : f b - (f a + (b - a) * deriv f a) = iteratedDeriv 2 f ξ * (b - a) ^ 2 / 2 ⊢ f b = f a + (b - a) * deriv f a + iteratedDeriv 2 f ξ * (b - a) ^ 2 / 2` |

Between them, `rw [taylorWithinEval_succ, taylor_within_zero_eval, d1] at hξ` leaves

```lean
hξ : f b - (f a + (((↑0 + 1) * ↑(Nat.factorial 0))⁻¹ * (b - a) ^ (0 + 1)) • deriv f a) =
       iteratedDeriv (1 + 1) f ξ * (b - a) ^ (1 + 1) / ↑(1 + 1).factorial
```

**W2: adding two expansions** cancels the odd term (in the exercise you subtract, or add for Part 2):

| Step | State |
|---|---|
| start | `h2 : f (x + -c) = f x - c * p + c ^ 2 * q ⊢ (f (x + c) + f (x - c)) / 2 - f x = c ^ 2 * q` |
| R20 | `h2 : f (x - c) = f x - c * p + c ^ 2 * q ⊢ (f (x + c) + f (x - c)) / 2 - f x = c ^ 2 * q` |

```lean-goal
⊢ (f x + c * p + c ^ 2 * q + (f x - c * p + c ^ 2 * q)) / 2 - f x = c ^ 2 * q
⊢ f x + c * p + c ^ 2 * q + (f x - c * p + c ^ 2 * q) - f x * 2 = c ^ 2 * q * 2
```

(after `rw [h1, h2]`, then after R21; `ring` closes it).

**W3: a bound through `|·|`**: R22 + R23 with R24, then R25, then R26 with R27 and R28 inside:

```lean-goal
⊢ |c / 3 * (g a + g b)| ≤ 2 * M * c / 3
⊢ c / 3 * |g a + g b| ≤ 2 * M * c / 3
```

**W4: the order trap.** `norm_num` (or `simp`) rewrites `iteratedDerivWithin 1 f s a` to `derivWithin f s a`:

| Before | After |
|---|---|
| `hξ : P (iteratedDerivWithin 1 f s a) ⊢ P (derivWithin f s a)` | `hξ : P (derivWithin f s a) ⊢ P (derivWithin f s a)` |

After that your `d1 : iteratedDerivWithin 1 f … = deriv f x` no longer matches anything in `hξ`.

---

## Part 2 · `second_difference_error`

Statement: if $f \in C^4$, $h > 0$ and $|f''''(y)| \le M$ for all $y$, then
$\left|\frac{f(x+h) - 2f(x) + f(x-h)}{h^2} - f''(x)\right| \le \frac{M h^2}{12}$.
No new entries: the same chain one degree higher.

- `taylor3`: as `taylor2` with `(n := 3)`, three R10 rewrites before R11, and a third coefficient
  `d3 : iteratedDerivWithin 3 f (uIcc x (x + h)) x = iteratedDeriv 3 f x` (R12–R16).
- `second_diff_error_eq`: as `central_error_eq` (R20, `rw [h1, h2]`, R21, `ring`). Adding the two expansions
  cancels $\pm h f'(x)$ and $\pm \frac{h^3}{6} f'''(x)$, leaving $\frac{h^4}{24}(f''''(\xi_1) + f''''(\xi_2))$
  on top of $h^2 f''(x)$.
- The bound: R22, R23 + R24, R25, R26 with R27 and R28, now with $h^2/24$ and $M h^2/12$.

---

## Traps

- **Order of the clean-up.** Rewrite every coefficient `iteratedDerivWithin k f (uIcc ..) x` with your `d1, d2(, d3)`
  *before* `norm_num [Nat.factorial] at hξ`; `norm_num` first turns `k = 1` into `derivWithin` (W4).
- The two expansions cancel only after all coefficients are `iteratedDeriv k f x` (or `deriv f x`): the sets
  `uIcc x (x + h)` and `uIcc x (x + -h)` differ, so the `Within` versions are different terms.
- After R10 the coefficients print as `iteratedDerivWithin (1 + 1) f …` and `iteratedDerivWithin (0 + 1) f …`.
  `d`-facts stated with `2` and `1` still rewrite them (Lean evaluates `1 + 1` on numerals), so state them with
  plain numerals; state `d1`'s right side as `deriv f x` (R17), since that is what `taylor2` mentions.
- `taylor2` at `-h` talks about `f (x + -h)`; rewrite it with R20 before `rw [h2]` into a goal with `f (x - h)`.
- `uniqueDiffOn_Icc` needs a strict `a < b`; for `h < 0` the interval `uIcc x (x + h)` is `Icc (x + h) x` (R3).
- `field_simp` needs `h ≠ 0` (or `0 < h`) in the context; otherwise it leaves the division.
- In `rw [abs_of_pos (by positivity)]` the positivity goal is the factor in front, `0 < h ^ 2 / 12`; write the
  error in the form `c * (…)` with `c` first, as the milestones do, so `abs_mul` splits off `|c|`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| case on `a ≠ b` | `rcases hab.lt_or_gt with h \| h` | R1 |
| `uIcc` → `Icc` | `rw [uIcc_of_le h.le]` / `rw [uIcc_of_ge h.le]` | R2, R3 |
| interval has unique derivatives | `exact uniqueDiffOn_Icc h` | R4 |
| prove `x ≠ x + h` from `h ≠ 0` | `intro e; apply hh; linarith` | R5, R6, R7 |
| `h ≠ 0`, `-h ≠ 0` from `0 < h` | `(by linarith)` | R7 |
| Taylor with remainder | `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) (x₀ := x) (x := x + h) hne hf.contDiffOn` | R8, R9 |
| unfold the Taylor polynomial | `rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval] at hξ` | R10, R11 |
| coefficient within → plain | `iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc` | R12–R16 |
| `iteratedDeriv 1 f` → `deriv f` | `rw [iteratedDeriv_one]` | R17 |
| evaluate numerals, factorials, `•` | `norm_num [Nat.factorial] at hξ` | R18 |
| goal = rearranged hypothesis | `linear_combination hξ` | R19 |
| `x + -h` → `x - h` | `rw [← sub_eq_add_neg] at h2` | R20 |
| clear denominators | `field_simp` then `ring` | R21 |
| split `\|c * e\|` with `c > 0` | `rw [abs_mul, abs_of_pos (by positivity)]` | R22–R24 |
| triangle inequality | `have h12 := abs_add_le a b` | R25 |
| chain `≤` and `=` | `calc … ≤ … := by gcongr; linarith [hM ξ₁, hM ξ₂]` then `_ = … := by ring` | R26–R28 |
| see the state | infoview | |
