# H091 · log Z is convex in β: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real exponential, logarithm and
real powers (`Real.exp`, `Real.log`, `Real.rpow`), finite sums `∑`, convexity (`ConvexOn`), Hölder's
inequality for finite sums, and physlib's `CanonicalEnsemble` with its partition function.

**The physics.** A finite canonical ensemble has microstates `i : ι` with energies `E i`. With `k_B = 1`
and inverse temperature `β`, the partition function is $Z(\beta) = \sum_i e^{-\beta E_i}$. The claim is
that $\beta \mapsto \log Z(\beta)$ is convex on all of ℝ: for weights $a, c \ge 0$ with $a + c = 1$,
$\log Z(a x + c y) \le a \log Z(x) + c \log Z(y)$. (Physically: $\partial_\beta^2 \log Z = \mathrm{Var}(E)
\ge 0$; here we avoid derivatives.) The route: **Hölder's inequality** for nonnegative $f_i, g_i$ and
exponents $p, q > 1$ with $1/p + 1/q = 1$ (*Hölder conjugates*) says
$\sum_i f_i g_i \le (\sum_i f_i^p)^{1/p} (\sum_i g_i^q)^{1/q}$. Take $p = 1/a$, $q = 1/c$,
$f_i = e^{-a x E_i}$, $g_i = e^{-c y E_i}$: then $f_i g_i = e^{-(a x + c y) E_i}$, $f_i^{1/a} = e^{-x E_i}$,
and Hölder reads $Z(a x + c y) \le Z(x)^a Z(y)^c$. Take logs.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that a `have` leaves untouched.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*); each entry says what it means.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

The problem has `open CanonicalEnsemble Real`, so names print without the `Real.` prefix.

| You see | It means |
|---|---|
| `rexp x` | `Real.exp x`, the real exponential $e^x$ |
| `log x` | `Real.log x`, the natural log. Total function: `log 0 = 0`, `log (-x) = log x`, so lemmas need `0 < x` or `x ≠ 0` |
| `x ^ y` with `y : ℝ` | `Real.rpow x y`, the real power ($= e^{y \log x}$ for `x > 0`). With `y : ℕ` it is the ordinary power |
| `p⁻¹`, `1 / a` | inverse and division in ℝ. Lean sets `1 / 0 = 0` and `0⁻¹ = 0` |
| `∑ i, f i` | $\sum_{i \in \iota} f(i)$ over all of a finite type (`Finset.univ`); needs `[Fintype ι]` |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι` |
| `Finset.univ`, `i ∈ Finset.univ` | the finite set of all elements of a `Fintype`; `∑ i, f i` is `∑ i ∈ Finset.univ, f i`. Membership is trivially true |
| `-(a * x) * e`, `-x * e` | unary minus binds tighter than `*`: `(-(a * x)) * e`, `(-x) * e` |
| `x_1` inside a sum | a bound variable renamed because `x` is already in the context; same as `i` |
| `CanonicalEnsemble ι` | physlib: a system with microstates `ι`; `[MeasurableSpace ι]` is required by its definition (unused here) |
| `𝓒.energy i` | the energy $E_i$ of microstate `i` |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | $Z(b) = \sum_i e^{-b E_i}$ (R12) |
| `inst✝ : Fintype ι`, `inst✝¹ : Nonempty ι` | type-class assumptions: `ι` is finite, `ι` has at least one element |
| `p.HolderConjugate q` | `Real.HolderConjugate p q`: `p, q` are Hölder conjugates, equivalently `1 < p ∧ p⁻¹ + q⁻¹ = 1` (R4; this forces `1 < q`) |
| `ConvexOn ℝ Set.univ f` | `f` is convex on the set of all reals (R15) |
| `Set.univ`, `x ∈ Set.univ` | the set of all elements; membership in it is trivially true |
| `a • x` | scalar `a` acting on `x`; for `a x : ℝ` it is `a * x` (R16) |
| `(fun b => log (…)) (a • x + c • y)` | a function applied to an argument, not yet substituted (left by R15); any `simp only` substitutes it (R16 does) |
| `x✝ : y ∈ Set.univ` | an unnamed hypothesis (you wrote `_`) |
| `case inl`, `case inr` | the two branches of an `∨` after `rcases` |
| `case refine_1`, `case calc_1`, `case hx` | goals left by `refine ⟨?_, ?_⟩`, by `calc` steps with `?_`, or by `apply`'s hypotheses |
| `case inr.inr.calc_1` | branch names stack up: second `rcases` branch twice, then the first `calc` step |

---

## Part 1 · `exp_rpow` (milestone)

Statement: `rexp (-(a * x) * e) ^ (1 / a) = rexp (-x * e)` for `0 < a`, i.e. $(e^{-a x e})^{1/a} = e^{-x e}$.
Merge the power into the exponent (R1), compare exponents (R2), clear `1 / a` (R3). W4 does the same on
`rexp (2 * a * u)`.

**R1 · `rw [← Real.exp_mul]`** changes the **goal**. The lemma is `Real.exp_mul : rexp (x * y) = rexp x ^ y`
(`^` is the real power); `←` uses it right to left. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x ^ y)` | `⊢ P (rexp (x * y))` |

**R2 · `congr 1`** changes the **goal**: `f u = f v` becomes `u = v` (one function application stripped).
It closes the new goal by itself when a hypothesis matches. Placeholders: `(u v : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp u = rexp v` | `⊢ u = v` |

**R3 · `field_simp`** changes the **goal**: it multiplies out denominators, using `a ≠ 0` (found from
`ha : 0 < a` in the context), and often closes the goal. Placeholders: `(u w a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ u / a = w` | `⊢ u = a * w` |

## Part 2 · `holderConjugate_weights` (milestone)

Statement: for `0 < a`, `0 < c`, `a + c = 1`, the exponents `1 / a` and `1 / c` are Hölder conjugates.
Rewrite the definition (R4), split the `∧` (TACTIC_STATES, `refine ⟨?_, ?_⟩`; the goals come in the order
`1 < 1 / a`, then `(1/a)⁻¹ + (1/c)⁻¹ = 1`). `1 < 1 / a` is `1 * a < 1` after R6, which R7 gets from `hc` and
`hac`. `(1/a)⁻¹ + (1/c)⁻¹ = 1` is `a + c = 1` after R5 (`simp [hac]` does R5 and uses `hac`).

**R4 · `rw [Real.holderConjugate_iff]`** changes the **goal**. The lemma is
`p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1`. Placeholders: `(p q : ℝ)`. W2 uses it on `3` and `3 / 2`.

| Before | After |
|---|---|
| `⊢ p.HolderConjugate q` | `⊢ 1 < p ∧ p⁻¹ + q⁻¹ = 1` |

**R5 · `simp only [one_div, inv_inv]`** changes the **goal**: `one_div : 1 / a = a⁻¹` and
`inv_inv : a⁻¹⁻¹ = a` together turn `(1 / a)⁻¹` into `a`. Plain `simp` uses both by itself.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 / a)⁻¹` | `⊢ P a` |

**R6 · `rw [lt_div_iff₀ hc]`** changes the **goal**. The lemma is `lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b)`
(stated for any ordered field; ℝ qualifies). Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ a < b / c` | `⊢ a * c < b` |

**R7 · `linarith`** **closes** a goal that is a linear combination of hypotheses (`=`, `≤`, `<` between
linear expressions over an ordered field). It treats nonlinear products such as `a * c` as atoms, but
multiplication by a numeral like `u * 1` is fine. Placeholders: `(u v : ℝ)`.

| Before | After |
|---|---|
| `h1 : u + v = 2, h2 : 0 < v ⊢ u * 1 < 2` | no goals |

## Part 3 · `holder_step` (milestone)

Statement: `Z(a * x + c * y) ≤ Z(x) ^ a * Z(y) ^ c` for `0 < a`, `0 < c`, `a + c = 1`. Get Hölder's
inequality as `key` (R8, with `holderConjugate_weights` and R9), simplify `key` with `exp_rpow`, R10 and R11,
unfold `Z` in the goal (R12), then match the goal against `key` (R13, R14, then R2 and `ring` on one summand).
After the `simp only [...] at key` the problem shows

```
key : ∑ x_1, rexp (-(a * x) * 𝓒.energy x_1 + -(c * y) * 𝓒.energy x_1) ≤
        (∑ x_1, rexp (-x * 𝓒.energy x_1)) ^ a * (∑ x, rexp (-y * 𝓒.energy x)) ^ c
```

and the unfolded goal differs only in the summand on the left: `rexp (-(a * x + c * y) * 𝓒.energy i)`.

**R8 · `have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s) (f := f) (g := g) hpq hf hg`** changes the
**context**: it adds Hölder's inequality. Arguments: `hpq : p.HolderConjugate q`, `hf : ∀ i ∈ s, 0 ≤ f i`,
`hg : ∀ i ∈ s, 0 ≤ g i`. Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℝ) (p q : ℝ)`. In the problem,
`s := Finset.univ` (the sum over all microstates) and `f`, `g` are `fun i => rexp (…)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `key : ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)` |

**R9 · `fun i _ => (Real.exp_pos _).le`** proves `∀ i ∈ s, 0 ≤ rexp (u i)`. `Real.exp_pos x : 0 < rexp x`, and
`.le` weakens `<` to `≤`. Pass it directly as `hf`/`hg` in R8, or `have` it (shown). Placeholders:
`{ι : Type} (s : Finset ι) (u : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hf : ∀ i ∈ s, 0 ≤ rexp (u i)` |

**R10 · `simp only [one_div_one_div] at key`** changes the **context**: `key` is rewritten, the goal is not.
The lemma is `one_div_one_div : 1 / (1 / a) = a`. In the problem it turns the outer exponents
`1 / (1 / a)` into `a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `key : P (1 / (1 / a)) ⊢ P a` | `key : P a ⊢ P a` |

**R11 · `simp only [← Real.exp_add] at key`** changes the **context**. The lemma is
`Real.exp_add : rexp (x + y) = rexp x * rexp y`; right to left it merges `f i * g i` into one exponential.
Placeholders: `(u v : ℝ)`.

| Before | After |
|---|---|
| `key : P (rexp u * rexp v) ⊢ P (rexp (u + v))` | `key : P (rexp (u + v)) ⊢ P (rexp (u + v))` |

In the same `simp only` put `exp_rpow _ _ _ ha` and `exp_rpow _ _ _ hc` (Part 1, instantiated for `a` and
for `c`): they rewrite `f i ^ (1 / a)` to `rexp (-x * 𝓒.energy i)`.

**R12 · `simp only [mathematicalPartitionFunctionBetaReal]`** changes the **goal**: it unfolds the
definition of `Z`. Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunctionBetaReal b)` | `⊢ P (∑ i, rexp (-b * 𝓒.energy i))` |

**R13 · `refine Eq.trans_le ?_ key`** changes the **goal**. The lemma is `Eq.trans_le : a = b → b ≤ c → a ≤ c`:
with `key : b ≤ c` it leaves `a = b`. Use it when the goal's right side already matches `key` and the
left sides are equal but not syntactically. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `key : b ≤ c ⊢ a ≤ c` | `⊢ a = b` |

**R14 · `refine Finset.sum_congr rfl fun i hi => ?_`** changes the **goal and the context**. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` says the index sets are
the same. You can put it in R13's `?_`. Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i = g i` |

Then `congr 1` (R2) strips `rexp`, and `ring` (TACTIC_STATES) proves
`-(a * x + c * y) * E = -(a * x) * E + -(c * y) * E`.

## Part 4 · `logZ_convex`

Statement: `ConvexOn ℝ Set.univ (fun b => log Z(b))`, given `[Nonempty ι]`. Unfold convexity (R15, R16), handle
the edge weights (R17, R18, `simp`: W1), get `0 < Z` (R19), then a two-step `calc` (R20): monotonicity of `log`
(R21) with `holder_step`, and the log of a product of powers (R22 → R23 → R24: W3). After R15 and R16 the
problem's goal is

```
⊢ log (𝓒.mathematicalPartitionFunctionBetaReal (a * x + c * y)) ≤
    a * log (𝓒.mathematicalPartitionFunctionBetaReal x) + c * log (𝓒.mathematicalPartitionFunctionBetaReal y)
```

**R15 · `refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩`** changes the **goal and the context**.
`ConvexOn 𝕜 s f` is the structure `Convex 𝕜 s ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ a b, 0 ≤ a → 0 ≤ b → a + b = 1 →
f (a • x + b • y) ≤ a • f x + b • f y`. `convex_univ : Convex 𝕜 Set.univ` fills the first half; the
`fun` binds the rest. Placeholders: `(f : ℝ → ℝ)`, here `𝕜 = ℝ`.

| Before | After |
|---|---|
| `⊢ ConvexOn ℝ Set.univ f` | `ha : 0 ≤ a, hb : 0 ≤ b, hab : a + b = 1 ⊢ f (a • x + b • y) ≤ a • f x + b • f y` |

**R16 · `simp only [smul_eq_mul]`** changes the **goal**: `smul_eq_mul : a • x = a * x` when the scalars act
on themselves (ℝ on ℝ). Placeholders: `(a x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • x)` | `⊢ P (a * x)` |

**R17 · `rcases ha.eq_or_lt with rfl | ha'`** changes the **goal list**. `LE.le.eq_or_lt : a ≤ b → a = b ∨ a < b`,
so `ha : 0 ≤ a` gives `0 = a ∨ 0 < a`. The pattern `rfl` substitutes `a := 0` in the first branch; the second
branch gets `ha' : 0 < a`. Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ P a` | `⊢ P 0`, `ha' : 0 < a ⊢ P a` |

**R18 · `obtain rfl : c = 1 := by linarith`** changes the **context** (and the goal): it proves `c = 1` (here
by R7) and substitutes `c := 1` everywhere. Placeholders: `(c : ℝ) (hc : 0 + c = 1)`.

| Before | After |
|---|---|
| `hc : 0 + c = 1 ⊢ P c` | `hc : 0 + 1 = 1 ⊢ P 1` |

In the problem, after `a = 0` and `c = 1` the goal is `log Z(0 * x + 1 * y) ≤ 0 * log Z(x) + 1 * log Z(y)`,
which `simp` closes (W1 shows the same on a generic `f`).

**Calling the milestones.** The `variable … (𝓒 : CanonicalEnsemble ι)` line of `section Milestones` adds `𝓒`
as an explicit first argument only to the milestones whose statement mentions `𝓒`. So `holder_step` is
called as `holder_step 𝓒 x y a c` followed by its three hypotheses (here `ha' hc' hac`, the strict ones from
R17), while `exp_rpow x e a ha` and `holderConjugate_weights a c ha hc hac` take no `𝓒`. `_` lets Lean
infer an explicit argument from the goal: `exp_rpow _ _ _ ha`.

**R19 · `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos`** changes the **context**. The physlib lemma
is `[Nonempty ι] → ∀ b, 0 < 𝓒.mathematicalPartitionFunctionBetaReal b` (a nonempty sum of positive
exponentials). Placeholders: `{ι : Type} [Nonempty ι] [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hZ : ∀ (b : ℝ), 0 < 𝓒.mathematicalPartitionFunctionBetaReal b` |

**R20 · `calc a ≤ b := ?_` / `_ = c := ?_`** changes the **goal list**: a chain of steps, each proved
separately (by a term after `:=`, by `by …`, or left as `?_` to become a goal). The relations combine
(`≤` then `=` gives `≤`). Indent the `_` lines under the first term. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

**R21 · `Real.log_le_log`** changes the **goal list** when `apply`ed: `log` is monotone on positive reals,
`Real.log_le_log : 0 < x → x ≤ y → log x ≤ log y`. Usually written as a term,
`Real.log_le_log hx hxy`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ log x ≤ log y` | `⊢ 0 < x`, `⊢ x ≤ y` |

**R22 · `(Real.rpow_pos_of_pos hx y).ne'`** proves `x ^ y ≠ 0`. `Real.rpow_pos_of_pos : 0 < x → ∀ y, 0 < x ^ y`,
and `h.ne'` turns `h : a < b` into `b ≠ a`. Placeholders: `(x y : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ G` | `hne : x ^ y ≠ 0 ⊢ G` |

**R23 · `rw [Real.log_mul hx hy]`** changes the **goal**: `Real.log_mul : x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y`.
Placeholders: `(x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`; in the problem `hx`, `hy` come from R22.

| Before | After |
|---|---|
| `⊢ P (log (x * y))` | `⊢ P (log x + log y)` |

**R24 · `rw [Real.log_rpow hx]`** changes the **goal**: `Real.log_rpow : 0 < x → ∀ y, log (x ^ y) = y * log x`
(real power). Placeholders: `(x y : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ P (log (x ^ y))` | `⊢ P (y * log x)` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: an edge weight.** For any `f : ℝ → ℝ`, `simp` closes

```lean-goal
⊢ f (0 * x + 1 * y) ≤ 0 * f x + 1 * f y
```

**W2: conjugate exponents 3 and 3/2.** R4, then `norm_num`:

```lean-goal
⊢ HolderConjugate 3 (3 / 2)
⊢ 1 < 3 ∧ 3⁻¹ + (3 / 2)⁻¹ = 1
```

**W3: log of a product of powers.** R22 inside R23, then R24 twice (the last `rw` closes the goal by `rfl`):

```lean-goal
⊢ log (u ^ s * v ^ t) = s * log u + t * log v
⊢ log (u ^ s) + log (v ^ t) = s * log u + t * log v
```

**W4: a power of an exponential.** R1, R2, R3 (`field_simp` closes the last goal):

```lean-goal
⊢ rexp (2 * a * u) ^ (1 / a) = rexp (2 * u)
⊢ rexp (2 * a * u * (1 / a)) = rexp (2 * u)
⊢ 2 * a * u * (1 / a) = 2 * u
```

---

## Traps

- **Edge weights first.** With `a = 0`, `1 / a = 0` in Lean, so `1 / a` and `1 / c` are not Hölder
  conjugates and `holder_step` needs `0 < a`, `0 < c`. Split `0 ≤ a` with R17 before anything else.
- `log` is total (`log 0 = 0`), so R21, R23, R24 all demand positivity or `≠ 0` hypotheses. Get them from
  `hZ` (R19) and R22.
- `x ^ y` must be the **real** power for R1, R22, R24. `Z x ^ a` with `a : ℝ` is; `x ^ 2` with a literal `2`
  is the natural-number power.
- `simp only [exp_rpow _ _ _ ha] at key` only fires if `key` literally contains
  `rexp (-(a * x) * …) ^ (1 / a)`: define `f` in R8 with exactly that shape, `fun i => Real.exp (-(a * x) * 𝓒.energy i)`.
- `rw [h]`/`simp only [...]` without `at key` acts on the goal, not on `key` (R10, R11).
- After `simp … at key`, bound variables may print as `x_1`: it is just a renamed `i`.
- `rcases … with rfl | h`: `rfl` replaces the variable everywhere, so the old `ha` becomes `ha : 0 ≤ 0`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `rexp u ^ y → rexp (u * y)` | `rw [← Real.exp_mul]` | R1 |
| `rexp u = rexp v → u = v` | `congr 1` | R2 |
| clear denominators | `field_simp` (needs `0 < a` or `a ≠ 0` in context) | R3 |
| unfold Hölder conjugate | `rw [Real.holderConjugate_iff]` | R4 |
| `(1 / a)⁻¹ → a` | `simp` (`one_div`, `inv_inv`) | R5 |
| `a < b / c → a * c < b` | `rw [lt_div_iff₀ hc]` | R6 |
| linear arithmetic | `linarith` | R7 |
| Hölder on a finite sum | `have key := Real.inner_le_Lp_mul_Lq_of_nonneg (s := …) (f := …) (g := …) hpq hf hg` | R8 |
| `0 ≤ rexp _` pointwise | `fun i _ => (Real.exp_pos _).le` | R9 |
| `1 / (1 / a) → a` in `key` | `simp only [one_div_one_div] at key` | R10 |
| `rexp u * rexp v → rexp (u + v)` | `simp only [← Real.exp_add]` | R11 |
| unfold `Z` | `simp only [mathematicalPartitionFunctionBetaReal]` | R12 |
| goal `a ≤ c` from `key : b ≤ c` | `refine Eq.trans_le ?_ key` | R13 |
| equal sums from equal summands | `Finset.sum_congr rfl fun i _ => ?_` | R14 |
| unfold convexity on ℝ | `refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩` | R15 |
| `a • x → a * x` | `simp only [smul_eq_mul]` | R16 |
| `0 ≤ a` → `a = 0` or `0 < a` | `rcases ha.eq_or_lt with rfl \| ha'` | R17 |
| substitute a forced value | `obtain rfl : c = 1 := by linarith` | R18 |
| `0 < Z b` | `𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R19 |
| chain `≤` and `=` | `calc` | R20 |
| `log` monotone | `Real.log_le_log hx hxy` | R21 |
| `x ^ y ≠ 0` | `(Real.rpow_pos_of_pos hx y).ne'` | R22 |
| `log (x * y)` | `rw [Real.log_mul hx hy]` | R23 |
| `log (x ^ y)` | `rw [Real.log_rpow hx]` | R24 |
| see the state | infoview | |
