# H055 · Coupon collector: expected time from waiting-time laws: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`,
`refine`, `constructor`, `ring`, `norm_num`, `fun x => …`, `∀ k < n, …`. **New here:** Mathlib's
measure-theoretic probability (`Measure`, `∫ … ∂μ`, `Integrable`, `Measure.map`, `HasLaw`,
`IsProbabilityMeasure`), the geometric law `geometricMeasure`, infinite sums `∑'` and `Summable`, the
type `unitInterval`, finite sums over `Finset.range`, and the tactics `linarith`, `field_simp`,
`exact_mod_cast`, `push_cast`, `omega`, `rcases`.

**The math, in symbols.** `n` coupon types, drawn uniformly. In phase `k` (`k` types already held,
`0 ≤ k < n`) a draw is new with probability $p_k = (n-k)/n$. Let $T_k$ be the number of *failed*
draws in phase `k` before the first new coupon. The exercise assumes only that $T_k$ has the geometric
law $\Pr(T_k = m) = (1-p_k)^m p_k$ for $m = 0, 1, 2, \dots$ (no independence). Then:

1. $\mathbb E[T_k] = \sum_{m \ge 0} m (1-p)^m p = p \cdot \frac{1-p}{p^2} = \frac{1-p}{p}$ (from
   $\sum_m m r^m = r/(1-r)^2$ for $|r| < 1$, with $r = 1 - p$).
2. $\mathbb E[T_k + 1] = \frac{1-p_k}{p_k} + 1 = \frac{1}{p_k} = \frac{n}{n-k}$.
3. Linearity: $\mathbb E\big[\sum_{k<n}(T_k+1)\big] = \sum_{k<n}\frac{n}{n-k}$. Reversing the order
   ($k \mapsto n-1-k$) gives $\sum_{k<n}\frac{n}{k+1} = n H_n$, with $H_n = \sum_{k<n} \frac{1}{k+1}$.

Lean splits this into five milestones (1 → mean of the law, 2 → its integrability, 3 → `p k ≠ 0`,
4 → integrability of `T k`, 5 → `E[T k + 1] = n/(n-k)`) and the main theorem.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `Q : Measure ℕ → Prop` for measures). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary
  goal that the step leaves alone.
- Lemmas that produce a fact (`hX.map_eq`, `hf.add hg`, …) are shown as `have h := …`, so the context
  gains `h` and you see its type. `hX.map_eq` is dot notation for `HasLaw.map_eq hX`.
- Placeholders are real-valued (`ℝ`) as in the exercise; `Ω : Type` with `[MeasurableSpace Ω]` is a
  sample space with its σ-algebra, `μ : Measure Ω` a measure on it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `p : ↑unitInterval` | a real number in `[0, 1]`, packaged with its proof: `unitInterval = Set.Icc 0 1`, a subset of `ℝ`, used as a type |
| `↑p` | the underlying real number of `p : unitInterval` (or the cast of a natural `n : ℕ` into `ℝ`) |
| `p.2.1`, `p.2.2` | the proofs `0 ≤ ↑p` and `↑p ≤ 1` carried by `p` (R2) |
| `↑0` with `0 : unitInterval` | the real number `0`; `Set.Icc.coe_zero` rewrites it (R20) |
| `Measure Ω`, `μ` | a measure on `Ω`; `[IsProbabilityMeasure μ]` says `μ Ω = 1` |
| `∫ (x : Ω), f x ∂μ` | the Lebesgue integral of `f : Ω → ℝ`; for a probability measure, the expectation $\mathbb E[f]$. It is `0` when `f` is not integrable |
| `μ[f]` | notation for `∫ ω, f ω ∂μ`; with a `fun` it prints as `∫ (x : Ω), (fun ω => …) x ∂μ` |
| `Integrable f μ` | `f` is measurable (almost everywhere) and `∫ ‖f‖ ∂μ < ∞` |
| `AEStronglyMeasurable f μ`, `AEMeasurable X μ` | measurability side conditions (up to a `μ`-null set); for functions out of `ℕ` they are free (R25) |
| `Measure.map X μ` | the pushforward of `μ` along `X : Ω → ℕ`: the distribution (law) of `X`, $A \mapsto \mu(X^{-1}A)$ |
| `HasLaw X ν μ` | `X` has law `ν` under `μ`: fields `hX.aemeasurable : AEMeasurable X μ` and `hX.map_eq : Measure.map X μ = ν` |
| `geometricMeasure p` | the measure on `ℕ` with mass `(1 - p) ^ n * p` at `n`: failures before the first success, success probability `p` |
| `μ.real Set.univ` | the measure of the whole space as a real number; `1` for a probability measure (R32) |
| `∑' (n : ℕ), f n` | the infinite sum (`tsum`); it is `0` when the series is not summable |
| `Summable f` | the series `∑ f n` converges (unconditionally) |
| `‖r‖` | the norm; on `ℝ` it is `\|r\|` (R5) |
| `a • b` | scalar multiplication; on `ℝ` it is `a * b` (R9) |
| `∑ k ∈ Finset.range n, f k` | the finite sum $\sum_{k=0}^{n-1} f(k)$; `s.sum g` is the same sum printed another way |
| `f ∘ X` | composition, `(f ∘ X) x = f (X x)` (R35) |
| `n - 1 - k` on `ℕ` | truncated subtraction: `0` when the result would be negative (R43) |
| `{Ω : Type*}`, printed `Ω : Type u_1` | `Ω` is any type, in any universe level `u_1` (types of types); read it as `Ω : Type` |
| `inst✝ : IsProbabilityMeasure μ` | an instance argument `[…]` from the statement, unnamed in the context |
| `this✝`, `hk✝`, `inst✝` | shadowed or unnamed hypotheses; still usable by tactics such as `linarith` and `field_simp` |
| `case a`, `case left`, `case right` | the name of the goal produced by `apply` (R3, R4) or `constructor` |

---

## Part 1 · `geometric_mean` (milestone 1)

Statement: for `p : unitInterval` with `p ≠ 0`, `∫ n, (n : ℝ) ∂(geometricMeasure p) = (1 - p) / p`:
the mean of the geometric law.

**R1 · `rw [integral_geometricMeasure hp]`** changes the **goal**: the integral over the geometric law
becomes a series. Statement: `p ≠ 0 → ∫ n, f n ∂geometricMeasure p = ∑' n, ((1 - ↑p) ^ n * ↑p) • f n`.
Placeholders: `(p : unitInterval) (hp : p ≠ 0) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (n : ℕ), f n ∂geometricMeasure p)` | `⊢ P (∑' (n : ℕ), ((1 - ↑p) ^ n * ↑p) • f n)` |

**R2 · `p.2.1`, `p.2.2`** change the **context**: `p : unitInterval` is a pair (value, proof of
`0 ≤ value ∧ value ≤ 1`), so `p.2.1` and `p.2.2` are the two bounds. Placeholders: `(p : unitInterval)`.

| Before | After `have h1 := p.2.1` | After `have h2 := p.2.2` |
|---|---|---|
| `⊢ 0 ≤ ↑p ∧ ↑p ≤ 1` | `h1 : 0 ≤ ↑p ⊢ 0 ≤ ↑p ∧ ↑p ≤ 1` | `h2 : ↑p ≤ 1 ⊢ 0 ≤ ↑p ∧ ↑p ≤ 1` |

**R3 · `apply Subtype.ext`** changes the **goal**: two elements of `unitInterval` are equal when their
real values are. Use it to turn `↑p = 0` (a real fact) into `p = 0` (what `hp : p ≠ 0` refutes). For `0 < ↑p`: after R4
the second goal is `0 ≠ ↑p`; `intro h` gives `h : 0 = ↑p` and goal `False` (R18), `apply hp` makes the
goal `p = 0`, R3 makes it `↑p = ↑0`, and `exact h.symm` closes it (`h.symm : ↑p = 0` is `h` flipped;
`↑(0 : unitInterval)` is the real `0` by definition). Placeholders: `(p q : unitInterval)`.

| Before | After |
|---|---|
| `⊢ p = q` | `⊢ ↑p = ↑q` |

**R4 · `apply lt_of_le_of_ne`** changes the **goal list**. Statement: `a ≤ b → a ≠ b → a < b`.
Placeholders: `(a b : ℝ)` (any partial order). In term mode: `lt_of_le_of_ne p.2.1 (fun h => …)`,
where `fun h => …` proves `0 ≠ ↑p` from `h : 0 = ↑p`.

| Before | After |
|---|---|
| `⊢ a < b` | `⊢ a ≤ b`, `⊢ a ≠ b` |

**R5 · `rw [Real.norm_eq_abs]`** changes the **goal**: `‖r‖ = |r|` on `ℝ`. Placeholders: `(r : ℝ)`.
Before and after:

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

**R6 · `rw [abs_lt]`** changes the **goal**. Statement: `|a| < b ↔ -b < a ∧ a < b`. Placeholders:
`(a b : ℝ)`. Follow it with `constructor` to get the two inequalities. Before and after:

```lean-goal
⊢ |a| < b
⊢ -b < a ∧ a < b
```

**R7 · `linarith [t]`** **closes** a goal that is a linear (in)equality (`<`, `≤`, `=`, `≠`, `False`)
following from the hypotheses plus the extra facts `t` in brackets. It treats products of unknowns as
atoms, so it cannot multiply inequalities. Placeholders: `(a b : ℝ) (hb : b ≤ 1) (ha : 0 < a)`.

| Before | After |
|---|---|
| `hb : b ≤ 1, ha : 0 < a ⊢ a - b > -1` | closed |

**R8 · `funext n`** changes the **goal and the context**: an equation of functions becomes an equation
at a fresh point `n`. Use it to prove a `have e : (fun n => …) = fun n => …`. Placeholders:
`(f g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `n : ℕ ⊢ f n = g n` |

**R9 · `rw [smul_eq_mul]`** changes the **goal**: `a • b = a * b`. `integral_geometricMeasure` states its
result with `•` because it works for vector-valued `f`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R10 · `rw [tsum_mul_left]`** changes the **goal**: a constant factor leaves the series. Statement:
`∑' x, a * f x = a * ∑' x, f x` (no summability needed). Placeholders: `(a : ℝ) (f : ℕ → ℝ)`. The
constant must be on the **left** of each summand, hence the rewrite `e` to `p * (n * (1 - p) ^ n)`.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), a * f n)` | `⊢ P (a * ∑' (x : ℕ), f x)` |

**R11 · `rw [tsum_coe_mul_geometric_of_norm_lt_one hr]`** changes the **goal**. Statement:
`‖r‖ < 1 → ∑' n, ↑n * r ^ n = r / (1 - r) ^ 2`. Placeholders: `(r : ℝ) (hr : ‖r‖ < 1)`. The summand
must be exactly `↑n * r ^ n`: cast first, power second.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), ↑n * r ^ n)` | `⊢ P (r / (1 - r) ^ 2)` |

**R12 · `rw [sub_sub_cancel]`** changes the **goal**. Statement: `a - (a - b) = b`. Placeholders:
`(a b : ℝ)` (any additive commutative group). With `r = 1 - p`, it turns `1 - (1 - ↑p)` into `↑p`.

| Before | After |
|---|---|
| `⊢ P (a - (a - b))` | `⊢ P b` |

**R13 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero,
using hypotheses such as `hb : 0 < b` or `hb : b ≠ 0` in the context. It may close the goal; otherwise
finish with `ring`. Placeholders: `(a b : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ b * (a / b ^ 2) = a / b` | closed |

**W1** (on `r = 1/2`): `∑' n, 3 * (↑n * (1/2) ^ n) = 6` by R5, R6, then R10 → R11 and `norm_num`:

```lean-goal
⊢ ∑' (n : ℕ), 3 * (↑n * (1 / 2) ^ n) = 6
⊢ 3 * (1 / 2 / (1 - 1 / 2) ^ 2) = 6
```

---

## Part 2 · `geometric_integrable` (milestone 2)

Statement: for `p ≠ 0`, `Integrable (fun n : ℕ => (n : ℝ)) (geometricMeasure p)`. Without it,
`integral_add` (R29) cannot be applied to `T k + 1`. After R14, prove `hp0` and then `hr` again as in
Part 1: a `have` belongs to one proof only, and `linarith` needs `hp0 : 0 < ↑p` for the half
`1 - ↑p < 1` of `hr`.

**R14 · `rw [integrable_geometricMeasure_iff hp]`** changes the **goal**: integrability against the
geometric law is summability of the weighted norms. Statement:
`p ≠ 0 → (Integrable f (geometricMeasure p) ↔ Summable fun n => (1 - ↑p) ^ n * ↑p * ‖f n‖)`.
Placeholders: `(p : unitInterval) (hp : p ≠ 0) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable f (geometricMeasure p)` | `⊢ Summable fun n => (1 - ↑p) ^ n * ↑p * ‖f n‖` |

**R15 · `rw [Real.norm_natCast]`** changes the **goal**: `‖(↑n : ℝ)‖ = ↑n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ‖↑n‖` | `⊢ P ↑n` |

**R16 · `summable_pow_mul_geometric_of_norm_lt_one k hr`** changes the **context**: it gives
`Summable fun n => ↑n ^ k * r ^ n` for `‖r‖ < 1`. Placeholders: `(r : ℝ) (hr : ‖r‖ < 1) (k : ℕ)`. For
`↑n` itself, take `k = 1` and write the summand as `↑n ^ 1 * r ^ n`.

| Before | After |
|---|---|
| `⊢ Summable fun n => ↑n ^ k * r ^ n` | `h : Summable fun n => ↑n ^ k * r ^ n ⊢ Summable fun n => ↑n ^ k * r ^ n` |

**R17 · `hf.mul_left a`** (`Summable.mul_left`) changes the **context**: a summable series times a
constant on the left is summable. Placeholders: `(f : ℕ → ℝ) (a : ℝ) (hf : Summable f)`.

| Before | After |
|---|---|
| `⊢ Summable fun i => a * f i` | `h : Summable fun i => a * f i ⊢ Summable fun i => a * f i` |

---

## Part 3 · `param_ne_zero` (milestone 3)

Statement: from `hp : ∀ k < n, (p k : ℝ) = (n - k) / n`, every `p k` with `k < n` is nonzero (since
`n - k > 0`). R1 and R14 need this as `hp`.

**R18 · `intro k hk h`** changes the **goal and the context**. `a ≠ b` is by definition `a = b → False`,
so after the bounded `∀ k < n` (which is `∀ k, k < n → …`) there is a third argument to introduce.
Placeholders: `(n : ℕ) (Q : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∀ k < n, Q k ≠ 0` | `k : ℕ, hk : k < n, h : Q k = 0 ⊢ False` |

**R19 · `exact_mod_cast hk`** **closes** a goal that is `hk` up to casts: here `↑k < ↑n` in `ℝ` from
`hk : k < n` in `ℕ`. Placeholders: `(k n : ℕ) (hk : k < n)`.

| Before | After |
|---|---|
| `hk : k < n ⊢ ↑k < ↑n` | closed |

**R20 · `rw [Set.Icc.coe_zero] at h`** changes the **context**: `↑(0 : unitInterval) = (0 : ℝ)`. After
`rw [h] at h0` with `h : p k = 0`, the hypothesis mentions `↑0`; this makes it the real `0`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `h : ↑0 = x ⊢ G` | `h : 0 = x ⊢ G` |

**R21 · `rw [eq_comm] at h`** changes the **context**: it flips an equation. Statement: `a = b ↔ b = a`.
Placeholders: `(a b : ℝ)`. Used so that `div_eq_zero_iff` (which needs `_ / _ = 0`) applies.

| Before | After |
|---|---|
| `h : a = b ⊢ G` | `h : b = a ⊢ G` |

**R22 · `rw [div_eq_zero_iff] at h`** changes the **context**. Statement: `a / b = 0 ↔ a = 0 ∨ b = 0`.
Placeholders: `(a b : ℝ)` (any field; note `x / 0 = 0` in Lean).

| Before | After |
|---|---|
| `h : a / b = 0 ⊢ G` | `h : a = 0 ∨ b = 0 ⊢ G` |

**R23 · `rcases h with h | h`** changes the **goal list and the context**: a disjunction gives one goal
per case. Placeholders: `(A B G : Prop) (h : A ∨ B)`. Follow it with `<;> linarith [...]` to close both.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h : A ⊢ G`, `h : B ⊢ G` |

**R24 · `Nat.cast_nonneg`** changes the **context**: `0 ≤ (↑k : ℝ)`. `linarith` does not know that a
cast natural is nonnegative; pass it as `linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]`. Placeholders:
`(k : ℕ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ↑k` | `h : 0 ≤ ↑k ⊢ 0 ≤ ↑k` |

---

## Part 4 · `waiting_time_integrable` (milestone 4)

Statement: every `fun ω => (T k ω : ℝ)` with `k < n` is integrable under `μ`. Integrability of `X`
under `μ` is integrability of the identity under the law of `X`: transport milestone 2 through `HasLaw`.

**R25 · `StronglyMeasurable.of_discrete.aestronglyMeasurable`** changes the **context**: any
`g : ℕ → ℝ` is `AEStronglyMeasurable` for any measure on `ℕ` (`ℕ` is countable and every subset is
measurable). Placeholders: `(g : ℕ → ℝ) (ν : Measure ℕ)`. Give the type with `have h : … := …`.

| Before | After |
|---|---|
| `⊢ AEStronglyMeasurable g ν` | `h : AEStronglyMeasurable g ν ⊢ AEStronglyMeasurable g ν` |

**R26 · `hX.aemeasurable`** changes the **context**: the measurability field of `hX : HasLaw X ν μ`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℕ) (ν : Measure ℕ)`.

| Before | After |
|---|---|
| `⊢ AEMeasurable X μ` | `h : AEMeasurable X μ ⊢ AEMeasurable X μ` |

**R27 · `refine (integrable_map_measure hg hX).1 ?_`** changes the **goal**. Statement:
`AEStronglyMeasurable g (map X μ) → AEMeasurable X μ → (Integrable g (map X μ) ↔ Integrable (g ∘ X) μ)`;
`.1` is the direction `→`. A goal `Integrable (fun ω => g (X ω)) μ` is accepted, since it is `g ∘ X` by
definition. Placeholders: as R26, plus `(g : ℕ → ℝ)`, `hg` from R25 (with `ν := Measure.map X μ`),
`hX` from R26.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => g (X ω)) μ` | `⊢ Integrable g (Measure.map X μ)` |

**R28 · `rw [hX.map_eq]`** changes the **goal**: the pushforward `Measure.map X μ` becomes the law `ν`.
Placeholders: as R26, `(Q : Measure ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ Q (Measure.map X μ)` | `⊢ Q ν` |

---

## Part 5 · `waiting_time_mean` (milestone 5)

Statement: for `k < n`, `μ[fun ω => (T k ω : ℝ) + 1] = n / (n - k)`. The integral starts as
`∫ (x : Ω), (fun ω => ↑(T k ω) + 1) x ∂μ`; `rw` with R29 sees through the `fun`.

**R29 · `rw [integral_add hf hg]`** changes the **goal**: linearity. Statement:
`Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`. Placeholders:
`(μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`. No independence needed.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω + g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R30 · `integrable_const c`** changes the **context**: a constant is integrable under a finite measure
(`[IsFiniteMeasure μ]`; a probability measure is one). Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c) μ` | `h : Integrable (fun x => c) μ ⊢ Integrable (fun x => c) μ` |

**R31 · `rw [integral_const]`** changes the **goal**. Statement: `∫ _, c ∂μ = μ.real Set.univ • c`.
Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), c ∂μ)` | `⊢ P (μ.real Set.univ • c)` |

**R32 · `rw [probReal_univ]`** changes the **goal**: `μ.real Set.univ = 1` under
`[IsProbabilityMeasure μ]`.

| Before | After |
|---|---|
| `⊢ P (μ.real Set.univ)` | `⊢ P 1` |

**R33 · `rw [one_smul]`** changes the **goal**: `1 • c = c`. Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 • c)` | `⊢ P c` |

**R34 · `hX.integral_comp (f := f) hf`** (`HasLaw.integral_comp`) changes the **context**: change of
variables, $\mathbb E_\mu[f(X)] = \mathbb E_\nu[f]$. Statement:
`HasLaw X ν μ → AEStronglyMeasurable f ν → ∫ x, (f ∘ X) x ∂μ = ∫ x, f x ∂ν`. Placeholders: as R26 and
`(f : ℕ → ℝ)`; `hf` is R25. Name `f` with `(f := fun m : ℕ => (m : ℝ))`: Lean cannot infer it.

| Before | After |
|---|---|
| `⊢ ∫ (x : Ω), (f ∘ X) x ∂μ = ∫ (m : ℕ), f m ∂ν` | goal unchanged; context gains `h : ∫ (x : Ω), (f ∘ X) x ∂μ = ∫ (x : ℕ), f x ∂ν` |

**R35 · `simp only [Function.comp_def] at h`** changes the **context**: `f ∘ X` becomes
`fun x => f (X x)`, and `simp` beta-reduces, so the left side of `h` matches the goal's `∫ … ↑(T k a) …`
and `rw [h]` works. Placeholders: `(X : Ω → ℕ) (f : ℕ → ℝ) (x : Ω)`. Under a binder (`∫ x, …`, `∀ x, …`) it works the same.

| Before | After |
|---|---|
| `h : (f ∘ X) x = 0 ⊢ G` | `h : f (X x) = 0 ⊢ G` |

After `rw [h1, milestone 1, hp k hk]` and R13 the leftover goal is pure algebra in `↑n`, `↑k`, closed by
`ring`.

**W2** (`X : Ω → ℝ` with `E[X] = 4`): `E[X + 5] = 9` by R29 (with R30), R31 → R32 → R33, `rw [hm]`,
`norm_num`:

```lean-goal
⊢ ∫ (ω : Ω), X ω + 5 ∂μ = 9
⊢ ∫ (a : Ω), X a ∂μ + ∫ (a : Ω), 5 ∂μ = 9
⊢ ∫ (a : Ω), X a ∂μ + 5 = 9
⊢ 4 + 5 = 9
```

**W4** (`X : Ω → ℕ` with any law `ν` of mean 7): R34 then R35 give `h1`; `rw [h1, hν]` closes
`∫ (ω : Ω), ↑(X ω) ∂μ = 7`.

---

## Part 6 · `coupon_collector`

Statement: `μ[fun ω => ∑ k ∈ Finset.range n, ((T k ω : ℝ) + 1)] = n * ∑ k ∈ Finset.range n, 1 / (k + 1)`.

**R36 · `Finset.mem_range`** changes the **context**. Statement: `k ∈ Finset.range n ↔ k < n`; `.1` is
`→`. The milestones take `k < n`, sums give `k ∈ Finset.range n`. Placeholders: `(k n : ℕ)`.

| Before | After |
|---|---|
| `hk : k ∈ Finset.range n ⊢ k < n` | `h : k < n ⊢ k < n` |

**R37 · `hf.add hg`** (`Integrable.add`) changes the **context**: a sum of integrable functions is
integrable. Lean states it for `f + g`, which is `fun ω => f ω + g ω` by definition. Placeholders: as
R29.

| Before | After |
|---|---|
| `⊢ Integrable (fun ω => f ω + g ω) μ` | `h : Integrable (f + g) μ ⊢ Integrable (fun ω => f ω + g ω) μ` |

**R38 · `rw [integral_finsetSum s hf]`** changes the **goal**: the integral of a finite sum is the sum of
integrals. Statement: `(∀ i ∈ s, Integrable (f i) μ) → ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ`.
Placeholders: `(s : Finset ℕ) (f : ℕ → Ω → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ)`. Write
`integral_finsetSum _ hint` and Lean reads `s` and `f` off `hint`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), ∑ i ∈ s, f i ω ∂μ)` | `⊢ P (∑ i ∈ s, ∫ (a : Ω), f i a ∂μ)` |

**R39 · `rw [Finset.sum_congr rfl hfg]`** changes the **goal**: every summand is rewritten by
`hfg : ∀ i ∈ s, f i = g i`, which may use `i ∈ s` (here: `k < n` for milestone 5). Statement of
`Finset.sum_congr`: `s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. Placeholders:
`(s : Finset ℕ) (f g : ℕ → ℝ)`. Lean prints the result as `s.sum g`, the same as `∑ i ∈ s, g i`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, f i)` | `⊢ P (s.sum g)` |

**R40 · `rw [Finset.mul_sum]`** changes the **goal**: a factor moves into the sum. Statement:
`a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Placeholders: `(s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

**R41 · `rw [← Finset.sum_range_reflect]`** changes the **goal**: it reverses the summation order.
Statement: `∑ j ∈ range n, f (n - 1 - j) = ∑ j ∈ range n, f j`. Placeholders: `(f : ℕ → ℝ) (n : ℕ)`.
Right to left it rewrites the **first** sum over `range n` it finds; put the sum you want reversed on
the left of the goal.

| Before | After |
|---|---|
| `⊢ P (∑ j ∈ Finset.range n, f j)` | `⊢ P (∑ j ∈ Finset.range n, f (n - 1 - j))` |

**R42 · `refine Finset.sum_congr rfl (fun k hk => ?_)`** changes the **goal and the context**: two sums
over the same set are equal when the summands are, term by term. Placeholders: `(s : Finset ℕ)
(f g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ k ∈ s, f k = ∑ k ∈ s, g k` | `k : ℕ, hk : k ∈ s ⊢ f k = g k` |

**R43 · `rw [Nat.cast_sub h]`** changes the **goal**: the cast of a truncated subtraction splits when it
does not truncate. Statement: `m ≤ n → ↑(n - m) = ↑n - ↑m`. Placeholders: `(m n : ℕ) (hmn : m ≤ n)`.
`n - 1 - k` is `(n - 1) - k`: the first `rw [Nat.cast_sub (by omega)]` splits the outer `- k`, the
second the inner `- 1`.

| Before | After |
|---|---|
| `⊢ P ↑(n - m)` | `⊢ P (↑n - ↑m)` |

**R44 · `omega`** **closes** linear arithmetic over `ℕ` and `ℤ`, truncated subtraction included, from the
hypotheses (e.g. `hk : k < n`). It does not work over `ℝ`. Placeholders: `(k n : ℕ) (hk : k < n)`.

| Before | After |
|---|---|
| `hk : k < n ⊢ 1 ≤ n - k` | closed |

**R45 · `push_cast`** changes the **goal**: casts move inward through `+`, `*`, … and casts of numerals
become numerals (`↑1` → `1`). Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(a + b + 1)` | `⊢ P (↑a + ↑b + 1)` |

The last goal, `↑n / (↑n - (↑n - 1 - ↑k)) = ↑n * (1 / (↑k + 1))`, is closed by `ring`: it simplifies
the denominator `↑n - (↑n - 1 - ↑k)` to `↑k + 1`, and both sides become `↑n * (↑k + 1)⁻¹`, so no nonzero
fact is needed.

**W3**: `∑ j ∈ range n, ↑(n - 1 - j) = ∑ j ∈ range n, ↑j` is one `rw [Finset.sum_range_reflect (fun j => (j : ℝ)) n]`:

```lean-goal
⊢ ∑ j ∈ Finset.range n, ↑(n - 1 - j) = ∑ j ∈ Finset.range n, ↑j
```

---

## Traps

- `HasLaw X ν μ` is a structure, not an equation: `rw [hX]` fails. Use its fields `hX.map_eq`
  (`Measure.map X μ = ν`) and `hX.aemeasurable`.
- `∫` of a non-integrable function is `0` and `∑'` of a non-summable series is `0`, so a wrong
  computation can still type-check. The integrability milestones are what make `integral_add` and
  `integral_finsetSum` usable.
- `tsum_mul_left` pulls out a constant on the **left** of the summand; `integral_geometricMeasure` puts
  the weight on the left of `•` and `↑n` on the right. Rewrite the summand first (`have e`, R8).
- `tsum_coe_mul_geometric_of_norm_lt_one` and `summable_pow_mul_geometric_of_norm_lt_one` need the norm
  form `‖1 - ↑p‖ < 1`, not `|1 - ↑p| < 1` or `0 < 1 - ↑p`. Prove it with R5, R6, `constructor`, R7,
  with `hp0 : 0 < ↑p` already in the context: `p.2.1` gives only `0 ≤ ↑p`, and the half `1 - ↑p < 1`
  fails without `hp0` (also in milestone 2).
- In `have hr : ‖(1 - p : ℝ)‖ < 1`, the type ascription `( … : ℝ)` matters: without it `1 - p` does
  not elaborate (`failed to synthesize HSub ℕ ↑unitInterval`): there is no subtraction between a
  numeral and a `unitInterval`.
- `n - 1 - k` and `n - k` are truncated on `ℕ`; `Nat.cast_sub` needs the inequality, and `push_cast`
  alone does not remove them.
- `field_simp` needs the nonzero facts as hypotheses in the context (`hp0 : 0 < ↑p`, `↑n - ↑k ≠ 0`,
  `↑n ≠ 0`); prove them with `have` before calling it.
- `linarith` does not use `0 ≤ ↑k` for a natural `k` on its own: supply `k.cast_nonneg` (R24).
- `t1 ; t2` runs `t2` on the first goal only. After `constructor` or `rcases`, use `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∫ f ∂geometricMeasure p` → series | `rw [integral_geometricMeasure hp]` | R1 |
| `0 ≤ ↑p`, `↑p ≤ 1` | `p.2.1`, `p.2.2` | R2 |
| `0 < ↑p` from `p ≠ 0` | `lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))` | R4, R3 |
| `‖1 - ↑p‖ < 1` (with `hp0` in context) | `rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]` | R5, R6, R7 |
| rewrite under `∑'` | `have e : (fun n => …) = fun n => … := by funext n; …; ring` | R8 |
| `a • b` → `a * b` | `rw [smul_eq_mul]` | R9 |
| constant out of `∑'` | `rw [tsum_mul_left]` | R10 |
| `∑' ↑n * r ^ n` | `rw [tsum_coe_mul_geometric_of_norm_lt_one hr]` | R11 |
| `a - (a - b)` → `b` | `rw [sub_sub_cancel]` | R12 |
| clear denominators | `field_simp` (then `ring`) | R13 |
| `Integrable f (geometricMeasure p)` | `rw [integrable_geometricMeasure_iff hp]` | R14 |
| `‖↑n‖` → `↑n` | `rw [Real.norm_natCast]` | R15 |
| `Summable (↑n ^ k * r ^ n)`, times `a` | `(summable_pow_mul_geometric_of_norm_lt_one k hr).mul_left a` | R16, R17 |
| prove `≠` | `intro … h` (goal `False`) | R18 |
| `↑k < ↑n` from `k < n` | `exact_mod_cast hk` | R19 |
| `↑(0 : unitInterval)` → `0` | `rw [Set.Icc.coe_zero] at h` | R20 |
| `a / b = 0` → cases | `rw [eq_comm, div_eq_zero_iff] at h; rcases h with h \| h` | R21, R22, R23 |
| `0 ≤ ↑k` | `k.cast_nonneg` | R24 |
| measurability of `ℕ → ℝ` | `StronglyMeasurable.of_discrete.aestronglyMeasurable` | R25 |
| integrable under `μ` ← under the law | `refine (integrable_map_measure hg hX.aemeasurable).1 ?_; rw [hX.map_eq]` | R27, R26, R28 |
| `E[f + g]` | `rw [integral_add hf hg]` | R29 |
| constants | `integrable_const c`, `rw [integral_const, probReal_univ, one_smul]` | R30–R33 |
| `E[f (X)]` = `∫ f ∂(law)` | `hX.integral_comp (f := …) …`, then `simp only [Function.comp_def] at h` | R34, R35 |
| `k ∈ range n` → `k < n` | `Finset.mem_range.1 hk` | R36 |
| integrable sum | `hf.add hg` | R37 |
| `∫ ∑` → `∑ ∫` | `rw [integral_finsetSum _ hint]` | R38 |
| rewrite each summand | `rw [Finset.sum_congr rfl (fun k hk => …)]` | R39 |
| `a * ∑` → `∑ a *` | `rw [Finset.mul_sum]` | R40 |
| reverse a sum over `range n` | `rw [← Finset.sum_range_reflect]` | R41 |
| equal sums termwise | `refine Finset.sum_congr rfl (fun k hk => ?_)` | R42 |
| `↑(n - m)` → `↑n - ↑m` | `rw [Nat.cast_sub (by omega)]` | R43, R44 |
| `↑1` → `1` etc. | `push_cast` | R45 |
| see the state | infoview | |
