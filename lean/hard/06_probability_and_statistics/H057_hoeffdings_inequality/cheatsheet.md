# H057 · Hoeffding's inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `apply`, `refine`, `rw`,
`simp`, `have`, `calc` (E020), `funext` (E022), `ring`.
**New here:** Mathlib's measure-theoretic probability: a probability measure `μ` on a sample space `Ω`,
measurable and integrable functions, "almost surely" (`∀ᵐ`), the expectation `μ[X]`, the moment
generating function `mgf`, independence `iIndepFun`, the probability of an event as a real number
`μ.real`; finite sums and products over `Finset.range n`; the norm `‖·‖`, `‖·‖₊` and `|·|` on `ℝ`; and
the tactics `convert`, `linarith`, `gcongr`, `positivity`, `field_simp`, `congr 1`.

**The maths.** Let `X₀, …, X_{n−1}` be independent, `Xᵢ ∈ [a, b]`, `E Xᵢ = 0`, `S = ∑ᵢ Xᵢ`, and write
`c = ((b − a)/2)²`. For `t ∈ ℝ` the *moment generating function* (mgf) is `M_Y(t) = E[e^{tY}]`.

1. **Hoeffding's lemma** (Mathlib, R3): `M_{Xᵢ}(t) ≤ exp(c t²/2)` for `t > 0`. MILESTONE `mgf_le`.
2. **Independence** (R10): `M_S(t) = ∏ᵢ M_{Xᵢ}(t) ≤ exp(c t²/2)ⁿ = exp(n c t²/2)`. MILESTONE `mgf_sum_le`.
3. **Chernoff** (R22): Markov's inequality applied to `e^{tS}` gives `P(S ≥ ε) ≤ e^{−tε} M_S(t)` for `t ≥ 0`,
   so `P(S ≥ ε) ≤ exp(−tε + n c t²/2)` for every `t > 0`. MILESTONE `tail_le_for_all_t`.
4. **Optimise `t`:** the exponent `φ(t) = −tε + n c t²/2` is a parabola with minimum at `t* = ε/(n c)`, where
   `φ(t*) = −ε²/(2 n c) = −2ε²/(n (b − a)²)`. That is `hoeffding`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a whole goal the step does not touch.
- Placeholders are written as Lean binders. `{Ω : Type} [MeasurableSpace Ω]` is a sample space with its
  σ-algebra (the family of measurable sets; Lean finds it by itself). `(μ : Measure Ω)
  [IsProbabilityMeasure μ]` is a measure with `μ Ω = 1`. In the guide all scalars are in `ℝ` and all
  index sets are `s : Finset ℕ` (a finite set of naturals, such as `Finset.range n = {0, …, n−1}`).
- States containing `|` (the absolute value, set-builder `{ω | …}`) are shown in ```` ```lean-goal ````
  blocks, because `|` would split a table cell.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω`, `μ : Measure Ω` | the sample space and the probability measure `P` on it |
| `{Ω : Type*}`, printed `Ω : Type u_1` | `Ω` is any type; `u_1` is a universe level you can ignore |
| `inst✝¹ : MeasurableSpace Ω` | the σ-algebra on `Ω` (an unnamed instance) |
| `inst✝ : IsProbabilityMeasure μ` | the instance `μ Ω = 1` (an unnamed hypothesis Lean uses by itself) |
| `X : ℕ → Ω → ℝ`, `X i ω` | a sequence of random variables; `X i ω` is the value of `Xᵢ` at the outcome `ω` |
| `Measurable X` | `X` is a random variable: preimages of Borel sets are measurable |
| `AEMeasurable X μ` | `X` agrees with a measurable function outside a `μ`-null set (weaker; R1) |
| `∀ᵐ (ω : Ω) ∂μ, p ω` | `p ω` holds almost surely: `μ {ω \| ¬ p ω} = 0` (R2) |
| `μ[X]`, printed `∫ (x : Ω), X x ∂μ` | the expectation `E X` (Bochner integral of `X` against `μ`) |
| `Integrable f μ` | `f` is measurable (a.e.) and `∫ \|f\| dμ < ∞` |
| `mgf X μ t` | the mgf `E[e^{t X}] = ∫ exp (t * X ω) dμ` (a real number) |
| `iIndepFun X μ` | the family `(X i)ᵢ` is mutually independent under `μ` |
| `μ.real {ω \| ε ≤ S ω}` | `P(S ≥ ε)` as a real number (`μ s` lives in `ℝ≥0∞ = [0, ∞]`; `μ.real s` is it converted to `ℝ`) |
| `Set.Icc a b` | the closed interval `[a, b]`; `x ∈ Set.Icc a b` is `a ≤ x ∧ x ≤ b` (R18) |
| `∑ i ∈ Finset.range n, X i ω` | the number `X 0 ω + … + X (n-1) ω` |
| `∑ i ∈ s, X i` | the **function** `X i₁ + … + X iₖ : Ω → ℝ` (pointwise sum; R9) |
| `∏ i ∈ s, f i` | the product of `f i` over `i ∈ s` |
| `∀ i ∈ s, p i` | `∀ i, i ∈ s → p i`; for `s = Finset.range n`, `i ∈ s` means `i < n` (`intro i hi` opens it) |
| `s.card` | the number of elements of the `Finset s` |
| `m • a` | `a + … + a` (`m` copies), `m : ℕ` (R21) |
| `↑n`, `↑m` | the natural number cast into `ℝ` |
| `‖x‖` | the norm of `x`; on `ℝ` it is `\|x\|` (R6) |
| `‖x‖₊`, `↑‖x‖₊` | the norm as an element of `ℝ≥0` (`NNReal`, the nonnegative reals), and its cast back into `ℝ` (R5) |
| `Real.exp x` | `eˣ`; `Real.exp x ^ m` is `(eˣ)ᵐ` (application binds tighter than `^`), `-t * ε` is `(-t) · ε` |
| `case h0`, `case refine_1`, `case hbc` | names of the goals `apply` / `refine` / `gcongr` created, in order |

---

## Part 1 · `mgf_le` (MILESTONE)

Statement: one variable `X` with `X ω ∈ [a, b]` for every `ω` and `μ[X] = 0` has
`mgf X μ t ≤ exp (((b - a) / 2) ^ 2 * t ^ 2 / 2)` for `t > 0`. Mathlib's Hoeffding lemma (R3) says exactly this,
except that it writes `↑‖b - a‖₊` where you want `b - a`, and it wants weaker hypotheses (R1, R2) than you have.

**R1 · `Measurable.aemeasurable`** **closes** the goal: `hY.aemeasurable : AEMeasurable Y μ` from
`hY : Measurable Y`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ)`.

| Before | After |
|---|---|
| `hY : Measurable Y ⊢ AEMeasurable Y μ` | closed by `exact hY.aemeasurable` |

**R2 · `Filter.Eventually.of_forall`** changes the **goal**: "everywhere" implies "almost everywhere", so
`∀ᵐ` becomes `∀`. As a term: `Filter.Eventually.of_forall h : ∀ᵐ ω ∂μ, p ω` from `h : ∀ ω, p ω`.
Placeholders: `(μ : Measure Ω) (p : Ω → Prop)`.

| Before | After `apply Filter.Eventually.of_forall` |
|---|---|
| `⊢ ∀ᵐ (ω : Ω) ∂μ, p ω` | `⊢ ∀ (x : Ω), p x` |

**R3 · `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`** (Hoeffding's lemma) changes the
**context** when used as `have h := … hY hb hm hs`. The lemma: for `[IsProbabilityMeasure μ]`,

`AEMeasurable Y μ → (∀ᵐ ω ∂μ, Y ω ∈ Set.Icc c d) → μ[Y] = 0 → 0 < s → mgf Y μ s ≤ Real.exp ((‖d - c‖₊ / 2) ^ 2 * s ^ 2 / 2)`.

`c d s : ℝ` are implicit: Lean reads them off `hb` and `hs`. It is `protected`, so write the full name.
Placeholders: `(Y : Ω → ℝ) (c d s : ℝ)`, a goal `G : Prop`.

| Before | After |
|---|---|
| `⊢ G` | `h : mgf Y μ s ≤ Real.exp ((↑‖d - c‖₊ / 2) ^ 2 * s ^ 2 / 2) ⊢ G` |

**R4 · `convert h using k`** changes the **goal list**: it closes the goal with `h` and leaves one goal
`(piece of goal) = (piece of h)` for each place where the two differ. `using k` limits the matching to depth
`k`; larger `k` gives smaller leftovers. It closes leftovers that `rfl` or an assumption proves.
Placeholders: `(u v w : ℝ)`, `h : Real.exp (u / 2 * w) ≤ 1`, goal with `v` in place of `u`.

| Before | After `convert h using 2` | After `convert h using 4` |
|---|---|---|
| `⊢ Real.exp (v / 2 * w) ≤ 1` | `⊢ v / 2 * w = u / 2 * w` | `⊢ v = u` |

In `mgf_le`, `convert h using 3` leaves `((b - a) / 2) ^ 2 * t ^ 2 = (↑‖b - a‖₊ / 2) ^ 2 * t ^ 2`: rewrite
the right side with R5 → R6 → R7, and `rw` closes the goal by `rfl`.

**R5 · `rw [coe_nnnorm]`** changes the **goal**. The lemma is `coe_nnnorm : ↑‖a‖₊ = ‖a‖`: the cast to `ℝ`
of the `ℝ≥0`-valued norm is the real-valued norm. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑‖x‖₊` | `⊢ P ‖x‖` |

**R6 · `rw [Real.norm_eq_abs]`** changes the **goal**. The lemma is `‖r‖ = |r|` for `r : ℝ`.
Placeholders: `(x : ℝ)`. Before, then after:

```lean-goal
⊢ P ‖x‖
⊢ P |x|
```

**R7 · `rw [abs_of_pos]`** changes the **goal list**. The lemma is `abs_of_pos : 0 < a → |a| = a`, so the
goal is rewritten and a side goal `0 < a` is added. Write `rw [abs_of_pos (by linarith)]` to prove it on
the spot. Placeholders: `(x : ℝ)`; `α = ℝ` (any ordered additive group). Before, then the two goals after:

```lean-goal
⊢ P |x|
⊢ P x
⊢ 0 < x
```

**R8 · `linarith`** **closes** a goal `t < 0`, `t ≤ 0`, `t = 0` (or `>`, `≥`) that follows from the
hypotheses by adding up multiples of them: linear arithmetic over ordered fields such as `ℝ`. It does not
multiply hypotheses together. Placeholders: `(c d : ℝ)`.

| Before | After |
|---|---|
| `hcd : c < d ⊢ 0 < d - c` | closed |

**W1** chains R5, R6, R7 + R8 on `↑‖x - 1‖₊ = x - 1` for `1 < x`:

```lean-goal
⊢ ↑‖x - 1‖₊ = x - 1
⊢ ‖x - 1‖ = x - 1
⊢ |x - 1| = x - 1
```

---

## Part 2 · `mgf_sum_le` (MILESTONE)

Statement: `mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ t ≤ exp (n * (((b - a) / 2) ^ 2 * t ^ 2 / 2))` for
`t > 0`. Rewrite the mgf of the sum as a product (R9, R10), the right side as a power (R11), and compare
factor by factor (R12, R13, Part 1), then close `∏ _ ∈ range n, c = c ^ n` with `simp` (R14, R15).

**R9 · `Finset.sum_apply`** changes the **goal**: `(∑ i ∈ s, f i) ω = ∑ i ∈ s, f i ω`, a sum of functions
evaluated at `ω` is the sum of the values. `simp` uses it by itself, so `funext ω; simp` proves
`(fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i`. You need that equation because R10 is stated for the sum of
functions. Placeholders: `(s : Finset ℕ) (f : ℕ → Ω → ℝ) (ω : Ω)`. Lean renames the bound `i` to `c`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, f i) ω)` | `⊢ P (∑ c ∈ s, f c ω)` |

**R10 · `rw [hind.mgf_sum hY]`** changes the **goal**. The lemma `iIndepFun.mgf_sum` (called with dot
notation on `hind : iIndepFun Y μ`): given `hY : ∀ i, Measurable (Y i)`, for every `s : Finset ℕ`,
`mgf (∑ i ∈ s, Y i) μ t = ∏ i ∈ s, mgf (Y i) μ t`: the mgf of an independent sum is the product of the mgfs.
Placeholders: `(Y : ℕ → Ω → ℝ) (s : Finset ℕ) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (mgf (∑ i ∈ s, Y i) μ t)` | `⊢ P (∏ i ∈ s, mgf (Y i) μ t)` |

**R11 · `rw [Real.exp_nat_mul]`** changes the **goal**. The lemma is `exp (↑m * x) = exp x ^ m` for
`m : ℕ`. Placeholders: `(x : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp (↑m * x))` | `⊢ P (Real.exp x ^ m)` |

After R9's equation, R10 and R11, the goal of `mgf_sum_le` is
`∏ i ∈ Finset.range n, mgf (X i) μ t ≤ Real.exp (((b - a) / 2) ^ 2 * t ^ 2 / 2) ^ n`.

**R12 · `Finset.prod_le_prod`** changes the **goal list**. The lemma:
`(∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ g i) → ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` (products of nonnegative
factors are monotone). Placeholders: `(s : Finset ℕ) (f g : ℕ → ℝ)`. As a term:
`Finset.prod_le_prod (fun i _ => …) (fun i _ => …)`, the `_` being the unused proof of `i ∈ s`.

| Before | After `apply Finset.prod_le_prod` |
|---|---|
| `⊢ ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` | `⊢ ∀ i ∈ s, 0 ≤ f i`, `⊢ ∀ i ∈ s, f i ≤ g i` |

**R13 · `mgf_nonneg`** **closes** `0 ≤ mgf Y μ t` (an integral of the positive function `exp`). All its
arguments are implicit. Placeholders: `(Y : Ω → ℝ) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ mgf Y μ t` | closed by `exact mgf_nonneg` |

**R14 · `rw [Finset.prod_const]`** changes the **goal**. The lemma is `∏ _x ∈ s, b = b ^ s.card` (the
factor does not depend on the index). Placeholders: `(s : Finset ℕ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∏ _i ∈ s, b)` | `⊢ P (b ^ s.card)` |

**R15 · `rw [Finset.card_range]`** changes the **goal**: `(Finset.range m).card = m`. Placeholders:
`(m : ℕ)`, `P : ℕ → Prop`.

| Before | After |
|---|---|
| `⊢ P (Finset.range m).card` | `⊢ P m` |

`simp` applies R14 and R15 by itself: in a `calc`, `_ = _ := by simp` closes
`∏ i ∈ Finset.range n, Real.exp u = Real.exp u ^ n`.

---

## Part 3 · `tail_le_for_all_t` (MILESTONE)

Statement: for every `t > 0`,
`μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ exp (-t * ε + n * (((b - a) / 2) ^ 2 * t ^ 2 / 2))`.
Chernoff (R22) needs `exp (t * S)` integrable: `S ω ∈ [n a, n b]` (R16–R21). Then bound the mgf with Part 2
(R24) and merge the exponentials (R25).

**R16 · `integrable_exp_mul_of_mem_Icc`** changes the **goal list**. The lemma: for a finite measure,
`AEMeasurable Y μ → (∀ᵐ ω ∂μ, Y ω ∈ Set.Icc a b) → Integrable (fun ω => Real.exp (t * Y ω)) μ`
(a bounded variable has every exponential moment). Lean would read the implicit bounds `a b` off the
`∀ᵐ` argument, but that argument is still `?_` (or built from `?_`), so name them: `(a := c) (b := d)`. The left `a` is the lemma's parameter name, the
right side is your value (in the exercise: `(a := n * a) (b := n * b)`).
Placeholders: `(Y : Ω → ℝ) (c d t : ℝ)`.

| Before | After `refine integrable_exp_mul_of_mem_Icc (a := c) (b := d) ?_ ?_` |
|---|---|
| `⊢ Integrable (fun ω => Real.exp (t * Y ω)) μ` | `⊢ AEMeasurable Y μ`, `⊢ ∀ᵐ (ω : Ω) ∂μ, Y ω ∈ Set.Icc c d` |

**R17 · `Finset.measurable_sum`** changes the **goal**. The lemma: `(s) → (∀ i ∈ s, Measurable (f i)) →
Measurable fun ω => ∑ i ∈ s, f i ω`. Then R1 gives `AEMeasurable`. Placeholders:
`(s : Finset ℕ) (f : ℕ → Ω → ℝ)`. As a term: `Finset.measurable_sum _ fun i _ => hf i`.

| Before | After `apply Finset.measurable_sum` |
|---|---|
| `⊢ Measurable fun ω => ∑ i ∈ s, f i ω` | `⊢ ∀ i ∈ s, Measurable (f i)` |

**R18 · `Set.mem_Icc`** (`x ∈ Set.Icc c d ↔ c ≤ x ∧ x ≤ d`) changes the **goal list**: membership in
`Set.Icc` *is* a conjunction, so `⟨?_, ?_⟩` splits it, and `hx.1 : c ≤ x`, `hx.2 : x ≤ d` take it apart.
Inside R2's term: `Filter.Eventually.of_forall fun ω => ⟨?_, ?_⟩`. Placeholders: `(x c d : ℝ)`.

| Before | After `refine ⟨?_, ?_⟩` |
|---|---|
| `⊢ x ∈ Set.Icc c d` | `⊢ c ≤ x`, `⊢ x ≤ d` |

In `tail_le_for_all_t` those two goals are `↑n * a ≤ ∑ i ∈ Finset.range n, X i ω` and
`∑ i ∈ Finset.range n, X i ω ≤ ↑n * b`.

**R19 · `Finset.sum_le_sum`** changes the **goal**. The lemma: `(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤
∑ i ∈ s, g i`. Placeholders: `(s : Finset ℕ) (f g : ℕ → ℝ)`.

| Before | After `apply Finset.sum_le_sum` |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `⊢ ∀ i ∈ s, f i ≤ g i` |

**R20 · `rw [Finset.sum_const]`** changes the **goal**. The lemma is `∑ _x ∈ s, b = s.card • b`.
Placeholders: `(s : Finset ℕ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ _i ∈ s, b)` | `⊢ P (s.card • b)` |

**R21 · `rw [nsmul_eq_mul]`** changes the **goal**. The lemma is `m • a = ↑m * a` (`m : ℕ`).
Placeholders: `(m : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (m • a)` | `⊢ P (↑m * a)` |

`simp` chains R20, R15, R21: `(n : ℝ) * a = ∑ i ∈ Finset.range n, a := by simp`. **W2** combines this with
R19 in a `calc` (first `≤` by R19, then `_ = m * d := by simp`), on the goal

```lean-goal
⊢ ∑ i ∈ Finset.range m, f i ≤ ↑m * d
```

**R22 · `measure_ge_le_exp_mul_mgf`** (Chernoff bound) changes the **goal list**. The lemma: for a finite
measure, `(ε : ℝ) → 0 ≤ t → Integrable (fun ω => Real.exp (t * Y ω)) μ →
μ.real {ω | ε ≤ Y ω} ≤ Real.exp (-t * ε) * mgf Y μ t`. Give `ε` explicitly. Placeholders:
`(Y : Ω → ℝ) (e t : ℝ)`. Before, then the two goals after `apply measure_ge_le_exp_mul_mgf e`:

```lean-goal
⊢ μ.real {ω | e ≤ Y ω} ≤ Real.exp (-t * e) * mgf Y μ t
⊢ 0 ≤ t
⊢ Integrable (fun ω => Real.exp (t * Y ω)) μ
```

In the exercise, `Y` is the function `fun ω => ∑ i ∈ Finset.range n, X i ω`, so the integrability goal reads
`Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ`: prove it first as a `have`.
**W3** writes R22 as one term for a single `Y` with values in `[-1, 1]`:
`measure_ge_le_exp_mul_mgf e ht.le (integrable_exp_mul_of_mem_Icc (a := -1) (b := 1) hY.aemeasurable (Filter.Eventually.of_forall hb))`.

**R23 · `LT.lt.le`** **closes** a `≤` goal from a `<` hypothesis: `ht.le : 0 ≤ t` from `ht : 0 < t`.
Placeholders: `(t : ℝ)`.

| Before | After |
|---|---|
| `ht : 0 < t ⊢ 0 ≤ t` | closed by `exact ht.le` |

**R24 · `gcongr`** changes the **goal**: for `c * A ≤ c * B` it reduces to `A ≤ B` ("generalised
congruence": peel off the common context of both sides, using monotonicity of `*`). The side goal
`0 ≤ c` it proves itself (with `positivity`). If a hypothesis is exactly the leftover `A ≤ B`, it closes the
goal with it; otherwise the leftover is your next goal (named `case hbc`, as in `tail_le_for_all_t`).
Placeholders: `(u A B : ℝ)`, `h : A - B ≤ 0` (finished by `linarith`).

| Before | After |
|---|---|
| `⊢ Real.exp u * A ≤ Real.exp u * B` | `⊢ A ≤ B` |

**R25 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is `exp (x + y) = exp x * exp y`; right to
left it merges two exponentials. As a term, `(Real.exp_add _ _).symm : exp x * exp y = exp (x + y)`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

**W4** (R25 forwards, then R24), on `t ^ 2 ≤ B`:

| Before | After `rw [Real.exp_add]` |
|---|---|
| `⊢ Real.exp (-t) * Real.exp (t ^ 2) ≤ Real.exp (-t + B)` | `⊢ Real.exp (-t) * Real.exp (t ^ 2) ≤ Real.exp (-t) * Real.exp B` |

then `gcongr` closes it: it peels `exp (-t) * ·` and then `exp` (monotone), leaving `t ^ 2 ≤ B`, which is `h`.

---

## Part 4 · `hoeffding`

Statement: for `0 < n`, `0 < ε`:
`μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-2 * ε ^ 2 / (n * (b - a) ^ 2))`.
Apply Part 3 at `t = ε / (n * ((b - a) / 2) ^ 2)` and show the two exponents are equal.

**R26 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` where `e` is built from `+`, `*`, `/`,
`^`, casts, `exp`, `√`, …; for an atom `x` it looks for a hypothesis `0 < x` (or `0 ≤ x`, `x ≠ 0`). For a cast
`↑m` of `m : ℕ` it uses `hm : 0 < m`. Placeholders: `(x y : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `hx : 0 < x, hy : 0 < y, hm : 0 < m ⊢ 0 < x / (↑m * y ^ 2)` | closed |

**R27 · `refine h₁.trans_eq ?_`** changes the **goal**. The lemma `LE.le.trans_eq : a ≤ b → b = c → a ≤ c`;
with `h₁ : A ≤ B` it leaves `B = C`. In the exercise `h₁` is Part 3 at the chosen `t` (with the `t` argument
written `_` and filled from the type of `ht`). Placeholders: `(A B C : ℝ)`.

| Before | After |
|---|---|
| `h₁ : A ≤ B ⊢ A ≤ C` | `⊢ B = C` |

**R28 · `congr 1`** changes the **goal**: `f x = f y` becomes `x = y` (one level of "equal functions on equal
arguments"). It closes the result itself if `rfl` or a hypothesis proves it. Placeholders: `(u v : ℝ)`,
`h : u - v = 0` (finished by `linarith`).

| Before | After |
|---|---|
| `⊢ Real.exp u = Real.exp v` | `⊢ u = v` |

**R29 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove `≠ 0` (from
hypotheses `0 < y`, `y ≠ 0`, and numerals) and simplifies, leaving an equation without `/`. Then `ring`
closes it. Placeholders: `(e y : ℝ)`, `he : 0 < e`, `hy : 0 < y`.

| Before | After |
|---|---|
| `⊢ -(e / y) * e + (e / y) ^ 2 * y / 2 = -e ^ 2 / (2 * y)` | `⊢ -2 + 1 = -1` |

In `hoeffding` the same happens: after R27 and R28 the goal is
`-(ε / (↑n * ((b - a) / 2) ^ 2)) * ε + ↑n * (((b - a) / 2) ^ 2 * (ε / (↑n * ((b - a) / 2) ^ 2)) ^ 2 / 2) = -2 * ε ^ 2 / (↑n * (b - a) ^ 2)`;
`field_simp` needs `0 < n`, `0 < b - a` (or `0 < ((b - a) / 2) ^ 2`) and `0 < ε` in the context, and leaves a
numeral identity for `ring`.

---

## Traps

- Hoeffding's lemma is `protected`: `mgf_le_of_mem_Icc_of_integral_eq_zero` alone is "unknown identifier" even
  after `open ProbabilityTheory`. Write `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`.
- `μ[X]` is printed as `∫ (x : Ω), X x ∂μ`. They are the same term; `hmean` fits R3's hypothesis directly.
- R3 gives `↑‖b - a‖₊`, not `b - a`. `exact h` fails; use `convert h using 3` (R4) and R5 → R6 → R7.
- R10 is about `mgf (∑ i ∈ s, X i) μ t` (sum of **functions**). The exercise has `fun ω => ∑ i ∈ …, X i ω`.
  `rw [hindep.mgf_sum hmeas]` fails until you rewrite with the equation from R9 (`funext ω; simp`).
- R12 needs the nonnegativity goal: an mgf is `≥ 0` by R13, not by `positivity`.
- In R16 the bounds must be named, `(a := ↑n * a)`; without them Lean cannot guess the interval.
- Shadowing: the exercise's variables `a b` have the same names as the lemma parameters `a b` in R16. In
  `(a := n * a)` the left `a` is the parameter, the right `a` is yours.
- `t` is a free choice: Part 3 holds for every `t > 0`; pick it only in Part 4. `positivity` (R26) proves
  `0 < ε / (↑n * ((b - a) / 2) ^ 2)` only if `hε`, `hn` and a fact `0 < b - a` (or `0 < ((b - a) / 2) ^ 2`) are in
  the context: prove those with `linarith` (R8) and `positivity` first.
- The names on the `BANNED:` line (Mathlib's sub-Gaussian `HasSubgaussianMGF` API, which proves Hoeffding
  outright) are rejected by the checker.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `AEMeasurable` from `Measurable` | `hmeas.aemeasurable` | R1 |
| `∀ᵐ ω ∂μ, p ω` from `∀ ω, p ω` | `Filter.Eventually.of_forall h` | R2 |
| Hoeffding's lemma | `have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hX hbd hmean ht` | R3 |
| goal almost equal to `h` | `convert h using k` | R4 |
| `↑‖x‖₊ → x` for `0 < x` | `rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by linarith)]` | R5–R8 |
| `(∑ f i) ω → ∑ f i ω` | `funext ω; simp` | R9 |
| mgf of an independent sum | `rw [hindep.mgf_sum hmeas]` | R10 |
| `exp (↑n * x) → exp x ^ n` | `rw [Real.exp_nat_mul]` | R11 |
| `∏ f ≤ ∏ g` | `Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => …)` | R12, R13 |
| `∏ _ ∈ range n, c = c ^ n`, `∑ _ ∈ range n, c = n * c` | `simp` | R14, R15, R20, R21 |
| `exp (t * Y)` integrable for bounded `Y` | `integrable_exp_mul_of_mem_Icc (a := …) (b := …) hX hbd` | R16 |
| measurability of a finite sum | `Finset.measurable_sum _ fun i _ => hmeas i` | R17 |
| prove / use `x ∈ Set.Icc c d` | `⟨?_, ?_⟩` / `hx.1`, `hx.2` | R18 |
| `∑ f ≤ ∑ g` | `Finset.sum_le_sum fun i _ => …` | R19 |
| Chernoff | `measure_ge_le_exp_mul_mgf ε ht.le hInt` | R22, R23 |
| `c * A ≤ c * B` from `A ≤ B` | `gcongr` | R24 |
| `exp x * exp y = exp (x + y)` | `(Real.exp_add _ _).symm` | R25 |
| `0 < expression` | `positivity` | R26 |
| `a ≤ b` and `b = c` | `refine h.trans_eq ?_` | R27 |
| `exp u = exp v` → `u = v` | `congr 1` | R28 |
| equation with denominators | `field_simp`, then `ring` | R29 |
| see the state | infoview | |
