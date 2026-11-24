# M096 · The exponential distribution is memoryless: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measures and probability
(`Measure`, `IsProbabilityMeasure`, `expMeasure`, `cdf`, conditional probability `μ[t | s]`), the
extended non-negative reals `ℝ≥0∞` with the cast `ENNReal.ofReal`, intervals `Set.Ioi`/`Set.Iic`,
`Real.exp`, and the closers `linarith`, `nlinarith`, `positivity`, `congr`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- `rw [← lemma]` uses an equation `lemma : L = R` right to left: it replaces `R` by `L`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Background in one paragraph

A **measure** `μ : Measure Ω` on a type `Ω` (with a σ-algebra, the instance `[MeasurableSpace Ω]`)
assigns to each set `s : Set Ω` a size `μ s : ℝ≥0∞`. `ℝ≥0∞` (Lean name `ENNReal`) is `[0, ∞]`; it has
`+`, `*`, `⁻¹` (with `0⁻¹ = ∞`) and a truncated `-` (`a - b = 0` when `b ≥ a`), so it is **not a ring**.
A **probability measure** (`[IsProbabilityMeasure μ]`) has `μ univ = 1`. `expMeasure r` is the law of
`T ~ Exp(r)` on `ℝ`, density $r e^{-r t}$ on $t \ge 0$; the event $\{T > x\}$ is the set `Set.Ioi x`.
**Measurable** sets (`MeasurableSet s`) are the ones in the σ-algebra; every interval is one.
`ENNReal.ofReal : ℝ → ℝ≥0∞` sends `p` to `p` if `p ≥ 0` and to `0` otherwise, so it respects `-`, `*`, `⁻¹`
only under sign conditions (R9, R19, R21).

## Reading the goals

| You see | It means |
|---|---|
| `expMeasure r` | the exponential distribution `Exp(r)`, a `Measure ℝ` |
| `(expMeasure r) (Set.Ioi x)` | `P(T > x)` for `T ~ Exp(r)`, a value in `ℝ≥0∞` |
| `Set.Ioi x`, `Set.Iic x` | the intervals `(x, ∞) = {y \| x < y}` and `(-∞, x] = {y \| y ≤ x}` |
| `Set.univ` | the whole space as a set (here all of `ℝ`) |
| `sᶜ` | the complement of the set `s`; `(expMeasure r) (Set.Iic x)ᶜ` is `μ` applied to `(Iic x)ᶜ` |
| `s ∩ t` | intersection of sets |
| `1 - a`, `a⁻¹` with `a : ℝ≥0∞` | truncated subtraction (`0` when `a ≥ 1`) and inverse (`0⁻¹ = ∞`) in `ℝ≥0∞`, not real arithmetic |
| `ENNReal.ofReal y⁻¹` | `ENNReal.ofReal (y⁻¹)`: the postfix `⁻¹` attaches to the argument `y`; compare `(ENNReal.ofReal y)⁻¹` |
| `ENNReal`, `ℝ≥0∞` | `[0, ∞]`; `ℝ≥0∞` needs `open scoped ENNReal` to print |
| `ENNReal.ofReal p` | the real `p` cast into `ℝ≥0∞` (negative numbers become `0`) |
| `↑(cdf μ) x` | `cdf μ x = P(T ≤ x)`, a real number; `↑` is the coercion of the `StieltjesFunction` `cdf μ` to a function `ℝ → ℝ` |
| `μ[t \| s]` | the conditional probability `P(t \| s) = μ (s ∩ t) / μ s` (`ProbabilityTheory.cond`) |
| `max a b` | the maximum (some lemmas print it as `a ⊔ b`) |
| `Real.exp x` | $e^x$ |
| `- -x` | `-(-x)`, not yet simplified |
| `this : IsProbabilityMeasure (expMeasure r)` | the instance added by `haveI := …` (R1) |
| `inst✝ : …` | an instance argument with no name |

---

## Part 1 · `exp_tail`

Statement: for `0 < r` and `0 ≤ x`, `P(T > x) = ofReal (e^{-r x})`. Route:
$P(T > x) = 1 - P(T \le x) = 1 - \mathrm{cdf}(x) = 1 - (1 - e^{-rx})$, all of it moved inside one
`ofReal` so that real arithmetic (`ring`) can finish.

**R1 · `haveI := isProbabilityMeasure_expMeasure hr`** changes the **context**: it adds the instance
`this : IsProbabilityMeasure (expMeasure r)`. The lemma is `0 < r → IsProbabilityMeasure (expMeasure r)`;
because it needs the hypothesis `hr`, Lean cannot find the instance by itself, and R3 and R5 ask for it.
Placeholders: `(r : ℝ) (hr : 0 < r)`.

| Before | After |
|---|---|
| `⊢ (expMeasure r) Set.univ = 1` | `this : IsProbabilityMeasure (expMeasure r) ⊢ (expMeasure r) Set.univ = 1` |

**R2 · `rw [← Set.compl_Iic]`** changes the **goal**. The lemma is `Set.compl_Iic : (Iic a)ᶜ = Ioi a`;
right to left it writes the tail event as the complement of the cdf event. Placeholders:
`{α : Type} [LinearOrder α] (a : α)` (`ℝ`, `ℕ`, `ℤ` are linear orders).

| Before | After |
|---|---|
| `⊢ P (Set.Ioi a)` | `⊢ P (Set.Iic a)ᶜ` |

**R3 · `rw [prob_compl_eq_one_sub]`** changes the **goal list**. The lemma is
`prob_compl_eq_one_sub : MeasurableSet s → μ sᶜ = 1 - μ s` for `[IsProbabilityMeasure μ]`. Without the
argument, the side goal `MeasurableSet s` is added; write `rw [prob_compl_eq_one_sub hs]` (or with R4)
to supply it. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)`.

| Before | After |
|---|---|
| `⊢ P (μ sᶜ)` | `⊢ P (1 - μ s)`, `⊢ MeasurableSet s` |

**R4 · `measurableSet_Iic`** **closes** `MeasurableSet (Set.Iic a)`. Use it as the argument of R3.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ MeasurableSet (Set.Iic a)` | closed |

**R5 · `rw [← ofReal_cdf]`** changes the **goal**. The lemma is
`ofReal_cdf : ENNReal.ofReal (cdf μ x) = μ (Set.Iic x)` for `μ : Measure ℝ` with `[IsProbabilityMeasure μ]`;
right to left it turns the measure of `(-∞, x]` into the cdf, a real number inside `ofReal`.
Placeholders: `(μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (μ (Set.Iic x))` | `⊢ P (ENNReal.ofReal (↑(cdf μ) x))` |

**R6 · `rw [cdf_expMeasure_eq hr]`** changes the **goal**. The lemma is
`cdf_expMeasure_eq : 0 < r → cdf (expMeasure r) x = if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0`.
Placeholders: `(r x : ℝ) (hr : 0 < r)`.

| Before | After |
|---|---|
| `⊢ P (↑(cdf (expMeasure r)) x)` | `⊢ P (if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0)` |

**R7 · `rw [if_pos hc]`** changes the **goal**. The lemma is `if_pos : c → (if c then a else b) = a`.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (hc : c) (a b : α)`. (`if_neg` is the `¬c` version.)

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `⊢ P a` |

**R8 · `rw [← ENNReal.ofReal_one]`** changes the **goal**. The lemma is `ENNReal.ofReal 1 = 1`; right to left
it rewrites **every** `1 : ℝ≥0∞` in the goal (real `1`s are untouched). This makes `1 - ofReal q` a difference
of two casts, the shape R9 needs.

| Before | After |
|---|---|
| `⊢ P 1` | `⊢ P (ENNReal.ofReal 1)` |

**R9 · `rw [← ENNReal.ofReal_sub p hq]`** changes the **goal**. The lemma is
`ENNReal.ofReal_sub (p : ℝ) {q : ℝ} : 0 ≤ q → ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q`.
The first argument `p` is explicit; write `_` to let `rw` find it. The proof of `0 ≤ q` is built from R10–R12.
Placeholders: `(p q : ℝ) (hq : 0 ≤ q)`.

| Before | After |
|---|---|
| `⊢ P (ENNReal.ofReal p - ENNReal.ofReal q)` | `⊢ P (ENNReal.ofReal (p - q))` |

**R10 · `sub_nonneg.mpr`** changes the **goal**. The lemma is the iff `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`;
`.mpr` is its right-to-left direction `b ≤ a → 0 ≤ a - b`, so `apply sub_nonneg.mpr` leaves `b ≤ a`, and
`sub_nonneg.mpr h` is a proof term. Placeholders: `{α : Type} [AddGroup α] [LE α] [AddRightMono α] (a b : α)`
(an additive group whose order is preserved by adding on the right; `ℝ` and `ℤ` qualify).

| Before | After |
|---|---|
| `⊢ 0 ≤ a - b` | `⊢ b ≤ a` |

**R11 · `Real.exp_le_one_iff.mpr`** changes the **goal**. The lemma is
`Real.exp_le_one_iff : Real.exp x ≤ 1 ↔ x ≤ 0`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.exp x ≤ 1` | `⊢ x ≤ 0` |

**R12 · `nlinarith`** **closes** an inequality over an ordered field such as `ℝ` that follows from the
hypotheses after multiplying pairs of them (here `0 < a` and `0 ≤ b` give `0 ≤ a * b`). Use it as
`(by nlinarith)` inside a term. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 ≤ b ⊢ -(a * b) ≤ 0` | closed |

**R13 · `congr 1`** changes the **goal**: an equation `f a = f b` between two applications of the same
function becomes `a = b`. Use it to drop the `ENNReal.ofReal` on both sides, so the rest is a real identity
for `ring`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ ENNReal.ofReal (a + b) = ENNReal.ofReal (b + a)` | `⊢ a + b = b + a` |

**Finish:** `ring` (TACTIC_STATES, "Closing"). It treats `Real.exp (…)` as an unknown, so
`1 - (1 - e) = e` is fine for it.

**W4: the end of a tail-style proof.** After `congr 1`:

```lean-goal
⊢ ENNReal.ofReal (1 - (1 - a)) = ENNReal.ofReal a
⊢ 1 - (1 - a) = a
```

**W1: the cdf in `ℝ≥0∞`** (R1, R5, R6, R7, on `Iic` instead of `Ioi`). The final `rw [if_pos hy]` leaves
`ofReal X = ofReal X`, which `rw` closes by `rfl`:

```lean-goal
⊢ (expMeasure k) (Set.Iic y) = ENNReal.ofReal (1 - Real.exp (-(k * y)))
⊢ ENNReal.ofReal (↑(cdf (expMeasure k)) y) = ENNReal.ofReal (1 - Real.exp (-(k * y)))
⊢ ENNReal.ofReal (if 0 ≤ y then 1 - Real.exp (-(k * y)) else 0) = ENNReal.ofReal (1 - Real.exp (-(k * y)))
```

---

## Part 2 · `exp_memoryless`

Statement: for `0 < r` and `0 ≤ s, t`, `P(T > s + t | T > s) = P(T > t)`. Route:
$P(T > s+t \mid T > s) = P(T > s)^{-1} \cdot P(\{T > s\} \cap \{T > s+t\}) = P(T>s)^{-1} P(T > s+t)$; then
`exp_tail` three times turns all three into `ofReal (exp …)`, and R19–R24 merge the left side into one
`ofReal (exp (…))`.

**R14 · `rw [cond_apply hs]`** changes the **goal**. The lemma is
`cond_apply : MeasurableSet s → ∀ μ t, μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)` (`μ[t | s]` is notation for
`ProbabilityTheory.cond μ s t`; it needs `open ProbabilityTheory`). Note the order: the conditioning
event `s` comes first in `s ∩ t`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω) (hs : MeasurableSet s)`.
Before and after:

```lean-goal
⊢ P μ[t | s]
⊢ P ((μ s)⁻¹ * μ (s ∩ t))
```

**R15 · `measurableSet_Ioi`** **closes** `MeasurableSet (Set.Ioi a)`. Use it as the argument of R14.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ MeasurableSet (Set.Ioi a)` | closed |

**R16 · `rw [Set.Ioi_inter_Ioi]`** changes the **goal**. The lemma is
`Set.Ioi_inter_Ioi : Ioi a ∩ Ioi b = Ioi (max a b)`. Placeholders: `{α : Type} [LinearOrder α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (Set.Ioi a ∩ Set.Ioi b)` | `⊢ P (Set.Ioi (max a b))` |

**R17 · `rw [max_eq_right hab]`** changes the **goal**. The lemma is `max_eq_right : a ≤ b → max a b = b`
(`max_eq_left : b ≤ a → max a b = a`). Placeholders: `{α : Type} [LinearOrder α] (a b : α) (hab : a ≤ b)`.

| Before | After |
|---|---|
| `⊢ P (max a b)` | `⊢ P b` |

**R18 · `linarith`** **closes** a linear (in)equality over an ordered field such as `ℝ` that follows from the
hypotheses by adding them up. Use it as `(by linarith)` for the side conditions `s ≤ s + t` and `0 ≤ s + t`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hb : 0 ≤ b ⊢ a ≤ a + b` | closed |

**Then `rw [exp_tail r (s + t) hr (by linarith), …]`:** your Part 1 theorem used as a rewrite rule
(TACTIC_STATES, `rw [lemma (by tac)]`). Give it all its arguments: the point `x` decides which
`expMeasure r (Set.Ioi x)` it rewrites.

**R19 · `rw [← ENNReal.ofReal_inv_of_pos hx]`** changes the **goal**. The lemma is
`ENNReal.ofReal_inv_of_pos : 0 < x → ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹`; right to left it moves `⁻¹`
inside the cast. Note `ENNReal.ofReal x⁻¹` means `ofReal (x⁻¹)`. Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ P (ENNReal.ofReal x)⁻¹` | `⊢ P (ENNReal.ofReal x⁻¹)` |

**R20 · `Real.exp_pos`** **closes** `0 < Real.exp x`. The lemma is `Real.exp_pos (x : ℝ) : 0 < Real.exp x`;
pass it (with `_` for `x`) as the argument of R19. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < Real.exp x` | closed |

**R21 · `rw [← ENNReal.ofReal_mul hp]`** changes the **goal**. The lemma is
`ENNReal.ofReal_mul : 0 ≤ p → ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q`; only the
**left** factor needs a sign condition. Placeholders: `(p q : ℝ) (hp : 0 ≤ p)`.

| Before | After |
|---|---|
| `⊢ P (ENNReal.ofReal p * ENNReal.ofReal q)` | `⊢ P (ENNReal.ofReal (p * q))` |

**R22 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) by looking at the shape of `e`:
exponentials, squares, inverses and products of positive things. Use it as `(by positivity)` for R21's
`0 ≤ (Real.exp …)⁻¹`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ (Real.exp x)⁻¹` | closed |

**R23 · `rw [← Real.exp_neg]`** changes the **goal**. The lemma is `Real.exp_neg : Real.exp (-x) = (Real.exp x)⁻¹`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x)⁻¹` | `⊢ P (Real.exp (-x))` |

**R24 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is
`Real.exp_add : Real.exp (x + y) = Real.exp x * Real.exp y`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

**R25 · `congr 2`** changes the **goal**: `f (g a) = f (g b)` becomes `a = b`, stripping `ENNReal.ofReal`
and then `Real.exp`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ ENNReal.ofReal (Real.exp (a + b)) = ENNReal.ofReal (Real.exp (b + a))` | `⊢ a + b = b + a` |

**Finish:** `ring` on the exponents.

**W2: a quotient of exponentials, merged** (R19 with R20, R21 with R22, R23, R24, R25, then `ring`):

```lean-goal
⊢ (ENNReal.ofReal (Real.exp a))⁻¹ * ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp (b - a))
⊢ ENNReal.ofReal (Real.exp a)⁻¹ * ENNReal.ofReal (Real.exp b) = ENNReal.ofReal (Real.exp (b - a))
⊢ ENNReal.ofReal ((Real.exp a)⁻¹ * Real.exp b) = ENNReal.ofReal (Real.exp (b - a))
⊢ ENNReal.ofReal (Real.exp (-a) * Real.exp b) = ENNReal.ofReal (Real.exp (b - a))
⊢ ENNReal.ofReal (Real.exp (-a + b)) = ENNReal.ofReal (Real.exp (b - a))
⊢ -a + b = b - a
```

**W3: nested tails under any measure `μ : Measure ℝ`** (R14 with R15, R16, R17 with R18), for `a ≤ b`:

```lean-goal
⊢ μ[Set.Ioi b | Set.Ioi a] = (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi b)
⊢ (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi a ∩ Set.Ioi b) = (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi b)
⊢ (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi (max a b)) = (μ (Set.Ioi a))⁻¹ * μ (Set.Ioi b)
```

---

## Traps

- `ring` cannot see through `ENNReal.ofReal`, and `ℝ≥0∞` is not a ring (truncated `-`, `0⁻¹ = ∞`). Gather
  everything into one `ofReal (…)` first (R8, R9 / R19, R21), then `congr 1` (or `congr 2` through
  `Real.exp`), then `ring` on real numbers.
- Without R1, R3 and R5 fail with "failed to synthesize IsProbabilityMeasure (expMeasure r)".
- `rw [← ENNReal.ofReal_one]` replaces every `1 : ℝ≥0∞`; do it when the only one left is the one you mean.
- `ENNReal.ofReal_sub` takes `p` explicitly and the sign proof for `q`, the number being **subtracted**:
  `ENNReal.ofReal_sub _ h` with `h : 0 ≤ q`.
- `cond_apply` puts the conditioning set first: `μ (s ∩ t)`, so for `T > s` it gives `Ioi s ∩ Ioi (s + t)`
  and `max s (s + t)`, which needs `max_eq_right`, not `max_eq_left`.
- `exp_tail` needs `0 ≤ x` at each of the three points `s + t`, `s`, `t`; `(by linarith)` gives `0 ≤ s + t`.
- `- -(r * s)` after R23 is `-(-(r * s))`; leave it to `ring`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| the probability instance | `haveI := isProbabilityMeasure_expMeasure hr` | R1 |
| `Ioi x → (Iic x)ᶜ` | `rw [← Set.compl_Iic]` | R2 |
| `μ sᶜ → 1 - μ s` | `rw [prob_compl_eq_one_sub measurableSet_Iic]` | R3, R4 |
| `μ (Iic x) →` cdf | `rw [← ofReal_cdf]` | R5 |
| cdf of `Exp(r)` | `rw [cdf_expMeasure_eq hr]` | R6 |
| take the `then` branch | `rw [if_pos hx]` | R7 |
| `1 → ofReal 1` | `rw [← ENNReal.ofReal_one]` | R8 |
| `ofReal p - ofReal q → ofReal (p - q)` | `rw [← ENNReal.ofReal_sub _ hq]` | R9 |
| `0 ≤ 1 - exp y` | `sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))` | R10–R12 |
| drop `ofReal` / `ofReal ∘ exp` on both sides | `congr 1` / `congr 2` | R13, R25 |
| conditional probability | `rw [cond_apply measurableSet_Ioi]` | R14, R15 |
| `Ioi a ∩ Ioi b → Ioi b` (`a ≤ b`) | `rw [Set.Ioi_inter_Ioi, max_eq_right (by linarith)]` | R16–R18 |
| `(ofReal x)⁻¹ → ofReal x⁻¹` | `rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]` | R19, R20 |
| `ofReal p * ofReal q → ofReal (p * q)` | `rw [← ENNReal.ofReal_mul (by positivity)]` | R21, R22 |
| `(exp x)⁻¹ → exp (-x)`, `exp x * exp y → exp (x + y)` | `rw [← Real.exp_neg, ← Real.exp_add]` | R23, R24 |
| real identity | `ring` | TACTIC_STATES |
| see the state | infoview | |
