# M085 · Chebyshev from Markov: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `intro`, `rw`, `simp`,
`∀`/`∃`/`∧`/`↔`, anonymous constructors `⟨_, _⟩`, dot notation `h.symm`. Helpful but not required: M084
(Markov's inequality, proved from scratch). **New here:** Mathlib's measure theory and probability:
probability measures, the integral `∫ ω, f ω ∂μ`, `Integrable`, `MemLp` (finite p-th moment),
`AEMeasurable`, "almost everywhere" (`0 ≤ᵐ[μ] f`), `μ.real`, `Var[X; μ]`, Markov's inequality as the
Mathlib lemma `mul_meas_ge_le_integral_of_nonneg`; the tactics `positivity` and `linarith`.

**The maths.** Let `(Ω, μ)` be a probability space, `X : Ω → ℝ` with `E[X²] < ∞`, `m = E X`,
`Var X = E[(X - m)²]`, and `c > 0`. Let `A = {ω | c ≤ |X ω - m|}`.

1. **Same event.** For `c ≥ 0` and `|a| ≥ 0`, `c ≤ |a| ↔ c² ≤ |a|² = a²` (squaring is monotone on
   `[0, ∞)`). So `A = {ω | c² ≤ (X ω - m)²}`.
2. **Markov.** `Y = (X - m)²` is nonnegative and integrable (`X - m ∈ L²`). Markov's inequality
   `ε · P(ε ≤ Y) ≤ E Y` at `ε = c²` gives `c² · P(c² ≤ Y) ≤ E[(X - m)²] = Var X`.
3. **Rewrite and divide.** By step 1 the event is `A`: `c² · P(A) ≤ Var X`. Since `c² > 0`,
   `P(A) ≤ Var X / c²`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` with `h : T → G` is a goal the entry does not touch;
  `h` only shows which fact `T` the step added.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type (the sample space).
  `[MeasurableSpace Ω]` says `Ω` carries a σ-algebra (the events); `(μ : Measure Ω)` is a measure on it;
  `[IsProbabilityMeasure μ]` says `μ Ω = 1` (it implies `IsFiniteMeasure μ`, which `memLp_const` asks
  for). A bracket `[…]` is a requirement Lean finds by itself (a *type class*).
- When a new hypothesis contains `|` (a set or an absolute value) or `, ` (an integral), the cell says
  "context gains" in words, or the states are shown as a `lean-goal` block.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `μ[X]` (in the source) | the expectation `E X = ∫ ω, X ω ∂μ`; the infoview prints it as `∫ (x : Ω), X x ∂μ` |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f : Ω → ℝ` against `μ`; it is `0` if `f` is not integrable |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ`, the variance `E[(X - E X)²]` (R15) |
| `μ.real s` | `μ s` as a real number: `P(s)` for a probability measure (`μ s` itself lives in `[0, ∞]`) |
| `{ω \| Q ω}` | the set (event) of `ω` with `Q ω`; `ω ∈ {ω \| Q ω}` simplifies to `Q ω` (R2) |
| `\|a\|` | the absolute value of `a : ℝ` |
| `Integrable f μ` | `f` is (a.e. strongly) measurable and `∫ ‖f‖ ∂μ < ∞`, i.e. `f ∈ L¹(μ)` |
| `MemLp f 2 μ` | `f ∈ L²(μ)`: `f` is a.e. strongly measurable and `E[f²] < ∞` (the `2` is an exponent in `ℝ≥0∞`) |
| `ℝ≥0∞` | the extended nonnegative reals `[0, ∞]`, where `μ s` and the `L^p` exponent live |
| `AEMeasurable f μ` | `f` agrees `μ`-a.e. with a measurable function (R14) |
| `0 ≤ᵐ[μ] f` | `0 ≤ f ω` for `μ`-almost every `ω` (outside a null set) |
| `0 x` | the zero function `0 : Ω → ℝ` applied to `x`; it is the number `0` (R12) |
| `f - fun x => c` | the function `ω ↦ f ω - c` written as a difference of functions (R9) |
| `inst✝ : …` | an unnamed type-class hypothesis (`[MeasurableSpace Ω]` etc.) |
| `{Ω : Type*}`, printed `Ω : Type u_1` | `Ω` is a type in some universe `u_1`: read it as `Ω : Type` |
| `∀ᶠ x in l, p x` | `p x` holds eventually along the filter `l`; `0 ≤ᵐ[μ] f` unfolds to this with `l` = "μ-almost every" (R12) |
| `{x \| c ^ 2 ≤ (X x - ∫ (x : Ω), X x ∂μ) ^ 2}` | two different `x`: the integral binds its own `x` (it is `μ[X]`, a constant); the outer `x` is the set's variable |

---

## Part 1 · `chebyshev`

Statement: for `c > 0` and `X ∈ L²(μ)`, `μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] / c ^ 2`. Plan:
prove the two descriptions of the event equal (R1–R8); prove `(X - μ[X])²` integrable (R9, R10); apply
Markov (R11–R13); fold its right side into `Var` and its set into the original event (R14–R16); clear the
denominator and finish (R17–R19).

### Two descriptions of one event

**R1 · `ext ω`** on sets changes the **goal and the context**. It uses `Set.ext`: two sets are equal when
they have the same elements. Placeholders: `{Ω : Type} (s t : Set Ω)`.

| Before | After |
|---|---|
| `⊢ s = t` | `ω : Ω ⊢ ω ∈ s ↔ ω ∈ t` |

**R2 · `simp only [Set.mem_setOf_eq]`** changes the **goal**. Lemma `Set.mem_setOf_eq :
(a ∈ {x | p x}) = p a`: membership in a set-builder set is the defining property. Placeholders:
`{Ω : Type} (p q : Ω → Prop) (ω : Ω)`. Before and after:

```lean-goal
⊢ ω ∈ {x | p x} ↔ ω ∈ {x | q x}
⊢ p ω ↔ q ω
```

**R3 · `rw [← sq_abs a]`** changes the **goal**. Lemma `sq_abs : |a| ^ 2 = a ^ 2`; right to left it turns
`a ^ 2` into `|a| ^ 2`, so both sides of the `↔` compare the same nonnegative quantity `|a|`. Placeholders:
`(a : ℝ)`. Before and after:

```lean-goal
⊢ P (a ^ 2)
⊢ P (|a| ^ 2)
```

**R4 · `abs_nonneg a`** changes the **context**: it proves `0 ≤ |a|`. Inside a term write
`abs_nonneg _` and Lean infers `a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `ha : 0 ≤ \|a\|` |

**R5 · `hc.le`** changes the **context**. `LT.lt.le : a < b → a ≤ b`, written with dot notation on
`hc : 0 < c`. Placeholders: `(c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ G` | `hc' : 0 ≤ c ⊢ G` |

**R6 · `two_ne_zero`** changes the **context**: `2 ≠ 0` in any type with a `2` that is nonzero; here the
exponent type `ℕ` (the `2` in `c ^ 2` is a natural number). The infoview prints it as `2 ≠ 0`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : 2 ≠ 0 ⊢ G` |

**R7 · `pow_le_pow_iff_left₀ ha hb hn`** changes the **context**. Lemma:
`0 ≤ a → 0 ≤ b → n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)`: on nonnegative numbers, `x ↦ xⁿ` preserves and
reflects `≤`. In the exercise `a = c` (R5), `b = |X ω - μ[X]|` (R4), `n = 2` (R6). Placeholders:
`(a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `hiff : a ^ n ≤ b ^ n ↔ a ≤ b ⊢ G` |

**R8 · `h.symm`** (`Iff.symm`) **closes** a goal that is `h : A ↔ B` read backwards. R7 gives
`c ^ 2 ≤ … ↔ c ≤ …`; the set equation needs `c ≤ … ↔ c ^ 2 ≤ …`, so `exact (pow_le_pow_iff_left₀ …).symm`.
Placeholders: `(A B : Prop) (h : A ↔ B)`.

| Before | After |
|---|---|
| `⊢ B ↔ A` | closed by `exact h.symm` |

### Integrability of the squared deviation

**R9 · `hf.sub (memLp_const c)`** changes the **context**. `memLp_const c : MemLp (fun _ => c) p μ` (finite
measure); `MemLp.sub : MemLp f p μ → MemLp g p μ → MemLp (f - g) p μ`. Placeholders:
`[IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ)`. In the exercise `c` is `μ[X]`; write
`memLp_const _` and Lean infers it.

| Before | After |
|---|---|
| `⊢ G` | `hs : MemLp (f - fun x => c) 2 μ ⊢ G` |

**R10 · `hs.integrable_sq`** changes the **context**. `MemLp.integrable_sq : MemLp g 2 μ →
Integrable (fun x => g x ^ 2) μ`. With `g = f - fun _ => c` the raw type is
`Integrable (fun x => (f - fun x => c) x ^ 2) μ`; writing the type in the `have` restates it in lambda
form (the two are equal by unfolding). Chain: `(hX.sub (memLp_const _)).integrable_sq` (R9 then R10).
Placeholders: `(f : Ω → ℝ) (c : ℝ) (hs : MemLp (f - fun _ => c) 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : Integrable (fun ω => (f ω - c) ^ 2) μ ⊢ G` |

### Markov's inequality

**R11 · `mul_meas_ge_le_integral_of_nonneg hnn hfi ε`** changes the **context**. This is Markov's
inequality: `0 ≤ᵐ[μ] f → Integrable f μ → ∀ ε : ℝ, ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`. Take
`f = fun ω => (X ω - μ[X]) ^ 2` (its integrability is R10's fact) and `ε = c ^ 2`. Write it as
`have hm := …` with no type: Lean computes the type. Placeholders: `(f : Ω → ℝ) (hnn : 0 ≤ᵐ[μ] f)
(hfi : Integrable f μ) (ε : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `hmk : ε * μ.real {x \| ε ≤ f x} ≤ ∫ (x : Ω), f x ∂μ` |

**R12 · `Filter.Eventually.of_forall`** changes the **goal**: what holds everywhere holds almost
everywhere. Lemma: `(∀ x, p x) → ∀ᶠ x in l, p x` (`0 ≤ᵐ[μ] f` is notation for such an `∀ᶠ`). As a term,
`Filter.Eventually.of_forall fun ω => (proof of 0 ≤ f ω)`. Placeholders: `(f : Ω → ℝ)
(h : ∀ ω, 0 ≤ f ω)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ᵐ[μ] f` | `⊢ ∀ (x : Ω), 0 x ≤ f x` |

**R13 · `sq_nonneg a`** changes the **context**: `0 ≤ a ^ 2`. In the exercise it is the pointwise proof
inside R12: `fun ω => sq_nonneg (X ω - μ[X])`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hsq : 0 ≤ a ^ 2 ⊢ G` |

### From the integral to the variance

**R14 · `hf.aemeasurable`** changes the **context**. `MemLp.aemeasurable : MemLp f p μ → AEMeasurable f μ`.
Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hm : AEMeasurable f μ ⊢ G` |

**R15 · `rw [← variance_eq_integral hf]`** changes the **goal** (or, `at h`, a hypothesis). Lemma:
`AEMeasurable X μ → Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ`. Right to left it folds the integral into
`Var`. In the exercise, apply it to Markov's fact: `rw [← variance_eq_integral hX.aemeasurable] at hm`
(R14 inline). Placeholders: `(f : Ω → ℝ) (hf : AEMeasurable f μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), (f ω - ∫ (x : Ω), f x ∂μ) ^ 2 ∂μ)` | `⊢ P Var[f; μ]` |

**R16 · `rw [← e] at h`** changes the **context**: in the hypothesis `h`, every `b` becomes `a`, for
`e : a = b`; the goal is untouched. In the exercise `e` is the set equation `hset` and `h` is Markov's fact,
whose set is the right side of `hset`. Placeholders: `{α : Type} (a b : α) (e : a = b)`.

| Before | After |
|---|---|
| `h : P b ⊢ Q` | `h : P a ⊢ Q` |

After R15 and R16 Markov's fact reads `c ^ 2 * μ.real {ω | c ≤ |X ω - …|} ≤ Var[X; μ]`.

### The final inequality

**R17 · `rw [le_div_iff₀ hc]`** changes the **goal**. Lemma: `0 < c → (a ≤ b / c ↔ a * c ≤ b)`; `rw` with an
`↔` replaces the left statement by the right. In the exercise the denominator is `c ^ 2`: write
`rw [le_div_iff₀ (by positivity)]` (R18). Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b` |

**R18 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` when `e` is built from `+`, `*`, `^`, `/` and
atoms it can see are positive or nonnegative (from hypotheses such as `hc : 0 < c`). Placeholders:
`(c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 < c ^ 2` | closed |

**R19 · `linarith`** **closes** a goal that follows linearly from the hypotheses. It treats a product of
unknowns as one unknown and normalises it first, so `k * p` and `p * k` are the same; `μ.real {…}` and
`Var[X; μ]` are unknown numbers to it. Placeholders: `(p k v : ℝ)`.

| Before | After |
|---|---|
| `h : k * p ≤ v ⊢ p * k ≤ v` | closed |

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: one event, described by cubes.** For `f ≥ 0` and `c ≥ 0`, `{ω | c ≤ f ω} = {ω | c ^ 3 ≤ f ω ^ 3}`:
R1, R2, then R7 (with `n = 3`, `(by norm_num) : 3 ≠ 0`) and R8 in one `exact`:

```lean-goal
⊢ {ω | c ≤ f ω} = {ω | c ^ 3 ≤ f ω ^ 3}
⊢ ω ∈ {ω | c ≤ f ω} ↔ ω ∈ {ω | c ^ 3 ≤ f ω ^ 3}
⊢ c ≤ f ω ↔ c ^ 3 ≤ f ω ^ 3
```

**W2: Markov on `f ^ 2`** for `f ∈ L²`: R10 (from `hf` directly, no `sub`), R12 with R13, then R11 gives
exactly the goal:

```lean-goal
⊢ c * μ.real {x | c ≤ f x ^ 2} ≤ ∫ (x : Ω), f x ^ 2 ∂μ
```

**W3: from `k * p ≤ v` to `p ≤ v / k`** with `k = (a + 1) ^ 3`, `0 < a`: R17 with `(by positivity)` (R18),
then R19:

```lean-goal
⊢ p ≤ v / (a + 1) ^ 3
⊢ p * (a + 1) ^ 3 ≤ v
```

---

## Traps

- **`rw [← sq_abs]` without an argument** rewrites the first square it finds, which is `c ^ 2`
  (giving `|c| ^ 2`), not `(X ω - μ[X]) ^ 2`. Write `rw [← sq_abs (X ω - μ[X])]` (R3).
- **The direction of the `↔`.** R7 states `a ^ n ≤ b ^ n ↔ a ≤ b`; the set equation, after R1 and R2, needs
  `c ≤ … ↔ c ^ 2 ≤ …`. Close it with `.symm` (R8).
- **`μ[X]` is printed as `∫ (x : Ω), X x ∂μ`.** The two are the same term; write `μ[X]` in your `have`s.
- **Bound variable names do not matter.** Markov's set is printed `{x | c ^ 2 ≤ (X x - …) ^ 2}`, your
  `hset` has `{ω | …}`; `rw [← hset] at hm` still finds it (R16).
- **Order of the product.** Markov gives `c ^ 2 * P(A)`; after R17 the goal is `P(A) * c ^ 2 ≤ Var[X; μ]`.
  `exact hm` fails; `linarith` (R19) does not care.
- **The denominator is `c ^ 2`**, so `le_div_iff₀ hc` does not fit (`hc : 0 < c`). Use
  `le_div_iff₀ (by positivity)`.
- **Banned:** Mathlib's own Chebyshev (`meas_ge_le_variance_div_sq`) and its `eLpNorm` relatives. The
  exercise is to derive it from Markov.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| equality of two sets | `ext ω` | R1 |
| `ω ∈ {x \| p x}` → `p ω` | `simp only [Set.mem_setOf_eq]` | R2 |
| `a ^ 2` → `\|a\| ^ 2` | `rw [← sq_abs a]` | R3 |
| `0 ≤ \|a\|`, `0 ≤ c` from `0 < c`, `2 ≠ 0` | `abs_nonneg _`, `hc.le`, `two_ne_zero` | R4–R6 |
| `a ^ n ≤ b ^ n ↔ a ≤ b` for `a, b ≥ 0` | `pow_le_pow_iff_left₀ ha hb hn` | R7 |
| flip an `↔` | `h.symm` | R8 |
| `(X - c)²` integrable from `MemLp X 2 μ` | `(hX.sub (memLp_const _)).integrable_sq` | R9, R10 |
| Markov `ε P(ε ≤ f) ≤ E f` | `mul_meas_ge_le_integral_of_nonneg hnn hfi ε` | R11 |
| a.e. nonnegativity of a square | `Filter.Eventually.of_forall fun ω => sq_nonneg (…)` | R12, R13 |
| `∫ (X - E X)²` → `Var[X; μ]` | `rw [← variance_eq_integral hX.aemeasurable] at h` | R14, R15 |
| replace `b` by `a` in `h` | `rw [← e] at h` | R16 |
| `a ≤ b / c` → `a * c ≤ b` | `rw [le_div_iff₀ (by positivity)]` | R17, R18 |
| linear finish | `linarith` | R19 |
| see the state | infoview | |
