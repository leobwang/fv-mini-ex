# M154 · High-temperature limit: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's finite canonical ensemble
(`CanonicalEnsemble`, its Boltzmann probability and partition function as functions of the inverse
temperature `b`), Mathlib's `Continuous`, limits written with `Tendsto` and `𝓝`, the tactic
`fun_prop`, and finite sums `∑`.

The physics: for a finite set `ι` of microstates with energies `E i`, at inverse temperature `b`
(`b = 1/T` with `k_B = 1`) the partition function is $Z(b) = \sum_{j} e^{-b E_j}$ and the Boltzmann
probability is $p_b(i) = e^{-b E_i} / Z(b)$. At $b = 0$ every term is $e^0 = 1$, so
$p_0(i) = 1/|\iota|$. The exercise: $p_b(i) \to 1/|\iota|$ as $b \to 0$, which follows because
$b \mapsto p_b(i)$ is continuous.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : (ℝ → ℝ) → Prop` when the changed part is a
  whole function). The step changes only the part inside `P (…)`.
- `Q : Prop` with `g : … → Q` is a stand-in goal: the entry only adds a hypothesis, and `g` uses it.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]`
  is a requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `∅` in an After cell: no goal is left.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | physlib: a physical system whose microstates are the elements of `ι`; `𝓒.energy : ι → ℝ` gives each microstate's energy |
| `[Fintype ι]` | `ι` is finite (so `∑` over all of `ι` makes sense) |
| `[Nonempty ι]` | `ι` has at least one element (so `Z(b) > 0`) |
| `[MeasurableSpace ι]` | a measure-theory structure on `ι` that `CanonicalEnsemble` requires; it plays no role here |
| `𝓒.probabilityBetaReal b i` | $p_b(i) = e^{-b E_i}/Z(b)$, the Boltzmann probability at inverse temperature `b` (R1) |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | $Z(b) = \sum_j e^{-b E_j}$ (R2) |
| `rexp x` | `Real.exp x`, the real exponential $e^x$ |
| `∑ i, f i` | sum of `f i` over every `i : ι` (`Finset.univ` is the finite set of all of `ι`) |
| `Finset.univ.card`, `Fintype.card ι` | the number of elements of `ι`, written $\lvert\iota\rvert$ |
| `n • a` | `n : ℕ` copies of `a` added up (`n • a = n * a` by R9) |
| `↑(Fintype.card ι)` | the natural number `Fintype.card ι` cast into `ℝ` |
| `a⁻¹` | `1 / a`; `simp` prefers this form (R10) |
| `Continuous f` | `f` is continuous (for `f : ℝ → ℝ`, the usual ε-δ notion) |
| `𝓝 a` | the *neighbourhood filter* of `a`: "points close to `a`" (needs `open Topology`) |
| `Tendsto f (𝓝 a) (𝓝 L)` | $f(x) \to L$ as $x \to a$ (from `Filter`; needs `open Filter`) |
| `fun b => …` | the function $b \mapsto \dots$ |
| `∑ i, rexp (-b * 𝓒.energy i)` after R2 | the sum's own bound variable, printed `i` (or `x` after `simp`); it is not your microstate `i` |
| `rexp (-(b * 𝓒.energy i))` | what `simp` makes of `rexp (-b * 𝓒.energy i)` (lemma `neg_mul : -a * b = -(a * b)`); same value |
| `case refine_1`, `refine_2`, `refine_3` | labels of the three goals R3 creates, in the order numerator, denominator, nonzero |
| `inst✝ : MeasurableSpace ι` | an unnamed instance hypothesis from a `[…]` binder of the statement |

---

## Part 1 · `high_temperature_limit`

Statement: for a finite, nonempty ensemble `𝓒` and a microstate `i`,
`Tendsto (fun b => 𝓒.probabilityBetaReal b i) (𝓝 0) (𝓝 (1 / Fintype.card ι))`, i.e.
$p_b(i) \to 1/\lvert\iota\rvert$ as $b \to 0$.

Plan: prove `hc : Continuous (fun b => 𝓒.probabilityBetaReal b i)` (R1–R6), turn it into a limit at `0`
(R7), and evaluate the limit value `p_0(i)` (R8–R11).

### Unfolding the physlib definitions

**R1 · `unfold CanonicalEnsemble.probabilityBetaReal`** changes the **goal**: every
`𝓒.probabilityBetaReal b k` is replaced by its definition, also inside `fun b => …`. Definition:
`𝓒.probabilityBetaReal b k = rexp (-b * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal b`.
Placeholders: `{ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (k : ι)`,
`(P : (ℝ → ℝ) → Prop)`. With `open CanonicalEnsemble` the short name `unfold probabilityBetaReal` works too.

| Before | After |
|---|---|
| `⊢ P fun b => 𝓒.probabilityBetaReal b k` | `⊢ P fun b => rexp (-b * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal b` |

**R2 · `unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal`** changes the **goal**: the
partition function becomes its finite sum. Definition:
`𝓒.mathematicalPartitionFunctionBetaReal b = ∑ i, rexp (-b * 𝓒.energy i)`. The bound variable is named
`i` by the definition; it is a fresh variable, not your `i`. Placeholders as in R1.

| Before | After |
|---|---|
| `⊢ P fun b => 𝓒.mathematicalPartitionFunctionBetaReal b` | `⊢ P fun b => ∑ i, rexp (-b * 𝓒.energy i)` |

### Continuity of a quotient

**R3 · `refine Continuous.div ?_ ?_ ?_`** changes the **goal list**: one goal becomes three. The lemma is
`Continuous.div : Continuous f → Continuous g → (∀ x, g x ≠ 0) → Continuous (f / g)`; `f / g` is the
same function as `fun x => f x / g x`, so `refine` matches it against your goal. Placeholders:
`(f g : ℝ → ℝ)` (in general `f g : α → G₀` with `G₀` a field such as `ℝ` or `ℂ`).

| Before | After |
|---|---|
| `⊢ Continuous fun x => f x / g x` | `⊢ Continuous f`, `⊢ Continuous g`, `⊢ ∀ (x : ℝ), g x ≠ 0` |

You can also pass the three proofs directly: `exact Continuous.div p₁ p₂ p₃`, with `(by fun_prop)` for
`p₁`, `p₂`.

**R4 · `fun_prop`** **closes** a goal `Continuous fun b => …` when the body is built from continuous
pieces it knows: `rexp`, `*`, `-`, `+`, constants, the variable, and finite sums `∑`. It does **not**
prove the third goal of R3 (`g x ≠ 0`), and it does not unfold definitions: unfold first (R1, R2).
Placeholders: `(c : ℝ)`; `{ι : Type} [Fintype ι] (E : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ Continuous fun b => rexp (-b * c)` | `∅` |
| `E : ι → ℝ ⊢ Continuous fun b => ∑ j, rexp (-b * E j)` | `∅` |

### The denominator is never zero

**R5 · `CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos`** changes the **context**. The lemma
is `[Nonempty ι] (b : ℝ) : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b` (a nonempty sum of positive
exponentials). Write it as `𝓒.mathematicalPartitionFunctionBetaReal_pos b`. Placeholders:
`{ι : Type} [MeasurableSpace ι] [Fintype ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` |
|---|---|
| `⊢ Q` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal b ⊢ Q` |

**R6 · `LT.lt.ne'`** **closes** a `≠` goal from a `<` fact. The lemma is `a < b → b ≠ a`; written with dot
notation, `h.ne'` for `h : a < b`. So `(hZ : 0 < x).ne' : x ≠ 0`. Placeholders:
`{α : Type} [Preorder α] (a b : α)` (`α` has an order `<`; `ℝ` qualifies).

| Before | After `exact h.ne'` |
|---|---|
| `h : a < b ⊢ b ≠ a` | `∅` |

`exact` accepts a proof whose type equals the goal *after unfolding definitions*. After R2 the third goal
of R3 talks about `∑ i, rexp (-b * 𝓒.energy i)`, while R5 talks about
`𝓒.mathematicalPartitionFunctionBetaReal b`; these are the same term once unfolded, so `exact` accepts
R5's fact anyway (W2 shows this on another definition). Introduce the `b` of `∀ b, …` first (`intro b`),
or pass `fun b => …`.

### From continuity to a limit

**R7 · `Continuous.tendsto`** changes the **context**. The lemma is
`Continuous f → ∀ x, Tendsto f (𝓝 x) (𝓝 (f x))`: a continuous function tends to its own value. Written
`hf.tendsto x`. Placeholders: `(f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)` (any topological spaces work).

| Before | After `have ht := hf.tendsto x` |
|---|---|
| `⊢ Q` | `ht : Tendsto f (𝓝 x) (𝓝 (f x)) ⊢ Q` |

With `f = fun b => 𝓒.probabilityBetaReal b i` and `x = 0`, the limit is `𝓒.probabilityBetaReal 0 i`, not
yet `1 / Fintype.card ι`: R8–R11 compute it.

### Evaluating at `b = 0`

`simp` applies R8–R10 by itself once the definitions are unfolded; they are listed so you can read what
it does.

**R8 · `neg_zero`, `zero_mul`, `Real.exp_zero`** change the **goal**: `-0 = 0`, `0 * c = 0`, `rexp 0 = 1`.
Placeholders: `(c : ℝ)`.

| Before | After `rw [neg_zero]` | After `rw [zero_mul]` | After `rw [Real.exp_zero]` |
|---|---|---|---|
| `⊢ P (rexp (-0 * c))` | `⊢ P (rexp (0 * c))` | `⊢ P (rexp 0)` | `⊢ P 1` |

**R9 · `Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul`, `mul_one`** change the **goal**: a sum of
the constant `1` over `ι` becomes `|ι|` as a real number. `Finset.sum_const : ∑ _x ∈ s, b = s.card • b`;
`Finset.card_univ : Finset.univ.card = Fintype.card ι`; `nsmul_eq_mul : n • a = ↑n * a`;
`mul_one : a * 1 = a`. Placeholders: `{ι : Type} [Fintype ι]`.

| Before | After `sum_const` | After `card_univ` | After `nsmul_eq_mul` | After `mul_one` |
|---|---|---|---|---|
| `⊢ P (∑ _j, 1)` | `⊢ P (Finset.univ.card • 1)` | `⊢ P (Fintype.card ι • 1)` | `⊢ P (↑(Fintype.card ι) * 1)` | `⊢ P ↑(Fintype.card ι)` |

**R10 · `one_div`** changes the **goal**. The lemma is `1 / a = a⁻¹`. `simp` uses it everywhere, on both
the hypothesis and the goal, so the target `1 / ↑(Fintype.card ι)` turns into `(↑(Fintype.card ι))⁻¹`.
Placeholders: `{G : Type} [DivInvMonoid G] (a : G)` (`G` has `*`, `1` and `⁻¹`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (1 / a)` | `⊢ P a⁻¹` |

**R11 · `simpa [d₁, d₂] using e`** **closes** the goal. It simplifies the type of `e` and the goal with
`simp`, unfolding the definitions `dᵢ` you list, and closes the goal if the two results agree.
Here `e` is R7's limit and `dᵢ` are the two definitions of R1, R2; `simp` then does R8–R10 on both sides
(and rewrites `-b * E` to `-(b * E)` on both sides, which is harmless). Placeholders: `(a : ℝ)`, a
definition `q x := 1 / (x * 1)`.

| Before | After `simpa [q] using e` |
|---|---|
| `e : P (q a) ⊢ P a⁻¹` | `∅` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: continuity of a quotient.** For `fun x => rexp (2 * x) / rexp x`: R3 gives three goals, R4 closes
the first two, and the third needs a positivity fact (`Real.exp_pos x : 0 < rexp x`) flipped by R6:

```lean-goal
⊢ Continuous fun x => rexp (2 * x) / rexp x
⊢ Continuous fun x => rexp (2 * x)
⊢ Continuous rexp
⊢ ∀ (x : ℝ), rexp x ≠ 0
```

**W2: `exact` sees through definitions.** With `Zt x := 1 + rexp x` and `h : 0 < Zt x`, `exact h.ne'`
closes `1 + rexp x ≠ 0`:

```lean-goal
⊢ 1 + rexp x ≠ 0
```

**W3: a limit at `0` by continuity.** `have hc` by `fun_prop`, then R7, then `simpa using ht`
(R8, R10 inside `simp`):

```lean-goal
⊢ Tendsto (fun x => rexp (-x * 3) / 2) (𝓝 0) (𝓝 (1 / 2))
```

After `have ht := hc.tendsto 0` the context holds
`ht : Tendsto (fun x => rexp (-x * 3) / 2) (𝓝 0) (𝓝 (rexp (-0 * 3) / 2))`: the limit is the value at
`0`, still unevaluated, exactly as in Part 1.

---

## Traps

- `Continuous.tendsto` gives the limit `f 0` in unevaluated form. Do not try to `exact hc.tendsto 0`:
  the goal's limit is `1 / ↑(Fintype.card ι)`, a different term. Simplify both with `simpa` (R11).
- `simpa` must be told the physlib definitions (`simpa [probabilityBetaReal, …]`): `simp` does not unfold
  `def`s on its own, so `𝓒.probabilityBetaReal 0 i` would stay as it is.
- `fun_prop` does not unfold definitions: on `Continuous fun b => 𝓒.probabilityBetaReal b i` it fails.
  Unfold both definitions first (R1, R2).
- `fun_prop` cannot prove the denominator is nonzero (third goal of R3). That needs R5 and R6.
- `mathematicalPartitionFunctionBetaReal_pos` is an inequality, not an equation: use it with `exact`/`.ne'`,
  never with `rw`.
- R5 needs the instance `[Nonempty ι]` (an empty sum is `0`). The exercise's statement provides it, so
  `𝓒.mathematicalPartitionFunctionBetaReal_pos b` needs no extra argument.
- Write the `have` type in full, `Continuous (fun b => 𝓒.probabilityBetaReal b i)`: `Continuous` needs
  the function, not its value `𝓒.probabilityBetaReal b i`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| state the milestone | `have hc : Continuous (fun b => 𝓒.probabilityBetaReal b i) := by …` | TACTIC_STATES |
| `p_b i` → `exp / Z` | `unfold probabilityBetaReal` | R1 |
| `Z b` → `∑ j, exp (-b * E j)` | `unfold mathematicalPartitionFunctionBetaReal` | R2 |
| continuity of `f / g` | `refine Continuous.div ?_ ?_ ?_` or `exact Continuous.div p₁ p₂ p₃` | R3 |
| continuity of exp / sum expressions | `fun_prop` | R4 |
| `0 < Z b` | `𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R5 |
| `x ≠ 0` from `h : 0 < x` | `h.ne'` | R6 |
| continuous ⇒ limit = value | `hc.tendsto 0` | R7 |
| `rexp (-0 * c) = 1` | `simp` (`neg_zero`, `zero_mul`, `Real.exp_zero`) | R8 |
| `∑ _j : ι, 1 = ↑(Fintype.card ι)` | `simp` (`Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul`) | R9 |
| `1 / a = a⁻¹` | `one_div` (simp normal form) | R10 |
| finish: simplify a fact and the goal to match | `simpa [defs] using e` | R11 |
| see the state | infoview | |
