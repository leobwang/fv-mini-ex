# M152 · Mean energy lies in the spectrum's range: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have`, `exact`, `apply`, `intro`, `rw`, `simp only`,
`unfold`, `constructor`, `calc` (E020), anonymous functions `fun i => …`, dot notation `h.foo`.
**New here:** physlib's `CanonicalEnsemble` (energy, partition function, Boltzmann probabilities and mean
energy as functions of the inverse temperature), Mathlib's finite sums `∑ i, f i` and the lemmas that pull a
constant out of one or compare two of them term by term, and the tactic `positivity`.

**The physics, in symbols.** Units `k_B = 1`. A finite system has microstates `i ∈ ι` with energies
`E i`. At inverse temperature `b` (any real, negative included): $Z(b) = \sum_i e^{-b E_i} > 0$
(partition function), $p_b(i) = e^{-b E_i}/Z(b)$ (Boltzmann probability) and
$U(b) = \sum_i E_i\, p_b(i)$ (mean energy). The weights satisfy $p_b(i) \ge 0$ and $\sum_i p_b(i) = 1$, so
$U(b)$ is a weighted average of the $E_i$. If $m \le E_i \le M$ for all $i$, then
$m = \sum_i m\,p_b(i) \le \sum_i E_i\,p_b(i) \le \sum_i M\,p_b(i) = M$.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`/`exact`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Preorder α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it. The guide fixes
  `{ι : Type} [Fintype ι] [MeasurableSpace ι]` once with `variable`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `inst✝² : Fintype ι` | an instance argument from the statement, shown without a usable name; never refer to it |
| `𝓒 : CanonicalEnsemble ι` | a physlib system with microstates of type `ι`; `𝓒.energy : ι → ℝ` is the energy `E` |
| `[Fintype ι]` | finitely many microstates, so sums `∑ i` over all of `ι` make sense |
| `[Nonempty ι]` | at least one microstate; needed for `Z > 0` (R1) |
| `[MeasurableSpace ι]` | required by the `CanonicalEnsemble` structure; plays no role here |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b)`, *defined* as `∑ i, rexp (-b * 𝓒.energy i)` (R7) |
| `𝓒.probabilityBetaReal b i` | `p_b(i)`, defined as `rexp (-b * 𝓒.energy i) / Z(b)` (R2) |
| `𝓒.meanEnergyBetaReal b` | `U(b)`, defined as `∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i` (R8) |
| `-b * 𝓒.energy i` | `(-b) * E i`: unary minus binds tighter than `*`; the Boltzmann exponent $-bE_i$ |
| `∀ (i : ι), m ≤ 𝓒.energy i` | how the infoview prints `hm : ∀ i, m ≤ 𝓒.energy i` from the statement |
| `rexp x` | `Real.exp x`, the real exponential $e^x$ |
| `∑ i, f i` | $\sum_{i \in ι} f(i)$, the sum over `Finset.univ` (all of `ι`) |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι`; lemma statements use this form |
| `∀ i ∈ Finset.univ, P i` | `∀ i, i ∈ Finset.univ → P i`; the membership is always true here (R12) |
| `(∑ i, f i) / a` vs `∑ i, f i / a` | the sum divided by `a` vs the sum of the quotients: `∑` reaches as far right as it can |
| `a * ∑ i, f i` | `a * (∑ i, f i)` |
| `a✝` | an anonymous hypothesis (from `intro i _`); you cannot name it, and need not |
| `case calc_1` | the goal for the first step of a `calc` whose proof is `?_` |
| `case hbc`, `case ha` | goals named after the lemma's hypotheses, left by `apply` (R13) |

---

## Part 1 · `meanEnergy_bounds`

Statement: with `hm : ∀ i, m ≤ E i` and `hM : ∀ i, E i ≤ M`, prove `m ≤ U(b) ∧ U(b) ≤ M` for every real `b`.
First build three facts: `hZ : 0 < Z(b)` (R1), `hp : ∀ i, 0 ≤ p_b(i)` (R2, R3) and
`h1 : ∑ i, p_b(i) = 1` (R2, R4, then R7: R6 applied with R5). Then unfold `U` (R8), split with `constructor`, and prove each half
with a two-step `calc` (R9): one step rewrites the constant as a weighted sum (R10, `rw [h1]`, R11), the other
compares the sums term by term (R12, R13).

### The weights: `hZ`, `hp`, `h1`

**R1 · `mathematicalPartitionFunctionBetaReal_pos`** changes the **context**. The lemma is
`[Nonempty ι] → 0 < 𝓒.mathematicalPartitionFunctionBetaReal b`; write
`have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b`. Placeholders:
`[Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t ⊢ G` |

**R2 · `unfold probabilityBetaReal`** changes the **goal**: every `𝓒.probabilityBetaReal t k` becomes its body.
`simp only [probabilityBetaReal]` does the same, and inside `simp only [probabilityBetaReal, ← Finset.sum_div]`
it combines with R4 in one call. Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ) (k : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal t k)` | `⊢ P (rexp (-t * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal t)` |

**R3 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) where `e` is built from `rexp`, `+`,
`*`, `/`, powers and numerals. It knows `0 < rexp x`; for an atom it cannot look into, such as `c` (or `Z(b)`),
it uses a hypothesis `0 < c` / `0 ≤ c` already in the context. So `have hZ` (R1) must come first.
Placeholders: `(x c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 ≤ rexp x / c` | closed |

**R4 · `rw [← Finset.sum_div]`** changes the **goal**. The lemma is
`Finset.sum_div : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; right to left it pulls the common divisor out of the
sum. Placeholders: `(f : ι → ℝ) (a : ℝ)` (stated for any `DivisionSemiring`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R5 · `hab.ne'`** (`LT.lt.ne'`) changes the **context**. The lemma is `a < b → b ≠ a`; the primed version flips
the sides, so from `hZ : 0 < Z` you get `hZ.ne' : Z ≠ 0`, which R6/R7 need. Placeholders:
`{α : Type} [Preorder α] (a b : α) (hab : a < b)` (α has `≤` and `<`; `ℝ` qualifies). Usually written inline:
`div_self hZ.ne'`.

| Before | After |
|---|---|
| `hab : a < b ⊢ G` | `h : b ≠ a ⊢ G` |

**R6 · `div_self`** changes the **goal**. The lemma is `div_self : a ≠ 0 → a / a = 1`. Placeholders:
`(a : ℝ) (ha : a ≠ 0)` (stated for any `GroupWithZero`; `ℝ` and `ℂ` qualify).

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ P (a / a)` | `⊢ P 1` |

**R7 · `exact div_self hZ`** **closes** `(∑ i, w i) / Zw w = 1` where `Zw w` is *defined* as `∑ i, w i`. `rw` looks
for the literal text `Zw w / Zw w` and fails; `exact` checks the type up to unfolding definitions, sees that the
numerator *is* `Zw w`, and succeeds. In the exercise `Z(b)` is defined as `∑ i, rexp (-b * 𝓒.energy i)`, the
numerator R4 leaves. Placeholders: `(w : ι → ℝ) (hZ : Zw w ≠ 0)`, with `Zw` a guide-only definition.

| Before | After |
|---|---|
| `hZ : Zw w ≠ 0 ⊢ (∑ i, w i) / Zw w = 1` | closed |

**W1 (R4 → R7 with R5): normalising positive weights `w`.**

```lean-goal
⊢ ∑ i, w i / Zw w = 1
⊢ (∑ i, w i) / Zw w = 1
```

The last goal is closed by `exact div_self hS.ne'`.

### The mean: unfold, split, two `calc`s

**R8 · `unfold meanEnergyBetaReal`** changes the **goal**: `𝓒.meanEnergyBetaReal t` becomes its body. Placeholders:
`(𝓒 : CanonicalEnsemble ι) (t : ℝ)`. After it, `constructor` (TACTIC_STATES, "Structure") splits the `∧`.

| Before | After |
|---|---|
| `⊢ P (𝓒.meanEnergyBetaReal t)` | `⊢ P (∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal t i)` |

**R9 · `calc` mixing `=` and `≤`** changes the **goal list**: `x ≤ z` becomes one goal per step, `x = y` and
`y ≤ z`. The first step starts with the goal's left side, the last ends with its right side, and each later step
starts with `_`. Either side of a step may be `_` when Lean can read it off the goal (`_ ≤ _ := …` as the last
step). In the exercise give each step its proof inline (`:= by rw […]`, `:= Finset.sum_le_sum …`).
Placeholders: `(x y z : ℝ)`.

| Before | After |
|---|---|
| `⊢ x ≤ z` | `⊢ x = y`, `⊢ y ≤ z` |

**R10 · `rw [← Finset.mul_sum]`** changes the **goal**. The lemma is
`Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left it pulls the common factor out.
Placeholders: `(f : ι → ℝ) (a : ℝ)` (stated for any semiring; `ℝ` qualifies). Then `rw [h1]` replaces the sum
of weights by `1`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R11 · `rw [mul_one]`** changes the **goal**: `a * 1` becomes `a`. When the goal becomes `a = a`, `rw` closes it
by `rfl`. Placeholders: `{α : Type} [MulOneClass α] (a : α)` (α has `*` with a unit `1`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**W2 (R10 → `rw [h1]` → R11): a constant against total weight 1.**

```lean-goal
⊢ ∑ i, 3 * w i = 3
⊢ 3 * ∑ i, w i = 3
⊢ 3 * 1 = 3
```

`rw [mul_one]` then closes the goal.

**R12 · `Finset.sum_le_sum`** changes the **goal**. The lemma is
`(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`: compare two sums term by term. `apply` leaves the
term-wise goal; `intro i _` then takes `i` and the (useless) membership. As a term:
`Finset.sum_le_sum fun i _ => proof_of_f_i_le_g_i`. Placeholders: `(f g : ι → ℝ)`.

| Before | After `apply Finset.sum_le_sum` | After `intro i _` |
|---|---|---|
| `⊢ ∑ i, f i ≤ ∑ i, g i` | `⊢ ∀ i ∈ Finset.univ, f i ≤ g i` | `i : ι, a✝ : i ∈ Finset.univ ⊢ f i ≤ g i` |

**R13 · `mul_le_mul_of_nonneg_right`** changes the **goal list**. The lemma is
`b ≤ c → 0 ≤ a → b * a ≤ c * a`: multiply an inequality on the right by a non-negative number. `apply` leaves its
two hypotheses as goals; as a term, `mul_le_mul_of_nonneg_right hbc ha`. Placeholders:
`(a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a)`. Here `b ≤ c` comes from `hm i` / `hM i` and `0 ≤ a` from `hp i`.

| Before | After |
|---|---|
| `⊢ b * a ≤ c * a` | `⊢ b ≤ c`, `⊢ 0 ≤ a` |

**W3 (R9, R12 → R13, then `one_mul`): values at most 1 weigh no more than the weights.**

```lean-goal
⊢ ∑ i, x i * w i ≤ ∑ i, w i
```

The first `calc` step `∑ i, x i * w i ≤ ∑ i, 1 * w i` is
`Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (hw i)`; the second is
`simp only [one_mul]`, with `one_mul : 1 * a = a` (the mirror of R11).

---

## Traps

- `positivity` without `hZ : 0 < Z(b)` in the context fails on `0 ≤ rexp (-b * E i) / Z(b)`: it cannot see that
  `Z(b)` is a sum of exponentials. Run R1 first.
- `rw [div_self hZ.ne']` fails on `(∑ i, rexp (-b * 𝓒.energy i)) / Z(b) = 1`: the numerator is not literally
  `Z(b)`. Use `exact div_self hZ.ne'` (R7).
- `rw [← Finset.mul_sum]` needs the *same* factor in front of every term: `∑ i, m * p_b(i)`, not
  `∑ i, p_b(i) * m`. Write the `calc` middle term with the constant on the left, which also matches the shape
  `b * a ≤ c * a` of R13 with `a = p_b(i)`.
- `R13` multiplies on the **right**: it proves `m * p ≤ E i * p`, matching `E i * p_b(i)` in `U(b)`. The
  `_left` version would give `p * m ≤ p * E i`, which does not match.
- The bound needs no sign of `b`: only `p_b(i) ≥ 0` and `∑ p_b(i) = 1` are used, and both hold for every real `b`.
- `R1` needs `[Nonempty ι]`: over no microstates `Z` is the empty sum `0`. The spec theorem carries that instance.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < Z(b)` | `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R1 |
| unfold `p_b(i)` | `unfold probabilityBetaReal` / `simp only [probabilityBetaReal]` | R2 |
| `0 ≤ rexp x / Z` (with `hZ` around) | `positivity` | R3 |
| `∑ i, f i / a → (∑ i, f i) / a` | `rw [← Finset.sum_div]` | R4 |
| `0 < Z → Z ≠ 0` | `hZ.ne'` | R5 |
| `a / a → 1` | `rw [div_self ha]` | R6 |
| `(∑ …) / Z = 1` with `Z` defined as that sum | `exact div_self hZ.ne'` | R7 |
| unfold `U(b)` | `unfold meanEnergyBetaReal` | R8 |
| split `A ∧ B` | `constructor` | TACTIC_STATES |
| chain `=` and `≤` | `calc x = y := … ` / `_ ≤ z := …` | R9 |
| `∑ i, a * f i → a * ∑ i, f i` | `rw [← Finset.mul_sum]` | R10 |
| `a * 1 → a` | `rw [mul_one]` | R11 |
| compare sums term by term | `Finset.sum_le_sum fun i _ => …` | R12 |
| `b ≤ c`, `0 ≤ a` ⟹ `b * a ≤ c * a` | `mul_le_mul_of_nonneg_right hbc ha` | R13 |
| see the state | infoview | |
