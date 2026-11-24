# M150 · The Boltzmann distribution: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` with its
finite-system Boltzmann probability and partition function, Mathlib's finite sums `∑`, `Real.exp`, and
the `positivity` tactic.

**The physics in one line.** A system with finitely many microstates `i : ι` of energy `E i` at inverse
temperature `β = 1/(k_B T)` (units with `k_B = 1`) has partition function `Z(β) = ∑ᵢ exp(-β E i)` and
Boltzmann probabilities `p_β(i) = exp(-β E i) / Z(β)`. Since every `exp(…) > 0`, `Z(β) > 0`, so each
`p_β(i) > 0`, and `∑ᵢ p_β(i) = Z(β) / Z(β) = 1`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is a whole goal the step leaves untouched.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | physlib's structure for a physical system whose microstates are the elements of `ι`; its field `𝓒.energy : ι → ℝ` gives each microstate's energy |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense (`Fin n`, `Bool` qualify) |
| `[Nonempty ι]` | `ι` has at least one element; needed for `Z(β) > 0` (an empty sum is `0`) |
| `[MeasurableSpace ι]` | a σ-algebra on `ι`; `CanonicalEnsemble` requires one. Irrelevant for finite sums, never touch it |
| `𝓒.energy i`, `𝓒.probabilityBetaReal b i` | dot notation: `CanonicalEnsemble.probabilityBetaReal 𝓒 b i`. The full name (with the `CanonicalEnsemble.` prefix) is what `unfold` and lemma names use |
| `inst✝ : Fintype ι` | an unnamed instance hypothesis (the brackets above) as the infoview prints it |
| `𝓒.mathematicalPartitionFunctionBetaReal β` | `Z(β) = ∑ i, rexp (-β * 𝓒.energy i)`, a real number (R6) |
| `𝓒.probabilityBetaReal β i` | `p_β(i) = rexp (-β * 𝓒.energy i) / Z(β)` (R3) |
| `rexp x` | `Real.exp x`, the real exponential `eˣ` |
| `-β * 𝓒.energy i` | `(-β) * E i`: unary minus binds tighter than `*` |
| `∑ i, f i` | `Finset.sum Finset.univ f`: the sum of `f i` over every `i : ι` |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι`; `∑ i, f i` is the case `s = Finset.univ` |
| `∑ i, f i / a` | `∑ i, (f i / a)`: the sum binds everything to its right |
| `(∑ i, f i) / a` | the whole sum divided by `a` |
| `case refine_1`, `case refine_2` | the two goals `refine ⟨?_, ?_⟩` created, in order |

---

## Part 1 · `boltzmann_is_distribution`

Statement: for a finite, nonempty ensemble `𝓒` and any real `b`, every Boltzmann probability
`𝓒.probabilityBetaReal b i` is positive, and they sum to `1`. One conjunction: a `∀` on the left, a sum
equation on the right.

### Fact first: `Z(b) > 0`

**R1 · `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos β`** changes the **context**: it adds
`hZ`. The lemma is
`CanonicalEnsemble.mathematicalPartitionFunctionBetaReal_pos [Nonempty ι] (β : ℝ) : 0 < 𝓒.mathematicalPartitionFunctionBetaReal β`.
With `have hZ := e` (no type written) Lean takes the type of `e`. Placeholders:
`{ι : Type} [MeasurableSpace ι] [Fintype ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ) (G : Prop)`.
Both halves of the problem need this one fact, so get it before splitting.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal β ⊢ G` |

### Splitting

**R2 · `refine ⟨fun i => ?_, ?_⟩`** changes the **goal list and the context**: a goal `(∀ i, A i) ∧ B`
becomes two goals; the first one gains `i : ι` (the anonymous constructor builds `∀ i, A i` as a
function `fun i => …`). Placeholders: `{ι : Type} (A : ι → Prop) (B : Prop)`. Same as
`constructor` followed by `intro i` in the first goal.

| Before | After |
|---|---|
| `⊢ (∀ (i : ι), A i) ∧ B` | `i : ι ⊢ A i`, `⊢ B` |

### Goal 1: `0 < 𝓒.probabilityBetaReal b i`

**R3 · `unfold CanonicalEnsemble.probabilityBetaReal`** changes the **goal**: the name is replaced by its
body. Under `open CanonicalEnsemble`, `unfold probabilityBetaReal` also works, and it unfolds under `∑`
too. Placeholders: `{ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ) (i : ι)
(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal β i)` | `⊢ P (rexp (-β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal β)` |

**R4 · `positivity`** **closes** a goal `0 < e` (or `0 ≤ e`, `e ≠ 0`) by walking the syntax of `e`: `exp`
of anything is positive, a quotient or product of positives is positive, and so on. An atom it cannot
analyse (here `Z`) counts as positive only if a hypothesis `0 < Z` is in the context; that is why R1 comes
first. It does **not** unfold definitions, so run R3 before it; without `hZ` it fails even after R3. Placeholders: `(x Z : ℝ)`.

| Before | After |
|---|---|
| `hZ : 0 < Z ⊢ 0 < rexp x / Z` | no goals |

### Goal 2: `∑ i, 𝓒.probabilityBetaReal b i = 1`

After R3 (it works under the `∑`), the goal is a sum of quotients that all share the denominator `Z(b)`.

**R5 · `rw [← Finset.sum_div]`** changes the **goal**. The lemma is
`Finset.sum_div : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`, and `←` uses it right to left: it pulls a common
denominator out of the sum. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ)` (any field such as
`ℝ` works for the value type). `simp only [CanonicalEnsemble.probabilityBetaReal, ← Finset.sum_div]` does
R3 and R5 in one call (W1).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R6 · `unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal`** changes the **goal**: `Z(β)`
becomes the sum that defines it. After R5 your numerator is exactly this sum, so the goal reads `Z / Z = 1`
up to unfolding. You do not need to run R6: `exact` (R8) unfolds it by itself. Use it to see why.
Placeholders: `{ι : Type} [MeasurableSpace ι] [Fintype ι] (𝓒 : CanonicalEnsemble ι) (β : ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunctionBetaReal β)` | `⊢ P (∑ i, rexp (-β * 𝓒.energy i))` |

**R7 · `hZ.ne'`** changes the **context** (with `have`): `LT.lt.ne' : a < b → b ≠ a`, so from
`hZ : 0 < a` it gives `a ≠ 0`. (`hZ.ne` gives `0 ≠ a`, the wrong way round for R8.) Placeholders:
`(a : ℝ) (G : Prop)`. Usually written inline: `div_self hZ.ne'`.

| Before | After |
|---|---|
| `hZ : 0 < a ⊢ G` | `hne : a ≠ 0 ⊢ G` |

**R8 · `exact div_self h`** **closes** the goal. The lemma is `div_self : a ≠ 0 → a / a = 1`.
Placeholders: `{α : Type} [DivisionRing α] (a : α) (h : a ≠ 0)` (α has `+ * /`; `ℝ`, `ℚ`, `ℂ` qualify; the
lemma itself is stated for `[GroupWithZero G₀]`, which every division ring is).
`exact` checks the goal against `a / a = 1` up to unfolding definitions, so the two sides of `/` need not
be the same text, only the same after unfolding (R6).

| Before | After |
|---|---|
| `h : a ≠ 0 ⊢ a / a = 1` | no goals |

### Worked combinations (on objects that are not the exercise's)

**W1: normalised weights.** `w g i = g i / ∑ j, g j` for any `g : ι → ℝ`, with `hS : 0 < ∑ j, g j`.
`simp only [w, ← Finset.sum_div]` (R3 + R5 in one call), then `exact div_self hS.ne'` (R7, R8):

```lean-goal
⊢ ∑ i, w g i = 1
⊢ (∑ j, g j) / ∑ j, g j = 1
```

**W2: positivity on its own.** `0 < rexp (y i) / ∑ j, rexp (y j)` closes with `positivity` alone: with
`[Nonempty ι]` it knows a sum of positive terms is positive. In the exercise the denominator is hidden
behind the name `Z(b)`, which `positivity` does not unfold, so it needs `hZ` instead.

---

## Traps

- `div_self hZ` fails: `div_self` wants `a ≠ 0`, and `hZ` says `0 < a`. Use `hZ.ne'` (R7), not `hZ.ne`.
- `rw [div_self hZ.ne']` fails on `(∑ i, rexp (-b * 𝓒.energy i)) / Z(b) = 1`: `rw` matches text, and the
  numerator is not literally `Z(b)`. `exact div_self hZ.ne'` works because `exact` unfolds `Z(b)` (R6, R8).
- `positivity` on `0 < 𝓒.probabilityBetaReal b i` fails: it does not unfold definitions. Unfold first (R3).
- `rw [← Finset.sum_div]` before unfolding finds no `… / …` under the sum. Unfold first (R3).
- `∑ i, f i / a` is `∑ i, (f i / a)`. To write the other one, use parentheses: `(∑ i, f i) / a`.
- In `refine ⟨fun i => ?_, ?_⟩` the first `?_` sits under `fun i`, so `i` is in that goal's context; with a
  plain `⟨?_, ?_⟩` you would still have to `intro i`.
- `sum_probability_eq_one` and `probability_nonneg_finite` (physlib's own versions of this result for
  the temperature-parameterised probability) are BANNED.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < Z(b)` | `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R1 |
| split `(∀ i, A i) ∧ B` | `refine ⟨fun i => ?_, ?_⟩` | R2 |
| expose `p_b(i) = exp(-b E i) / Z(b)` | `unfold CanonicalEnsemble.probabilityBetaReal` | R3 |
| `0 < exp … / Z` with `hZ : 0 < Z` | `positivity` | R4 |
| `∑ i, f i / a → (∑ i, f i) / a` | `rw [← Finset.sum_div]` | R5 |
| unfold + pull out in one go | `simp only [CanonicalEnsemble.probabilityBetaReal, ← Finset.sum_div]` | R3, R5 |
| see what `Z(b)` is | `unfold CanonicalEnsemble.mathematicalPartitionFunctionBetaReal` | R6 |
| `0 < a → a ≠ 0` | `hZ.ne'` | R7 |
| close `a / a = 1` | `exact div_self h` | R8 |
| see the state | infoview | |
