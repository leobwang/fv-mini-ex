# E100 · Conditional probability: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rw [h]` (E009). The measure-theory setup of
E095: a sample space `Ω` with a σ-algebra, events `MeasurableSet A`, a measure `μ : Measure Ω` with values
in `ENNReal`, and `[IsProbabilityMeasure μ]`.
**New here:** the conditional probability `μ[t | s]` (Mathlib's `ProbabilityTheory.cond`) and how to unfold
it; algebra by hand in `ENNReal`, where `a⁻¹ * a = 1` needs `a ≠ 0` and `a ≠ ∞`.

## How to read an entry

Each entry is one lemma used with `rw` or `exact`. It says what changes (**goal**, **context**, or **goal
list**), gives the lemma's statement, lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `open MeasureTheory ProbabilityTheory` | lets you write `Measure`, `cond_apply`, `μ[t \| s]` without the `MeasureTheory.` / `ProbabilityTheory.` prefixes; the notation `μ[t \| s]` exists only after this `open` |
| `Ω : Type*`, infoview `Ω : Type u_1` | the sample space, a type in any universe (`Type*` is `Type u` for a fresh universe level `u`, which Lean names `u_1`) |
| `[MeasurableSpace Ω]`, infoview `inst✝¹ : MeasurableSpace Ω` | `Ω` carries a σ-algebra, the family of sets that can be measured. `inst✝`, `inst✝¹` are how unnamed instance arguments print |
| `Set Ω`, `A B : Set Ω` | subsets of `Ω` (a set is a predicate `Ω → Prop`) |
| `MeasurableSet A` | `A` belongs to the σ-algebra: `A` is an *event* |
| `μ : Measure Ω`, `μ A` | a (countably additive) measure on `Ω`, applied to a set like a function; `μ A : ENNReal` is the probability of `A` |
| `[IsProbabilityMeasure μ]`, infoview `inst✝ : IsProbabilityMeasure μ` | the assumption `μ Set.univ = 1` (`Set.univ` is all of `Ω`); it implies `IsFiniteMeasure μ`: every `μ s` is finite (R3) |
| `μ[t \| s]` | `cond μ s t`, the conditional probability $P(t \mid s)$. Note the order: the event conditioned on (`s`) is written *last*. `cond μ s` is the measure $(\mu\,s)^{-1}\cdot\mu$ restricted to `s` |
| `μ (s ∩ t)` | the measure of the intersection, $P(s \cap t)$ |
| `ENNReal` (also written `ℝ≥0∞`) | the extended non-negative reals $[0, \infty]$, where measures take their values |
| `⊤` | `∞ : ENNReal` ("top", the largest element). `a ≠ ⊤` says `a` is finite |
| `(μ s)⁻¹` | the inverse in `ENNReal`. Convention: `0⁻¹ = ⊤` and `⊤⁻¹ = 0`, so `a⁻¹ * a = 1` fails at `a = 0` (`⊤ * 0 = 0`) and at `a = ⊤` |
| `a * b * c` | `(a * b) * c`: `*` groups to the left |

---

## Part 1 · `cond_of_indep`

Statement: for an event `A` with `μ A ≠ 0` and `μ (A ∩ B) = μ A * μ B` (independence), `μ[B | A] = μ B`, i.e.
$P(B \mid A) = P(B)$. Route: unfold `μ[B | A]` to `(μ A)⁻¹ * μ (A ∩ B)` (R1); substitute the independence
hypothesis with `rw [h]`; regroup so `(μ A)⁻¹ * μ A` appears (R2); cancel it (R4, whose second side condition
comes from R3); drop the `1 *` (R5).

### Unfolding

**R1 · `cond_apply`** changes the **goal**. The lemma is
`cond_apply : MeasurableSet s → ∀ (μ : Measure Ω) (t : Set Ω), μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`, the definition
$P(t \mid s) = P(s \cap t) / P(s)$ written with an inverse. `s` is implicit (read off `hs`), `μ` and `t` are
explicit but may be left out for `rw`, which finds them in the goal. Only the conditioning event needs to be
measurable. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω)
(hs : MeasurableSet s)`.

Before (first line) and after (second line). The states are in a block, not a table, because the `|` of
`μ[t | s]` would split a table cell:

```lean-goal
⊢ P μ[t | s]
⊢ P ((μ s)⁻¹ * μ (s ∩ t))
```

### Algebra in `ENNReal`

`ENNReal` has `*`, `⁻¹` and `1`, but no negatives, so `ring`, `field_simp` and `group` do not apply. You move
factors with the monoid lemmas R2, R5 and cancel with R4.

**R2 · `rw [← mul_assoc]`** changes the **goal**. The lemma is `mul_assoc : a * b * c = a * (b * c)`; with `←`
it is used right to left and regroups `a * (b * c)` as `(a * b) * c`, which prints `a * b * c`. Placeholders:
`{α : Type} [Monoid α] (a b c : α)`; a *monoid* is a type with an associative `*` and a unit `1`. `ℕ`, `ℝ`
and `ENNReal` qualify.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R3 · `measure_ne_top`** **closes** a goal `μ s ≠ ⊤`. The lemma is
`measure_ne_top : ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω), μ s ≠ ⊤`. A probability measure is
finite, so `[IsProbabilityMeasure μ]` supplies `[IsFiniteMeasure μ]`. Both `μ` and `s` are explicit: the
term is `measure_ne_top μ s`, and you will mostly pass it as an argument to R4 rather than prove a goal with
it. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)`.

| Before | After |
|---|---|
| `⊢ μ s ≠ ⊤` | no goals |

**R4 · `rw [ENNReal.inv_mul_cancel ha0 hatop]`** changes the **goal**. The lemma is
`ENNReal.inv_mul_cancel : a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1`, with `a` implicit (read off the arguments). It needs
`a⁻¹ * a` to appear literally, adjacent and in this order. Placeholders: `(a : ENNReal) (ha0 : a ≠ 0)
(hatop : a ≠ ⊤)`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * a)` | `⊢ P 1` |

**R5 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul : 1 * a = a`. If the goal becomes `x = x`,
`rw` closes it by `rfl` on its own. Placeholders: `{α : Type} [Monoid α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

### Worked combinations (in `guide.lean`, on objects that are not the exercise's)

**W1: cancelling a factor.** `a⁻¹ * (a * x) = x` for `a x : ENNReal` with `ha0 : a ≠ 0`, `hatop : a ≠ ⊤`. R2,
R4, R5 in turn; the last `rw` closes `x = x`:

```lean-goal
⊢ a⁻¹ * (a * x) = x
⊢ a⁻¹ * a * x = x
⊢ 1 * x = x
```

**W2: an event conditioned on itself.** `μ[s | s] = 1` for an event `s` with `μ s ≠ 0`. R1, then
`Set.inter_self : s ∩ s = s`, then R4 with `measure_ne_top μ s` (R3) as its second argument:

```lean-goal
⊢ μ[s | s] = 1
⊢ (μ s)⁻¹ * μ (s ∩ s) = 1
⊢ (μ s)⁻¹ * μ s = 1
```

---

## Traps

- `ring` and `field_simp` do not cancel `a⁻¹ * a` in `ENNReal`: it is not a field, and the cancellation is
  false at `a = 0` and `a = ⊤`. Rewrite with R4 and supply both side conditions.
- R4's second condition is `μ A ≠ ⊤`, not given as a hypothesis: build it with `measure_ne_top μ A` (R3).
- `rw [ENNReal.inv_mul_cancel …]` fails on `(μ A)⁻¹ * (μ A * μ B)`: the pattern `(μ A)⁻¹ * μ A` is not a
  subterm until you regroup with `← mul_assoc` (R2).
- `μ[B | A]` conditions on `A` (the event after the bar), so `cond_apply` needs `MeasurableSet A`, here `hA`.
  It unfolds to `μ (A ∩ B)`, with `A` first: that is the left side of `h`, so `rw [h]` matches.
- If you leave out R4's second argument, `rw [ENNReal.inv_mul_cancel hA0]` still rewrites, but adds the side goal
  `⊢ μ A ≠ ⊤` after the main one (TACTIC_STATES, `rw [lemma (by tac)]`). Close it with `exact measure_ne_top μ A`
  (R3) once the main goal is done, or pass the argument up front as the skeleton does.
- Without `open ProbabilityTheory` the notation `μ[B | A]` does not parse; the spec region opens it for you.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `μ[t \| s] → (μ s)⁻¹ * μ (s ∩ t)` | `rw [cond_apply hs]` | R1 |
| replace `μ (A ∩ B)` by its value | `rw [h]` | TACTIC_STATES |
| `a * (b * c) → a * b * c` | `rw [← mul_assoc]` | R2 |
| `μ s ≠ ⊤` (finite measure) | `measure_ne_top μ s` | R3 |
| `a⁻¹ * a → 1` in `ENNReal` | `rw [ENNReal.inv_mul_cancel ha0 hatop]` | R4 |
| `1 * a → a` | `rw [one_mul]` | R5 |
| `s ∩ s → s` | `rw [Set.inter_self]` | W2 |
| several rewrites at once | `rw [l₁, l₂, …]` (left to right) | E009 R2 |
| see the state | infoview | |
