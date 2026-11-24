# E095 · Events and probability measures: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory as probability:
a sample space with a σ-algebra, events (`MeasurableSet`), a measure `μ` with values in the extended
non-negative reals `ENNReal`, the probability-measure assumption, and the real-valued `μ.real`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on `Ω` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `open MeasureTheory ProbabilityTheory` | lets you write `Measure`, `prob_le_one`, … instead of `MeasureTheory.Measure`, `MeasureTheory.prob_le_one` |
| `Ω : Type*`, infoview `Ω : Type u_1` | the sample space, a type in any universe (`Type*` is `Type u` for a fresh universe level `u`; Lean names it `u_1`) |
| `[MeasurableSpace Ω]`, `inst✝¹ : MeasurableSpace Ω` | `Ω` carries a σ-algebra: the family of sets that can be measured. `inst✝` is how an unnamed instance prints |
| `Set Ω` | subsets of `Ω` (a set is a predicate `Ω → Prop`) |
| `MeasurableSet A` | `A` belongs to the σ-algebra: `A` is an *event* |
| `Aᶜ` | the complement `{ω | ω ∉ A}` |
| `A ⊆ B` | every element of `A` is in `B` |
| `s ∩ t` | intersection |
| `μ : Measure Ω` | a (countably additive) measure on `Ω`; applied like a function, `μ A` |
| `μ A : ENNReal` (also written `ℝ≥0∞`) | the measure of `A`, a value in the extended non-negative reals `[0, ∞]` |
| `[IsProbabilityMeasure μ]` | the assumption `μ Set.univ = 1` (`Set.univ` is the whole of `Ω`): `μ` is a probability measure |
| `1 - μ A` in `ENNReal` | *truncated* subtraction: `a - b = 0` when `b ≥ a` (like `ℕ`); `ENNReal` is not a ring |
| `μ.real A : ℝ` | `(μ A).toReal`, the measure as a real number (`∞` would go to `0`; a probability is never `∞`) |
| `case refine_1`, `case refine_2`, … | the goals `refine ⟨?_, ?_, ?_⟩` creates, one per `?_`, in order |

---

## Part 1 · `events_basics`

Statement: for an event `A ⊆ B`, `μ Aᶜ = 1 - μ A ∧ μ A ≤ μ B ∧ μ B ≤ 1`, all in `ENNReal`: the complement
rule, monotonicity, and "a probability is at most 1". Route: split the triple (R1), then each conjunct is one
library lemma (R2, R3, R4), given the measurability or subset proof as its argument.

**R1 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: one goal becomes three. `∧` nests to the right, so
`A ∧ B ∧ C` is `A ∧ (B ∧ C)`, and one `?_` per conjunct works. The term `⟨e₁, e₂, e₃⟩` (anonymous
constructor) builds the whole proof at once when you already have `e₁ e₂ e₃`. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C` | `⊢ A`, `⊢ B`, `⊢ C` |

**R2 · `prob_compl_eq_one_sub`** changes the **goal**. The lemma is
`prob_compl_eq_one_sub : MeasurableSet s → μ sᶜ = 1 - μ s` (with `μ` a probability measure; `μ` and `s` are
implicit, read off the goal or off the argument). So `prob_compl_eq_one_sub hs` is a proof of
`μ sᶜ = 1 - μ s`, usable with `rw` or directly as a term. Placeholders: `{Ω : Type} [MeasurableSpace Ω]
(μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)`.

| Before | After |
|---|---|
| `⊢ P (μ sᶜ)` | `⊢ P (1 - μ s)` |

**R3 · `measure_mono`** changes the **goal**. The lemma is `measure_mono : s ⊆ t → μ s ≤ μ t`, for every
measure (no probability assumption; `#check @measure_mono` shows it for any `μ : F` with
`[OuterMeasureClass F α]`, i.e. anything measure-like, `Measure Ω` included). `apply measure_mono` reduces the inequality to the inclusion; as a
term, `measure_mono hst` proves `μ s ≤ μ t`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
(s t : Set Ω) (hst : s ⊆ t)`.

| Before | After |
|---|---|
| `⊢ μ s ≤ μ t` | `⊢ s ⊆ t` |

**R4 · `prob_le_one`** **closes** `μ s ≤ 1`. The lemma is `prob_le_one : μ s ≤ 1`; it needs
`[IsZeroOrProbabilityMeasure μ]` ("`μ Set.univ` is 0 or 1"), which Lean derives from
`[IsProbabilityMeasure μ]`. Every argument is implicit, so write plain `prob_le_one`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)`.

| Before | After |
|---|---|
| `⊢ μ s ≤ 1` | no goals |

**W1** in `guide.lean` runs R1, R2, R3, R4 on `s ∩ t` for two events `s, t`. The arguments come from
`MeasurableSet.inter` (`hs.inter ht : MeasurableSet (s ∩ t)`; dot notation `hs.inter` means
`MeasurableSet.inter hs` because `hs : MeasurableSet s`) and `Set.inter_subset_left : s ∩ t ⊆ s`. After R1:

```lean-goal
⊢ μ (s ∩ t)ᶜ = 1 - μ (s ∩ t)
⊢ μ (s ∩ t) ≤ μ s
⊢ μ s ≤ 1
```

---

## Part 2 · `real_compl`

Statement: `μ.real A + μ.real Aᶜ = 1` for an event `A`, in `ℝ`. Route: rewrite `μ.real Aᶜ` with the real
complement rule (R5); what is left is an identity of real numbers in the unknown `μ.real A`, closed by `ring`
(R6).

**R5 · `probReal_compl_eq_one_sub`** changes the **goal**. The lemma is
`probReal_compl_eq_one_sub : MeasurableSet s → μ.real sᶜ = 1 - μ.real s` (with `μ` a probability measure).
This `-` is ordinary real subtraction. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
[IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)`.

| Before | After |
|---|---|
| `⊢ P (μ.real sᶜ)` | `⊢ P (1 - μ.real s)` |

**R6 · `ring`** **closes** an equation that holds in every commutative ring. It treats `μ.real s` as an
unknown number. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a + (b - a) = b` | no goals |

**W2** in `guide.lean` chains R5 → R6 on `2 * μ.real sᶜ = 2 - 2 * μ.real s`:

```lean-goal
⊢ 2 * μ.real sᶜ = 2 - 2 * μ.real s
⊢ 2 * (1 - μ.real s) = 2 - 2 * μ.real s
```

---

## Traps

- Subtraction in `ENNReal` truncates at 0 (like `ℕ`), and `ENNReal` is not a ring, so `ring` will not
  rearrange `1 - μ A` there. That is why Part 2 is stated with `μ.real` in `ℝ`, where `ring` works.
- R2 and R5 need `MeasurableSet A`; R3 does not, it only needs `A ⊆ B`. Pass the right hypothesis to each.
- `prob_le_one` takes no explicit arguments: `prob_le_one hA` is an error.
- `rw [probReal_compl_eq_one_sub hA]` rewrites `μ.real Aᶜ`, not `μ.real A`: the left side of the lemma must
  appear literally in the goal.
- `μ A` and `μ.real A` live in different types (`ENNReal` vs `ℝ`); a lemma about one does not rewrite the other.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B ∧ C` | `refine ⟨?_, ?_, ?_⟩` or the term `⟨e₁, e₂, e₃⟩` | R1 |
| `μ sᶜ = 1 - μ s` (`ENNReal`) | `prob_compl_eq_one_sub hs` | R2 |
| `μ s ≤ μ t` from `s ⊆ t` | `measure_mono hst` | R3 |
| `μ s ≤ 1` | `prob_le_one` | R4 |
| `μ.real sᶜ → 1 - μ.real s` (`ℝ`) | `rw [probReal_compl_eq_one_sub hs]` | R5 |
| real arithmetic in the unknown `μ.real s` | `ring` | R6 |
| `MeasurableSet (s ∩ t)` | `hs.inter ht` | W1 |
| see the state | infoview | |
