# M082 · Complements of independent events: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory and probability:
events as `Set Ω`, measures `μ : Measure Ω`, probability measures, independence `IndepSet`, and the
extended non-negative reals `ENNReal` (`[0, ∞]`) in which measures take values, with their truncated
subtraction.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ENNReal → Prop` or `P : Set Ω → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type (the sample space). A bracket is a
  requirement (a *type class*): `[MeasurableSpace Ω]` says `Ω` carries a σ-algebra (a chosen family of
  "measurable" subsets closed under complement and countable union); `[IsProbabilityMeasure μ]` says
  `μ Set.univ = 1`. A probability measure is automatically a finite measure (`[IsFiniteMeasure μ]`, needed by
  R5) and meets `[IsZeroOrProbabilityMeasure μ]` (needed by R1); Lean finds both by itself.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω`, `Set Ω` | the sample space; an event is a subset `s : Set Ω` |
| `Ω : Type u_1` | `Ω` is a type in some universe level `u_1`; Lean prints `Type*` binders this way. Read it as `Ω : Type` |
| `Measure Ω` | a measure on `Ω` (from `MeasureTheory`); `μ s` is the measure of the event `s` |
| `ENNReal` | `[0, ∞]`, the type of `μ s`. Mathlib's scoped notation for it is `ℝ≥0∞` (only after `open ENNReal`) |
| `⊤` | `∞`, the top element of `ENNReal` (printed `∞` only after `open ENNReal`) |
| `a - b` in `ENNReal` | truncated subtraction: `max (a - b) 0`, and `∞ - ∞ = 0`. Not a ring |
| `sᶜ` | the complement `Ω \ s` |
| `s ∩ t`, `s \ t` | intersection; difference (points of `s` not in `t`) |
| `Set.univ` | the whole space `Ω` (the sure event) |
| `MeasurableSet s` | `s` belongs to the σ-algebra; measure lemmas need it |
| `IndepSet s t μ` | `s`, `t` are independent under `μ`: `μ (s ∩ t) = μ s * μ t` (R1). Its `μ` argument defaults to `volume` if omitted |
| `inst✝ : IsProbabilityMeasure μ`, `inst✝¹ : MeasurableSpace Ω` | anonymous instance hypotheses from `[…]` binders (the superscript only numbers them) |

---

## Part 1 · `indep_compl`

Statement: if `A`, `B` are measurable and independent under a probability measure `μ`, then `A` and `Bᶜ` are
independent. In numbers: from $\mu(A\cap B)=\mu(A)\mu(B)$ derive
$\mu(A\cap B^c)=\mu(A)-\mu(A\cap B)=\mu(A)-\mu(A)\mu(B)=\mu(A)(1-\mu(B))=\mu(A)\,\mu(B^c)$, with every `-` in
`ENNReal`.

### Independence ↔ a product equation

**R1 · `rw [indepSet_iff_measure_inter_eq_mul hs ht μ]`** changes the **goal**. The lemma is
`MeasurableSet s → MeasurableSet t → ∀ μ [IsZeroOrProbabilityMeasure μ], IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
(hs : MeasurableSet s) (ht : MeasurableSet t)`. Pass `μ` explicitly: it is an `autoParam` (an argument with a
default value, here `volume`), and leaving it out does not let Lean infer it from the goal.

| Before | After |
|---|---|
| `⊢ IndepSet s t μ` | `⊢ μ (s ∩ t) = μ s * μ t` |

**R2 · `ht.compl`** (lemma `MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ`) is a term. Dot notation
`ht.compl` means `MeasurableSet.compl ht` because `ht : MeasurableSet t`. Used in a `have` it changes the
**context**; usually you pass it straight to R1 as the second argument. Placeholders: `(t : Set Ω)
(ht : MeasurableSet t)`.

| Before | After |
|---|---|
| `⊢ G` | `htc : MeasurableSet tᶜ ⊢ G` |

**R3 · `rw [lemma] at h`** changes the **context**: `h`'s type is rewritten, the goal is left alone. Here with
R1's lemma, to turn the hypothesis `h : IndepSet s t μ` into an equation you can `rw` with.

| Before | After |
|---|---|
| `h : IndepSet s t μ ⊢ μ (s ∩ t) = μ s * μ t` | `h : μ (s ∩ t) = μ s * μ t ⊢ μ (s ∩ t) = μ s * μ t` |

### Splitting an event and cancelling in `ENNReal`

**R4 · `rw [← measure_inter_add_sdiff s ht]`** changes the **goal**. The lemma is
`measure_inter_add_sdiff (s) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s` (additivity over the
disjoint split $s = (s\cap t)\sqcup(s\setminus t)$). Right to left it replaces every `μ s` by the sum, so give
`s` explicitly. Placeholders: `(μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t)`; no finiteness needed.

| Before | After |
|---|---|
| `⊢ P (μ s)` | `⊢ P (μ (s ∩ t) + μ (s \ t))` |

**R5 · `measure_ne_top μ s`** is a term: `measure_ne_top (μ) [IsFiniteMeasure μ] (s) : μ s ≠ ⊤`. In a `have` it
changes the **context**; usually you pass it to R6 or R9, with `_` for `s` when Lean can infer it.
Placeholders: `(μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : μ s ≠ ⊤ ⊢ G` |

**R6 · `rw [ENNReal.add_sub_cancel_left ha]`** changes the **goal**. The lemma is
`a ≠ ⊤ → a + b - a = b`. Without `ha` it is false: `⊤ + 1 - ⊤ = ⊤ - ⊤ = 0 ≠ 1`. Placeholders:
`(a b : ENNReal) (ha : a ≠ ⊤)`.

| Before | After |
|---|---|
| `⊢ P (a + b - a)` | `⊢ P b` |

**R7 · `rw [Set.sdiff_eq]`** changes the **goal**. The lemma is `Set.sdiff_eq (s t) : s \ t = s ∩ tᶜ`.
Placeholders: `{Ω : Type} (s t : Set Ω)`.

| Before | After |
|---|---|
| `⊢ P (s \ t)` | `⊢ P (s ∩ tᶜ)` |

After R4, R6, R7 both sides of an equation can become the same text; `rw` then closes it (R11).

### Complements and distributing

**R8 · `rw [prob_compl_eq_one_sub ht]`** changes the **goal**. The lemma is
`[IsProbabilityMeasure μ] → MeasurableSet t → μ tᶜ = 1 - μ t`. Placeholders: `(μ : Measure Ω)
[IsProbabilityMeasure μ] (t : Set Ω) (ht : MeasurableSet t)`.

| Before | After |
|---|---|
| `⊢ P (μ tᶜ)` | `⊢ P (1 - μ t)` |

**R9 · `rw [ENNReal.mul_sub (fun _ _ => ha)]`** changes the **goal**. The lemma is
`ENNReal.mul_sub : (0 < c → c < b → a ≠ ⊤) → a * (b - c) = a * b - a * c`. Its hypothesis is a function of two
(unused) proofs, so wrap `ha : a ≠ ⊤` as `fun _ _ => ha`. Placeholders: `(a b c : ENNReal) (ha : a ≠ ⊤)`.

| Before | After |
|---|---|
| `⊢ P (a * (b - c))` | `⊢ P (a * b - a * c)` |

**R10 · `rw [mul_one]`** changes the **goal**. The lemma is `mul_one (a) : a * 1 = a`, for any
`[MulOneClass M]` (a type with `*` and `1`; `ENNReal`, `ℕ`, `ℝ` qualify). Placeholders: `(a : ENNReal)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**R11 · `rw` closes `x = x`** changes the **goal list**: after the last rewrite `rw` tries `rfl`, so when both
sides have become identical the goal disappears and no `exact`/`rfl` is needed (adding one is then an error,
"no goals"). Placeholders: `(a b : ENNReal) (h : a = b)`.

| Before | After `rw [mul_one, h]` |
|---|---|
| `h : a = b ⊢ a * 1 = b` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: the split written with a complement.** R7 right to left, then R4 left to right; R11 closes it.

```lean-goal
⊢ μ (s ∩ t) + μ (s ∩ tᶜ) = μ s
⊢ μ (s ∩ t) + μ (s \ t) = μ s
```

**W2: every event is independent of `Set.univ`.** R1 with `MeasurableSet.univ` gives the equation, then `simp`
uses `Set.inter_univ` and `measure_univ` (`μ Set.univ = 1`) and `mul_one`:

```lean-goal
⊢ IndepSet s Set.univ μ
⊢ μ (s ∩ Set.univ) = μ s * μ Set.univ
```

**W3: cancel a measure.** `have hs := measure_ne_top μ s` (R5), then `rw [ENNReal.add_sub_cancel_left hs]` (R6):

```lean-goal
⊢ μ s + b - μ s = b
```

---

## Traps

- `ENNReal` subtraction truncates at 0 and `∞ - ∞ = 0`, so `ring`, `linarith` and `abel` cannot cancel or
  distribute over `-`. Every cancellation goes through a named lemma with a `≠ ⊤` side condition (R6, R9), which
  R5 supplies.
- Leaving `μ` out of R1 (`indepSet_iff_measure_inter_eq_mul hA hB`) makes Lean use the default `volume`, which
  needs a `MeasureSpace Ω` instance that does not exist here: the `rw` fails.
- R1 for the goal needs `MeasurableSet Bᶜ`, not `MeasurableSet B`: pass `hB.compl` (R2).
- `rw [← measure_inter_add_sdiff A hB]` rewrites every `μ A`. In a goal `μ (A ∩ Bᶜ) = μ A - μ (A ∩ B)` that is
  exactly one occurrence (`μ (A ∩ B)` is not `μ A`), but on the full goal it would also hit the right side.
  Prove the split as a separate `have` first.
- `rw` closes the goal itself when both sides match (R11); a trailing `rfl` then fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `IndepSet s t μ` ↔ `μ (s ∩ t) = μ s * μ t` (goal) | `rw [indepSet_iff_measure_inter_eq_mul hs ht μ]` | R1 |
| measurability of a complement | `ht.compl` | R2 |
| same, in a hypothesis | `rw [indepSet_iff_measure_inter_eq_mul hs ht μ] at h` | R3 |
| `μ s → μ (s ∩ t) + μ (s \ t)` | `rw [← measure_inter_add_sdiff s ht]` | R4 |
| `μ s ≠ ⊤` | `measure_ne_top μ s` (or `measure_ne_top μ _`) | R5 |
| `a + b - a → b` in `ENNReal` | `rw [ENNReal.add_sub_cancel_left ha]` | R6 |
| `s \ t → s ∩ tᶜ` | `rw [Set.sdiff_eq]` | R7 |
| `μ tᶜ → 1 - μ t` | `rw [prob_compl_eq_one_sub ht]` | R8 |
| `a * (b - c) → a * b - a * c` in `ENNReal` | `rw [ENNReal.mul_sub (fun _ _ => ha)]` | R9 |
| `a * 1 → a` | `rw [mul_one]` | R10 |
| finish when both sides match | nothing: `rw` closes it | R11 |
| add a fact | `have h1 : T := by …` | TACTIC_STATES |
| see the state | infoview | |
