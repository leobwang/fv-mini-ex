# M079 · Inclusion–exclusion for two events: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `rw [h]`, `exact`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory (measurable
spaces, measurable sets, measures), set difference `\`, `Disjoint`, and the extended non-negative reals
`ℝ≥0∞` in which measures take their values.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on `Ω` (a *type class*): here, that `Ω` comes with a σ-algebra.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω : Type*}`, `Ω : Type u_1` | `Ω` is any type, in any universe: `Type*` (Mathlib notation) introduces a fresh universe variable, which the infoview names `u_1`. Read it as `Type` |
| `open MeasureTheory` | lets you drop the prefix: `Measure` is `MeasureTheory.Measure`, `measure_union` is `MeasureTheory.measure_union` (likewise R5). The spec's `open` line is in force in the proof |
| `Set Ω` | subsets of the type `Ω`; a set `s` is a predicate `Ω → Prop` |
| `s ∪ t`, `s ∩ t` | union, intersection |
| `s \ t` | set difference `{x ∈ s ∣ x ∉ t}`. It binds tighter than `∪`/`∩`: `s ∪ t \ s` is `s ∪ (t \ s)` |
| `Disjoint s t` | `s ∩ t = ∅` (Mathlib states it order-theoretically; you only pass proofs of it) |
| `[MeasurableSpace Ω]`, `inst✝ : MeasurableSpace Ω` | `Ω` carries a σ-algebra 𝓕 (a family of subsets closed under complement and countable union). `inst✝` is that unnamed instance |
| `MeasurableSet s` | `s ∈ 𝓕`; the hypotheses `hA`, `hB` say the events are measurable |
| `Measure Ω`, `μ : Measure Ω` | a measure on 𝓕: countably additive, `μ ∅ = 0`. A probability measure is the special case `μ univ = 1` |
| `μ s` | the measure of `s`. `μ` is a structure applied to a set through a coercion to a function (`DFunLike.coe`); the infoview prints just `μ s` |
| `ℝ≥0∞`, `ENNReal` | the same type: `[0, ∞]`, non-negative reals plus `∞`. Every `μ s` lives here |
| `a - b` in `ℝ≥0∞` | truncated: `max (a - b) 0`, and `∞ - ∞ = 0`. That is why the statement has `+` on both sides |

---

## Part 1 · `union_add_inter`

Statement: for measurable `A B : Set Ω` and any measure `μ`, `μ (A ∪ B) + μ (A ∩ B) = μ A + μ B`. In words:
the union plus the overlap weighs as much as the two events. The proof cuts `A ∪ B` into the disjoint pieces
`A`, `B \ A` and cuts `B` into `B ∩ A`, `B \ A`; then both sides are sums of the same three numbers.

### Cutting the union (fact 1: `μ (A ∪ B) = μ A + μ (B \ A)`)

**R1 · `rw [← Set.union_sdiff_self]`** changes the **goal**. The lemma is
`Set.union_sdiff_self : s ∪ t \ s = s ∪ t` (with `s t` implicit); `←` uses it right to left, so the first
`_ ∪ _` in the goal becomes `_ ∪ _ \ _`. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ P (s ∪ t)` | `⊢ P (s ∪ t \ s)` |

**R2 · `Set.disjoint_sdiff_right`** is a proof term of `Disjoint s (t \ s)`: a set and what another set has
outside it share no point. `s` and `t` are implicit, so Lean fills them in from where you use it. Here it
**closes** the goal; in the exercise you pass it as the first argument of R4. Placeholders:
`{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ Disjoint s (t \ s)` | no goals |

**R3 · `ht.diff hs`** (lemma `MeasurableSet.diff`) is a proof term of `MeasurableSet (t \ s)`. The lemma is
`MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)`; `ht.diff hs` is dot notation for
`MeasurableSet.diff ht hs`, allowed because `ht : MeasurableSet t`. Here it **closes** the goal; in the
exercise it is the second argument of R4. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (s t : Set Ω)
(hs : MeasurableSet s) (ht : MeasurableSet t)`.

| Before | After |
|---|---|
| `⊢ MeasurableSet (t \ s)` | no goals |

**R4 · `rw [measure_union hd ht]`** changes the **goal**: the measure of a disjoint union becomes a sum. The
lemma is `measure_union : Disjoint s₁ s₂ → MeasurableSet s₂ → μ (s₁ ∪ s₂) = μ s₁ + μ s₂`. Only the **second**
set must be measurable. With both proofs passed in, no side goal appears, and if the two sides of the goal
become identical, `rw` closes it by itself. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
(s t : Set Ω) (hd : Disjoint s t) (ht : MeasurableSet t)`, `P : ℝ≥0∞ → Prop`.

| Before | After |
|---|---|
| `⊢ P (μ (s ∪ t))` | `⊢ P (μ s + μ t)` |

### Cutting `B` (fact 2: `μ B = μ (B ∩ A) + μ (B \ A)`)

**R5 · `measure_inter_add_sdiff s ht`** is the equation `μ (s ∩ t) + μ (s \ t) = μ s` for a measurable `t`
(the lemma `measure_inter_add_sdiff (s) : MeasurableSet t → μ (s ∩ t) + μ (s \ t) = μ s`; `s` is explicit,
`t` is read off `ht`). Used with `rw` it changes the **goal**. Placeholders: `{Ω : Type} [MeasurableSpace Ω]
(μ : Measure Ω) (s t : Set Ω) (ht : MeasurableSet t)`.

| Before | After |
|---|---|
| `⊢ P (μ (s ∩ t) + μ (s \ t))` | `⊢ P (μ s)` |

**R6 · `e.symm`** (lemma `Eq.symm : a = b → b = a`) flips an equation. Inside `have h : b = a := e.symm` it
changes the **context**. Use it when a lemma gives `x + y = z` but you need `z = x + y` to rewrite `z` away.
Placeholders: `{α : Type} (a b : α) (e : a = b)`.

| Before | After |
|---|---|
| `e : a = b ⊢ G` | `h : b = a ⊢ G` |

### Assembling

After `rw [fact1, fact2]` (TACTIC_STATES, "Rewriting") the goal is a sum of `μ (…)` terms, but one side has
`A ∩ B` and the other `B ∩ A`.

**R7 · `rw [Set.inter_comm s t]`** changes the **goal**: `s ∩ t` becomes `t ∩ s`. The lemma is
`Set.inter_comm (a b : Set α) : a ∩ b = b ∩ a`. Without arguments, `rw [Set.inter_comm]` swaps the first
`_ ∩ _` it meets, and every copy of that same intersection. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ P (s ∩ t)` | `⊢ P (t ∩ s)` |

**R8 · `ring`** **closes** an identity built from `+`, `*` and numerals in a commutative semiring; `ℝ≥0∞` is
one. It treats each `μ (…)` as an unknown, so the two sets inside must already be written the same way (R7).
Placeholders: `(a b c : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ a + b + c = b + (c + a)` | no goals |

### Worked combinations (W1–W2, on statements that are not the exercise's)

**W1: the mirror cut `s ∪ t = (s \ t) ∪ t`.** `Set.sdiff_union_self : s \ t ∪ t = s ∪ t` and
`Set.disjoint_sdiff_left : Disjoint (t \ s) s` are the mirror images of R1 and R2. Rewrite the union, then
R4; the second `rw` leaves two identical sides and closes the goal:

```lean-goal
⊢ μ (s ∪ t) = μ (s \ t) + μ t
⊢ μ (s \ t ∪ t) = μ (s \ t) + μ t
```

**W2: R5 flipped by R6, rewritten, rearranged by R8.** `have h : μ s = μ (s ∩ t) + μ (s \ t) :=
(measure_inter_add_sdiff s ht).symm`, then `rw [h]`, then `ring`:

```lean-goal
⊢ μ u + μ s = μ (s \ t) + μ u + μ (s ∩ t)
⊢ μ u + (μ (s ∩ t) + μ (s \ t)) = μ (s \ t) + μ u + μ (s ∩ t)
```

---

## Traps

- Do not subtract. In `ℝ≥0∞`, `a - b` is truncated and `∞ - ∞ = 0`, so the textbook form
  `μ (A ∪ B) = μ A + μ B - μ (A ∩ B)` needs `μ (A ∩ B) ≠ ∞` and special lemmas. The statement keeps `+` on both
  sides; so does every step of the proof.
- `\` binds tighter than `∪`: `A ∪ B \ A` is `A ∪ (B \ A)`, not `(A ∪ B) \ A` (which is `B \ A`).
- `measure_union` wants measurability of the **second** set only. `measure_union hd hA` with `hA` about the
  first set is a type error.
- `rw [h]` with `h : μ B = …` rewrites the term `μ B` only, never `μ (B \ A)` or `μ (B ∩ A)`: those are
  different terms. Likewise a fact about `μ (A ∪ B)` only fires on that exact union, not on `μ (B ∪ A)`.
- `ring` sees `μ (A ∩ B)` and `μ (B ∩ A)` as two different unknowns. Make them the same with R7 first.
- The library lemma that proves the whole statement is on the `BANNED:` line; so are `exact?`, `apply?`, `rw?`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `s ∪ t` → `s ∪ t \ s` (disjoint pieces) | `rw [← Set.union_sdiff_self]` | R1 |
| `Disjoint s (t \ s)` | `Set.disjoint_sdiff_right` | R2 |
| `MeasurableSet (t \ s)` | `ht.diff hs` | R3 |
| `μ (s ∪ t)` → `μ s + μ t` for disjoint `s, t` | `rw [measure_union hd ht]` | R4 |
| `μ (s ∩ t) + μ (s \ t) = μ s` | `measure_inter_add_sdiff s ht` | R5 |
| flip `a = b` to `b = a` | `e.symm` | R6 |
| add a fact | `have h : T := by …` / `:= term` | TACTIC_STATES |
| use the facts | `rw [h1, h2]` | TACTIC_STATES |
| `s ∩ t` → `t ∩ s` | `rw [Set.inter_comm]` / `rw [Set.inter_comm s t]` | R7 |
| rearrange a sum in `ℝ≥0∞` | `ring` | R8 |
| see the state | infoview | |
