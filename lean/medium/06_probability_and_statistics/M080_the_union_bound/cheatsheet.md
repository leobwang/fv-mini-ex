# M080 · The union bound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measures `μ : Measure Ω`, the
extended non-negative reals `ℝ≥0∞`, finite sets `Finset ι` with their induction principle, bounded
unions `⋃ i ∈ s` and finite sums `∑ i ∈ s`, the cardinality `s.card` cast into `ℝ≥0∞`, and `calc` chains.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`refine`/`apply`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ≥0∞ → Prop`, `P : Set Ω → Prop`, `P : Finset ι → Prop`). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[Preorder α]` is a
  requirement Lean must find (a *type class* instance). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω`, `ι` | the sample space, and the type that indexes the events |
| `Type u_1`, `Type*` | a type in some universe: read it as `Type` |
| `MeasurableSpace Ω` | a σ-algebra on `Ω` (the sets that get a measure). Not used by the proofs here |
| `μ : Measure Ω` | `MeasureTheory.Measure`: a measure on `Ω`. `μ S : ℝ≥0∞` is the measure of the set `S`. No `IsProbabilityMeasure` is assumed: the bound holds for every measure |
| `ℝ≥0∞` | `ENNReal`, the numbers `[0, ∞]`; it has `+`, `*`, `≤`. All measures take values here. The symbol is available after `open scoped ENNReal` |
| `Finset ι` | a finite set of elements of `ι` (a list without duplicates, up to order) |
| `∅`, `insert a s` | the empty finite set; `s` with `a` added, i.e. `{a} ∪ s` |
| `a ∉ s` | `¬ (a ∈ s)` |
| `∀ i ∈ s, Q i` | `∀ i, i ∈ s → Q i` (as in the hypothesis `h` of Part 2 and the goal after R13) |
| `⋃ i ∈ s, A i` | the union of the sets `A i` over `i ∈ s`; officially `⋃ i, ⋃ (_ : i ∈ s), A i` |
| `t a ∪ U` | union of two sets |
| `∑ i ∈ s, f i` | the finite sum of `f i` over `i ∈ s` (`Finset.sum s f`) |
| `∑ _x ∈ s, b` | a sum whose terms do not depend on the index: `b` added `s.card` times |
| `s.card` | the number of elements of `s`, a natural number `ℕ` |
| `↑s.card` | that natural number cast into `ℝ≥0∞` (`Nat.cast`), so it can multiply `ε` |
| `n • b` | `n : ℕ` times `b` as repeated addition, `b + … + b` (`nsmul`) |
| `inst✝ : …` | an unnamed instance hypothesis, such as `[MeasurableSpace Ω]` or `[DecidableEq ι]` |
| `DecidableEq ι` | a procedure that decides `a = b` for `a b : ι`; `insert` needs it |
| `case empty`, `case insert` | the two goals of induction on a finite set (R2); `case insert.refine_1`, `…refine_2` are the goals a `refine … ?_ ?_` made inside `insert` |

---

## Part 1 · `union_bound`

Statement: for a measure `μ`, a finite index set `s` and sets `A i`,
`μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i)`. In maths (Boole's inequality):
$\mu\big(\bigcup_{i \in s} A_i\big) \le \sum_{i \in s} \mu(A_i)$.
Plan: induction on `s`; the insert step is subadditivity for two sets plus the induction hypothesis.

### Induction on a finite set

**R1 · `classical`** changes the **context**, invisibly: from here on every proposition counts as
decidable (classical logic), so instances such as `DecidableEq ι` are found. The goal and the visible
hypotheses do not change. The statement has no `[DecidableEq ι]`, and `insert a s` (hence R2, R6, R7)
needs one. Placeholders: `{ι : Type} (a b : ι)`; the example uses it for `if h : a = b`.

| Before | After |
|---|---|
| `⊢ a = b ∨ a ≠ b` | `⊢ a = b ∨ a ≠ b` |

**R2 · `induction s using Finset.induction_on with | empty => … | insert a s ha ih => …`** changes the
**goal list and the context**. The principle `Finset.induction_on` says: to prove `P s` for every finite
set, prove `P ∅`, and prove `P (insert a s)` from `a ∉ s` and `P s`. The names after `insert` are, in
order, the new element, the smaller set, the proof `a ∉ s` and the induction hypothesis. Placeholders:
`{ι : Type} [DecidableEq ι] (P : Finset ι → Prop) (s : Finset ι)`. Write the alternatives
at the same indent as `induction` or deeper (the guide uses deeper); `?_` after `=>` leaves that case as a goal.

| Before | After |
|---|---|
| `⊢ P s` | `⊢ P ∅`, `a : ι, s : Finset ι, ha : a ∉ s, ih : P s ⊢ P (insert a s)` |

In the exercise `P s` is `μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i)`, so `ih` is that inequality for the
smaller `s`.

### The empty case

One `simp` closes it: it applies R3–R5 by itself and then closes `0 ≤ 0`.

**R3 · `rw [Finset.sum_empty]`** changes the **goal**. The lemma is `Finset.sum_empty : ∑ x ∈ ∅, f x = 0`.
Placeholders: `{ι : Type} (f : ι → ℝ≥0∞)` (any `AddCommMonoid`, e.g. `ℕ`, `ℝ`, `ℝ≥0∞`).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ ∅, f i)` | `⊢ P 0` |

**R4 · `simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]`** changes the **goal**: the
union over the empty finite set is the empty set. Three lemmas, because `⋃ i ∈ s, t i` is two unions:
`Finset.notMem_empty : a ∉ ∅` turns `i ∈ ∅` into `False`; `Set.iUnion_of_empty` says a union indexed by an
empty type (here the proofs of `False`) is `∅`; `Set.iUnion_empty : ⋃ i, ∅ = ∅`. Placeholders:
`{Ω ι : Type} (t : ι → Set Ω)`.

| Before | After |
|---|---|
| `⊢ P (⋃ i ∈ ∅, t i)` | `⊢ P ∅` |

**R5 · `rw [measure_empty]`** changes the **goal**. The lemma is `measure_empty : μ ∅ = 0`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)`.

| Before | After |
|---|---|
| `⊢ P (μ ∅)` | `⊢ P 0` |

### The insert case: split off one element

**R6 · `rw [Finset.set_biUnion_insert]`** changes the **goal**. The lemma is
`Finset.set_biUnion_insert : ⋃ x ∈ insert a s, t x = t a ∪ ⋃ x ∈ s, t x`. Placeholders:
`{Ω ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι) (t : ι → Set Ω)`. Note the bound variable is renamed
`x`; that is only a name.

| Before | After |
|---|---|
| `⊢ P (⋃ x ∈ insert a s, t x)` | `⊢ P (t a ∪ ⋃ x ∈ s, t x)` |

**R7 · `rw [Finset.sum_insert ha]`** changes the **goal**. The lemma is
`Finset.sum_insert : a ∉ s → ∑ x ∈ insert a s, f x = f a + ∑ x ∈ s, f x` (the hypothesis matters: without
it `a` would be counted twice). Placeholders: `{ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι)
(ha : a ∉ s) (f : ι → ℝ≥0∞)`. Without the argument `ha`, `rw` adds the side goal `a ∉ s`.

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ insert a s, f x)` | `⊢ P (f a + ∑ x ∈ s, f x)` |

In the exercise, R6 acts on the left side (`t = A`) and R7 on the right side (`f = fun i => μ (A i)`), so
the insert goal becomes `μ (A a ∪ ⋃ x ∈ s, A x) ≤ μ (A a) + ∑ x ∈ s, μ (A x)`: a union of two sets on the
left, the matching sum on the right, and `ih` bounds the second pieces.

### Chaining inequalities

**R8 · `exact measure_union_le s t`** **closes** the two-set union bound. The lemma is
`measure_union_le (s t : Set Ω) : μ (s ∪ t) ≤ μ s + μ t` (subadditivity; no measurability needed). The two
sets are explicit arguments: write them, or `measure_union_le _ _` to let Lean read them off the goal.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (s t : Set Ω)`.

| Before | After |
|---|---|
| `⊢ μ (s ∪ t) ≤ μ s + μ t` | closed |

**R9 · `refine hab.trans ?_`** changes the **goal**. `le_trans : a ≤ b → b ≤ c → a ≤ c`; dot notation
`hab.trans` puts `hab : a ≤ b` first, so what is left is `b ≤ c`. `hab` may be any proof term, e.g.
`(measure_union_le _ _).trans …`. Placeholders: `{α : Type} [Preorder α] (a b c : α)` (`≤` is reflexive and
transitive; `ℕ`, `ℝ`, `ℝ≥0∞` qualify).

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

**R10 · `refine add_le_add ?_ ?_`** changes the **goal list**. The lemma is
`add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d`: add two inequalities termwise. As a term, `add_le_add h₁ h₂`.
Placeholders: `(a b c d : ℝ≥0∞)` (also `ℕ`, `ℝ`: any type where `+` respects `≤` on both sides).

| Before | After |
|---|---|
| `⊢ a + c ≤ b + d` | `⊢ a ≤ b`, `⊢ c ≤ d` |

**R11 · `exact le_rfl`** **closes** `a ≤ a`. Its argument is implicit; Lean reads `a` off the goal. Use it
for the summand that is the same on both sides. Placeholders: `{α : Type} [Preorder α] (a : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ a` | closed |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: induction with an `add_le_add` step.** `∑ i ∈ s, f i ≤ ∑ i ∈ s, (f i + g i)`: R1, R2, `simp` for
`empty`; for `insert`, R7 on both sides, then `add_le_add le_self_add ih` (R10;
`le_self_add : a ≤ a + b` in `ℝ≥0∞`). The state before and after `classical` is

```lean-goal
⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, (f i + g i)
```

**W2: three sets.** R9 with R8 for the outer union, then R10 of R8 (inner union) and R11:

```lean-goal
⊢ μ (s ∪ t ∪ u) ≤ μ s + μ t + μ u
⊢ μ (s ∪ t) + μ u ≤ μ s + μ t + μ u
```

---

## Part 2 · `union_bound_uniform`

Statement: if `h : ∀ i ∈ s, μ (A i) ≤ ε` (each event has measure at most `ε : ℝ≥0∞`), then
`μ (⋃ i ∈ s, A i) ≤ ↑s.card * ε`. In maths: $\mu\big(\bigcup_{i\in s} A_i\big) \le |s|\,\varepsilon$.
Milestone: Part 1 gives the first step of a `calc`; no second induction is needed.

**R12 · `calc`** **closes** `a ≤ c` from a chain. The first line names the start, `calc a ≤ b := proof`;
each next line `_ ≤ x := proof` or `_ = x := proof` starts from the previous right side, and Lean combines
`≤` and `=` steps into `≤`. A proof can be a term (`hab`, a lemma applied to arguments) or `by tac`. It can
also stand without `by`, directly after `:=`. Placeholders: `{α : Type} [Preorder α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | closed |

**R13 · `apply Finset.sum_le_sum`** changes the **goal**. The lemma is
`Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`: compare sums term by term. As a
term, `Finset.sum_le_sum h`. `g` may be constant: `∑ i ∈ s, c` is `∑ i ∈ s, (fun _ => c) i`, and Lean
finds that `g` itself. Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `⊢ ∀ i ∈ s, f i ≤ g i` |

**R14 · `rw [Finset.sum_const]`** changes the **goal**. The lemma is
`Finset.sum_const (b : M) : ∑ _x ∈ s, b = s.card • b`: a constant sum is `s.card` copies of `b`, written
with `•` (repeated addition), not `*`. Placeholders: `{ι : Type} (s : Finset ι) (b : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P (∑ _x ∈ s, b)` | `⊢ P (s.card • b)` |

**R15 · `rw [nsmul_eq_mul]`** changes the **goal**. The lemma is `nsmul_eq_mul (n : ℕ) (a : α) : n • a = ↑n * a`:
repeated addition is multiplication by the cast `↑n`. Placeholders: `(n : ℕ) (a : ℝ≥0∞)` (any semiring:
`ℕ`, `ℝ`, `ℝ≥0∞`).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

**W3: a constant sum as a product.** R14, R15, then `mul_comm`; the last `rw` closes the goal by `rfl`:

```lean-goal
⊢ ∑ _i ∈ s, 2 = 2 * ↑s.card
⊢ s.card • 2 = 2 * ↑s.card
⊢ ↑s.card * 2 = 2 * ↑s.card
```

---

## Traps

- Without R1, `induction s using Finset.induction_on` does not fail at once: it leaves an extra goal
  `⊢ DecidableEq ι` (`case inst`) and reports "unsolved goals". Put `classical` first.
- `rw [Finset.sum_insert]` without `ha` adds a side goal `a ∉ s`. Pass `ha` (R7).
- `measure_union_le` takes the two sets explicitly: `measure_union_le _ _`, not `measure_union_le` alone,
  when you chain it with `.trans` (R8, R9).
- `Finset.sum_const` gives `s.card • ε`, but the goal has `↑s.card * ε` (the statement writes `s.card * ε`;
  Lean inserts the cast `↑`): finish with `nsmul_eq_mul` (R14, R15). In a `calc` line you may write either
  `s.card * ε` or `↑s.card * ε`.
- Do not repeat the induction in Part 2: Part 1 is the first `calc` step (`union_bound μ s A`).
- Banned (they are the theorem): `measure_biUnion_finset_le`, `measure_biUnion_le`,
  `measure_iUnion_fintype_le`, `measure_iUnion_le`, and the search tactics `exact?`, `apply?`, `rw?`, `hint`,
  `try?`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `DecidableEq ι` for `insert` | `classical` | R1 |
| induct on `s : Finset ι` | `induction s using Finset.induction_on with \| empty => … \| insert a s ha ih => …` | R2 |
| empty case | `simp` | R3–R5 |
| `∑ x ∈ ∅, f x → 0` | `rw [Finset.sum_empty]` | R3 |
| `⋃ i ∈ ∅, t i → ∅` | `simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]` | R4 |
| `μ ∅ → 0` | `rw [measure_empty]` | R5 |
| `⋃ x ∈ insert a s, t x → t a ∪ ⋃ x ∈ s, t x` | `rw [Finset.set_biUnion_insert]` | R6 |
| `∑ x ∈ insert a s, f x → f a + ∑ x ∈ s, f x` | `rw [Finset.sum_insert ha]` | R7 |
| `μ (s ∪ t) ≤ μ s + μ t` | `measure_union_le _ _` | R8 |
| `a ≤ c` from `hab : a ≤ b` | `hab.trans ?_` | R9 |
| `a + c ≤ b + d` | `add_le_add h₁ h₂` | R10 |
| `a ≤ a` | `le_rfl` | R11 |
| chain `≤` and `=` steps | `calc a ≤ b := … ; _ = c := …` (one step per line) | R12 |
| compare sums termwise | `Finset.sum_le_sum h` | R13 |
| `∑ _x ∈ s, b → s.card • b` | `rw [Finset.sum_const]` | R14 |
| `n • a → ↑n * a` | `rw [nsmul_eq_mul]` | R15 |
| use Part 1 | `union_bound μ s A` | milestone |
| see the state | infoview | |
