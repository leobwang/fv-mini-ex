# M081 · Total probability and Bayes: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory: measures,
measurable sets, the extended non-negative reals `ℝ≥0∞`, conditional probability `μ[t | s]`, indexed
unions `⋃`, infinite sums `∑'`, and `Pairwise`/`Disjoint`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp_rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ≥0∞ → Prop` or `P : Set Ω → Prop`). The step changes only the
  part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as
  `[IsFiniteMeasure μ]` is a requirement Lean must find (a *type class* instance). Each entry says when
  the exercise meets it.
- States that contain `μ[t | s]` are shown in a ```` ```lean-goal ```` block, first line before, second
  line after (a `|` cannot sit inside a table cell).
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω`, `ι` | the sample space and the index type of the partition |
| `MeasurableSpace Ω` | a σ-algebra on `Ω`: the family of sets that have a probability |
| `MeasurableSet s` | `s` is in that σ-algebra |
| `μ : Measure Ω` | a measure; `μ s : ℝ≥0∞` is the measure (here: probability) of the set `s` |
| `ℝ≥0∞` | `ENNReal`, the numbers `[0, ∞]`. `+`, `*`, `⁻¹` exist, but `0⁻¹ = ∞` and there is no subtraction law |
| `IsProbabilityMeasure μ` | `μ Set.univ = 1`. It gives `IsFiniteMeasure μ` (`μ Set.univ < ∞`) automatically, which R1 and R12 require |
| `μ[t \| s]` | `ProbabilityTheory.cond μ s t`: the probability of `t` given `s`, equal to `(μ s)⁻¹ * μ (s ∩ t)`. Note the order: the conditioning set `s` comes **second** in the notation but first in `cond` |
| `Set.univ` | the whole space `Ω` |
| `s ∩ t`, `s ⊆ t` | intersection and inclusion of sets `s t : Set Ω`; on sets, `≤` is `⊆` |
| `(μ s)⁻¹`, `a / b` | inverse and division in `ℝ≥0∞`; `a / b` is by definition `a * b⁻¹` (R13) |
| `⋃ i, f i` | the union of the sets `f i` over all `i : ι` |
| `∑ i, f i` | a finite sum over all of `ι` (needs `[Fintype ι]`, "`ι` is finite") |
| `∑' (i : ι), f i` | `tsum`: the sum of a possibly infinite family; for a finite `ι` it equals `∑ i, f i` (R11) |
| `∑ x, μ (B x ∩ A)` | the same as `∑ i, μ (B i ∩ A)`: `simp_rw` renames the bound variable |
| `Disjoint a b` | `a ∩ b = ∅` |
| `Pairwise R` | `∀ ⦃i j⦄, i ≠ j → R i j` (the `⦃⦄` binders are filled from `i ≠ j`) |
| `Function.onFun Disjoint f i j` | `Disjoint (f i) (f j)` (it unfolds by itself) |
| `fun i => B i ∩ A` | the family `i ↦ B i ∩ A`; this is the `f` that R6 sees in the exercise |
| `(fun i => B i ∩ A) i` | that function applied to `i`, i.e. `B i ∩ A` (Lean has not substituted yet; `exact` and `simp` see through it) |
| `case hn`, `case h` | the side goals of R6 without arguments: disjointness (`hn`) and measurability (`h`) |
| `Countable ι` | needed by R6; every `Fintype` is countable, so Lean finds it for the exercise's `ι` |
| `inst✝ : …` | an unnamed instance hypothesis, such as `[Fintype ι]` |
| `Type u_1`, `Type*` | a type in some universe: read it as `Type` |

---

## Part 1 · `total_probability`

Statement: for a measurable partition `B : ι → Set Ω` of `Ω` (`hmeas`: each piece measurable, `hdisj`:
pieces pairwise disjoint, `hcover`: their union is everything) and a measurable `A`,
`μ A = ∑ i, μ[A | B i] * μ (B i)`. In maths: $P(A) = \sum_i P(A \mid B_i)\,P(B_i)$.

### Each term is the measure of an intersection

**R1 · `rw [cond_mul_eq_inter hs]`** changes the **goal**. The lemma is
`ProbabilityTheory.cond_mul_eq_inter : MeasurableSet s → ∀ t μ [IsFiniteMeasure μ], μ[t | s] * μ s = μ (s ∩ t)`,
i.e. $P(t \mid s)\,P(s) = P(s \cap t)$. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω) (hs : MeasurableSet s)`.

```lean-goal
⊢ P (μ[t | s] * μ s)
⊢ P (μ (s ∩ t))
```

**R2 · `simp_rw [cond_mul_eq_inter (hs _)]`** changes the **goal**: R1 applied inside every term of a sum.
`rw` fails here: each term mentions the bound variable `i`, and `rw` cannot rewrite under a binder.
`simp_rw` can, and `(hs _)` lets it pick `i` per term. Placeholders:
`{Ω ι : Type} [Fintype ι] (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i)) (t : Set Ω)`, plus `μ` as in R1.

```lean-goal
⊢ P (∑ i, μ[t | s i] * μ (s i))
⊢ P (∑ x, μ (s x ∩ t))
```

### The pieces `B i ∩ A` cover `A`

**R3 · `rw [← Set.iUnion_inter]`** changes the **goal**. The lemma is
`Set.iUnion_inter : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s` (intersection distributes over a union); right to left
it pulls `∩ s` out of the union. Placeholders: `{Ω ι : Type} (t : ι → Set Ω) (s : Set Ω)`.

| Before | After |
|---|---|
| `⊢ P (⋃ i, t i ∩ s)` | `⊢ P ((⋃ i, t i) ∩ s)` |

**R4 · `rw [Set.univ_inter]`** changes the **goal**. The lemma is `Set.univ_inter : Set.univ ∩ s = s`.
Placeholders: `{Ω : Type} (s : Set Ω)`. In the exercise, `rw [hcover]` first turns `⋃ i, B i` into
`Set.univ`.

| Before | After |
|---|---|
| `⊢ P (Set.univ ∩ s)` | `⊢ P s` |

**R5 · `conv_lhs => rw [ha]`** changes the **goal**, on the left side of `=` only. Plain `rw [ha]` with
`ha : A = ⋃ i, B i ∩ A` would replace every `A`, including those on the right side. Placeholders:
`{α β : Type} (a b : α) (F G : α → β) (ha : a = b)`.

| Before | After |
|---|---|
| `⊢ F a = G a` | `⊢ F b = G a` |

### Countable additivity

**R6 · `rw [measure_iUnion hd hm]`** changes the **goal**. The lemma is
`MeasureTheory.measure_iUnion : Pairwise (Function.onFun Disjoint f) → (∀ i, MeasurableSet (f i)) → μ (⋃ i, f i) = ∑' i, μ (f i)`
($\sigma$-additivity), for `[Countable ι]`. Without the two arguments, `rw [measure_iUnion]` changes the
**goal list**: the two hypotheses become new goals. Placeholders:
`{Ω ι : Type} [Countable ι] (μ : Measure Ω) (f : ι → Set Ω)`. In the exercise `f` is
`fun i => B i ∩ A`, and the two arguments are R7–R9 and R10.

| Before | After `rw [measure_iUnion]` |
|---|---|
| `⊢ P (μ (⋃ i, f i))` | `⊢ P (∑' (i : ι), μ (f i))`, `⊢ Pairwise (Function.onFun Disjoint f)`, `⊢ ∀ (i : ι), MeasurableSet (f i)` |

**R7 · `intro i j hij`** on a `Pairwise` goal changes the **context**: `Pairwise R` is a `∀ ⦃i j⦄, i ≠ j → …`,
so `intro` takes the two indices and the proof that they differ. As a term the same thing is
`fun i j hij => …`. Read the other way: from `hd : Pairwise (Function.onFun Disjoint f)` and `hij : i ≠ j`,
`hd hij : Disjoint (f i) (f j)`. Placeholders: `{Ω ι : Type} (f : ι → Set Ω)`.

| Before | After |
|---|---|
| `⊢ Pairwise (Function.onFun Disjoint f)` | `i j : ι, hij : i ≠ j ⊢ Function.onFun Disjoint f i j` |

**R8 · `refine hbd.mono ?_ ?_`** changes the **goal list**. The lemma is
`Disjoint.mono : a ≤ b → c ≤ d → Disjoint b d → Disjoint a c`: subsets of disjoint sets are disjoint
(`≤` on sets is `⊆`). Dot notation `hbd.mono` puts `hbd` in the `Disjoint b d` slot. Placeholders:
`{Ω : Type} (a b c d : Set Ω) (hbd : Disjoint b d)`. In the exercise, after R7, `refine (hdisj hij).mono ?_ ?_`
leaves `(fun i => B i ∩ A) i ⊆ B i` and the same with `j`; each is `B i ∩ A ⊆ B i`, closed by R9.

| Before | After |
|---|---|
| `⊢ Disjoint a c` | `⊢ a ⊆ b`, `⊢ c ⊆ d` |

**R9 · `exact Set.inter_subset_left`** **closes** `s ∩ t ⊆ s`. Its arguments `s t` are implicit, so Lean
reads them off the goal. Placeholders: `{Ω : Type} (s t : Set Ω)`. (`Set.inter_subset_right` closes
`s ∩ t ⊆ t`.)

| Before | After |
|---|---|
| `⊢ s ∩ t ⊆ s` | closed |

**R10 · `apply MeasurableSet.inter`** changes the **goal list**: the intersection of two measurable sets is
measurable. The lemma is `MeasurableSet.inter : MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)`;
as a term, `hs.inter ht`. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (s t : Set Ω)`.

| Before | After |
|---|---|
| `⊢ MeasurableSet (s ∩ t)` | `⊢ MeasurableSet s`, `⊢ MeasurableSet t` |

**R11 · `rw [tsum_fintype]`** changes the **goal**. The lemma is `tsum_fintype : ∑' b, f b = ∑ b, f b` for a
finite index type. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ≥0∞)`. (`#check tsum_fintype` prints a more general form with a
summation filter, `∑'[L] b, f b`; the plain `∑'` is the default filter, so ignore `L`.) After it, `rw` tries `rfl`, which
closes `∑ i, g i = ∑ x, g x` (same sum, renamed variable).

| Before | After |
|---|---|
| `⊢ P (∑' (i : ι), f i)` | `⊢ P (∑ b, f b)` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: disjointness after intersecting.** `Pairwise (Function.onFun Disjoint fun i => s ∩ t i)` from
`hd : Pairwise (Function.onFun Disjoint t)`. R7 gives

```lean-goal
⊢ Function.onFun Disjoint (fun i => s ∩ t i) i j
```

and `exact (hd hij).mono Set.inter_subset_right Set.inter_subset_right` closes it (R8 with R9's mirror).

**W2: two pieces.** For `f : Fin 2 → Set Ω` disjoint and measurable, R6 (with arguments), R11, then
`Fin.sum_univ_two : ∑ i : Fin 2, g i = g 0 + g 1`:

```lean-goal
⊢ μ (⋃ i, f i) = μ (f 0) + μ (f 1)
⊢ ∑' (i : Fin 2), μ (f i) = μ (f 0) + μ (f 1)
⊢ ∑ b, μ (f b) = μ (f 0) + μ (f 1)
```

---

## Part 2 · `bayes`

Statement: with the same partition, for any `j : ι`,
`μ[B j | A] = μ[A | B j] * μ (B j) / ∑ i, μ[A | B i] * μ (B i)`. In maths:
$P(B_j \mid A) = P(A \mid B_j)\,P(B_j) / \sum_i P(A \mid B_i)\,P(B_i)$. The denominator is the right side of
Part 1, so Part 1 is the milestone: `rw [← total_probability …]` turns it back into `μ A`.

**R12 · `rw [cond_eq_inv_mul_cond_mul hs ht]`** changes the **goal**. The lemma is
`ProbabilityTheory.cond_eq_inv_mul_cond_mul : MeasurableSet s → MeasurableSet t → ∀ μ [IsFiniteMeasure μ], μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t`,
i.e. $P(t \mid s) = P(s)^{-1} P(s \mid t) P(t)$. The first argument is about the set **after** the bar.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s t : Set Ω)`.

```lean-goal
⊢ P μ[t | s]
⊢ P ((μ s)⁻¹ * μ[s | t] * μ t)
```

**R13 · `rw [div_eq_mul_inv]`** changes the **goal**. The lemma is `div_eq_mul_inv : a / b = a * b⁻¹`.
Placeholders: `(a b : ℝ≥0∞)` (it holds in any `DivInvMonoid`, which `ℝ≥0∞` is).

| Before | After |
|---|---|
| `⊢ P (a / b)` | `⊢ P (a * b⁻¹)` |

**R14 · `ring`** **closes** an identity of commutative semirings. `ℝ≥0∞` is one. `ring` treats `x⁻¹` as an
unknown, so it can reorder `a⁻¹ * b * c`, but it cannot cancel `a * a⁻¹` (false in `ℝ≥0∞` when `a = 0` or
`a = ∞`). Placeholders: `(a b c : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ a⁻¹ * b * c = c * b * a⁻¹` | closed |

**W3: division and reordering.** R13 then R14:

```lean-goal
⊢ a * b / c = c⁻¹ * b * a
⊢ a * b * c⁻¹ = c⁻¹ * b * a
```

---

## Traps

- `rw [cond_mul_eq_inter (hmeas _)]` fails on `∑ i, μ[A | B i] * μ (B i)`: the pattern mentions the bound
  `i`. Use `simp_rw` (R2).
- `rw [hA']` with `hA' : A = ⋃ i, B i ∩ A` rewrites every `A`, on the right side and inside the union too.
  Rewrite the left side only (R5).
- The conditioning set comes second in the notation: `μ[t | s]` is "`t` given `s`", and the lemmas take the
  proof `MeasurableSet s` first. For `μ[B j | A]`, R12 needs `hA` first, then `hmeas j`.
- Values are in `ℝ≥0∞`, not `ℝ`: `a / b` is `a * b⁻¹` (R13), there is no `a * a⁻¹ = 1` without `a ≠ 0` and
  `a ≠ ∞`, and `ring` treats `⁻¹` as an unknown (R14). Avoid needing cancellation: reorder instead.
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES, "Structure"). R6 without arguments leaves three
  goals; giving the arguments is simpler.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `μ[t \| s] * μ s → μ (s ∩ t)` | `rw [cond_mul_eq_inter hs]` | R1 |
| the same under `∑ i` | `simp_rw [cond_mul_eq_inter (hs _)]` | R2 |
| `⋃ i, t i ∩ s → (⋃ i, t i) ∩ s` | `rw [← Set.iUnion_inter]` | R3 |
| `Set.univ ∩ s → s` | `rw [Set.univ_inter]` | R4 |
| rewrite the left side only | `conv_lhs => rw [h]` | R5 |
| `μ (⋃ i, f i) → ∑' i, μ (f i)` | `rw [measure_iUnion hd hm]` | R6 |
| prove `Pairwise …` | `fun i j hij => …` / `intro i j hij` | R7 |
| use `hd : Pairwise (onFun Disjoint f)` | `hd hij : Disjoint (f i) (f j)` | R7 |
| shrink a disjoint pair | `h.mono hab hcd` | R8 |
| `s ∩ t ⊆ s` / `s ∩ t ⊆ t` | `Set.inter_subset_left` / `Set.inter_subset_right` | R9 |
| `MeasurableSet (s ∩ t)` | `hs.inter ht` | R10 |
| `∑' → ∑` over a finite type | `rw [tsum_fintype]` | R11 |
| `μ[t \| s] → (μ s)⁻¹ * μ[s \| t] * μ t` | `rw [cond_eq_inv_mul_cond_mul hs ht]` | R12 |
| `a / b → a * b⁻¹` | `rw [div_eq_mul_inv]` | R13 |
| reorder a product in `ℝ≥0∞` | `ring` | R14 |
| use Part 1 backwards | `rw [← total_probability μ B hmeas hdisj hcover A hA]` | milestone |
| see the state | infoview | |
