# H051 · Borel–Cantelli lemma: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `apply`, `have`, `obtain`
patterns, `refine` with `?_`, `rw`, `simp`, `ext`, `calc`, `∀`/`∃`/`∧`/`¬`, anonymous constructors `⟨a, b⟩`.
**New here:** Mathlib's measure theory (`Measure`, `μ S`, `∀ᵐ`), the extended non-negative reals `ℝ≥0∞`,
infinite sums `∑'`, filters (`atTop`, `∀ᶠ`, `∃ᶠ`, `Tendsto`, `𝓝`), `limsup` of a sequence of sets, finite and
infinite sets, finsets and subtypes.

**The maths.** Let `(Ω, μ)` be a measure space and `s : ℕ → Set Ω` a sequence of events with
`∑ₙ μ(sₙ) < ∞`.

1. *limsup of sets.* `limsup s atTop = ⋂ₙ ⋃_{k ≥ n} s k = ⋂ₙ ⋃ₖ s (k + n)`: the `ω` lying in infinitely many
   `s k`. In particular, for every `n`, `limsup s ⊆ ⋃ₖ s (k + n)`.
2. *Subadditivity.* So `μ(limsup s) ≤ μ(⋃ₖ s (k + n)) ≤ ∑ₖ μ(s (k + n))`, the `n`-th tail of the series.
3. *Squeeze.* The tails of a convergent series tend to `0`; a constant `≤` every term of a sequence
   tending to `0` is `≤ 0`, hence `= 0` (measures are `≥ 0`). This is `borel_cantelli`.
4. *Almost surely.* `∀ᵐ ω, P ω` means `μ {ω | ¬P ω} = 0`. With `P ω = "ω ∉ s n for all large n"`, the
   bad set `{ω | ¬ ∀ᶠ n, ω ∉ s n}` is exactly `limsup s atTop`. This is `ae_finitely_many`.
5. *Countable index.* For `s : ι → Set Ω` with `ι` countable there is no "large `i`". Replace the tail
   `{k ≥ n}` by the complement `{i // i ∉ F}` of a finite set `F`. If `ω` is in infinitely many `s i`, then
   `{i | ω ∈ s i} \ F` is still infinite, hence nonempty, so `ω ∈ ⋃_{i ∉ F} s i`. Subadditivity bounds the
   bad set by `∑_{i ∉ F} μ(s i)`, and these "tails over finsets" tend to `0` as `F` grows. This is `ae_finite`.

The guide never uses the exercise's `s`, its limsup or its bad sets; it uses placeholders and toy objects
(a null union, `(↑n)⁻¹`, `f ω = 0` a.e.).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`apply`/`have`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement and its placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. `{Ω : Type}` is any type. A bracket such as `[MeasurableSpace Ω]`
  is a requirement on the type (a *type class*): here, that `Ω` carries a σ-algebra (its measurable sets).
  `[Countable ι]` says `ι` is countable; `ℕ`, `ℤ`, `ℚ`, finite types and subtypes of countable types qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A state containing `|` (set-builder `{ω | …}`) cannot sit in a Markdown table (`|` splits cells). Such
  states are given as a `lean-goal` block instead: the first line is the goal before the step, the next line
  the goal after.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type u_1` | the sample space; `Type*` in a statement makes a universe variable `u_1` (ignore it) |
| `Set Ω`, `ω ∈ S` | a set of points of `Ω` (an event); `Set Ω` is `Ω → Prop`, and `ω ∈ S` is "`S` holds at `ω`" |
| `{ω \| p ω}` | set-builder: the set of `ω` with `p ω`. `x ∈ {ω \| p ω}` is `p x` by definition (`exact` accepts either) |
| `⋃ i, B i`, `⋂ i, B i` | union / intersection of a family `B : ι → Set Ω`: `ω ∈ ⋃ i, B i ↔ ∃ i, ω ∈ B i`, `ω ∈ ⋂ i, B i ↔ ∀ i, ω ∈ B i` |
| `μ : Measure Ω` | a measure on `Ω` (`MeasureTheory.Measure`); not necessarily a probability measure |
| `μ S` | the measure of `S : Set Ω`, a value in `ℝ≥0∞`. Defined for every set (outer measure), measurable or not |
| `ℝ≥0∞`, `ENNReal` | `[0, ∞]`: non-negative reals plus `∞`. `0` is its least element `⊥`; `0⁻¹ = ∞` |
| `∞` | the top element of `ℝ≥0∞` (`open scoped ENNReal` makes the notation available) |
| `∑' (i : ι), f i` | `tsum`, the infinite sum. In `ℝ≥0∞` every series has a sum (possibly `∞`), so `≠ ∞` means "converges" |
| `limsup s atTop` | for sets: `⋂ n, ⋃ k ≥ n, s k`, the points in infinitely many `s k` |
| `⨅ n, f n`, `⨆ i, f i` | infimum / supremum of a family; for sets they are `⋂` / `⋃` (Lean prints `⨅`/`⨆` after R1, R7) |
| `⨆ i, ⨆ (_ : i ≥ n), f i` | `⨆ i ≥ n, f i`: supremum over the `i` with `i ≥ n` |
| `⋃ i, s ↑i` | union over the subtype `{x // x ∉ F}`; `↑i : ι` is the underlying index |
| `atTop` | the filter "eventually large": on `ℕ`, sets containing some `{n, n+1, …}`; on `Finset ι`, "`F` contains any given finset" |
| `∀ᶠ n in atTop, p n` | `p n` holds for all large `n` (`∃ N, ∀ n ≥ N, p n` on `ℕ`) |
| `∃ᶠ n in atTop, p n` | `p n` holds for infinitely many `n` (`∀ N, ∃ n ≥ N, p n` on `ℕ`) |
| `∀ᵐ (ω : Ω) ∂μ, p ω` | `p` holds `μ`-almost everywhere: `μ {ω \| ¬p ω} = 0` |
| `Tendsto f atTop (𝓝 a)` | `f n → a` as `n → ∞`; `𝓝 a` is the neighbourhood filter of `a` |
| `{ x // x ∉ F }` | the subtype of `ι`: pairs `⟨x, hx⟩` with `hx : x ∉ F` |
| `F : Finset ι`, `↑F` | a finite set (a finset); `↑F : Set ι` is the same set as a `Set` |
| `S.Finite`, `S.Infinite` | `S` has finitely many elements; `S.Infinite` is by definition `¬S.Finite` |
| `S.Nonempty` | `∃ x, x ∈ S` |
| `S \ T` | set difference: `x ∈ S \ T` is by definition `x ∈ S ∧ x ∉ T` |
| `x ∉ S` | `¬(x ∈ S)` |
| `S ⊆ T` | by definition `∀ ⦃x⦄, x ∈ S → x ∈ T`; `intro` opens it |
| `inst✝ : Countable ι` | an anonymous type-class hypothesis |
| `case a` | the two goals produced by `apply le_antisymm` |

---

## Part 1 · `limsup_subset` (milestone)

Statement: `limsup s atTop ⊆ ⋃ k, s (k + n)` for every `n`. Rewrite the limsup into `⨅`/`⨆` (R1); the goal
is then "an intersection is contained in its `n`-th member" (R2).

**R1 · `rw [limsup_eq_iInf_iSup_of_nat']`** changes the **goal**. The lemma is
`limsup u atTop = ⨅ n, ⨆ i, u (i + n)` for `u : ℕ → α` in a complete lattice (sets are one; `≤` is `⊆`,
`⨅` is `⋂`, `⨆` is `⋃`). Placeholders: `{Ω : Type} (A : ℕ → Set Ω)`, `P : Set Ω → Prop`.

| Before | After |
|---|---|
| `⊢ P (limsup A atTop)` | `⊢ P (⨅ n, ⨆ i, A (i + n))` |

**R2 · `exact iInf_le _ i`** **closes** the goal. The lemma is `iInf_le f i : ⨅ j, f j ≤ f i`. On sets `≤` is
`⊆` by definition, and `⨆ i, A (i + n)` is literally `⋃ i, A (i + n)`, so it closes `⊆` goals between them.
Placeholders: `{Ω : Type} (B : ℕ → Set Ω) (i : ℕ)`.

| Before | After |
|---|---|
| `⊢ ⨅ j, B j ⊆ B i` | closed |

---

## Part 2 · `measure_limsup_le` (milestone)

Statement: `μ (limsup s atTop) ≤ ∑' k, μ (s (k + n))`. A two-step `calc`: monotonicity with Part 1 (R4),
then countable subadditivity (R5).

**R3 · `calc`** changes the **goal list**: a goal `a ≤ c` is proved as a chain `a ≤ b`, `b ≤ c`, each step
followed by `:= proof`. `_` stands for the previous right-hand side. Placeholders:
`{α : Type} [Preorder α] (a b c : α)` (`α` has a `≤` that is reflexive and transitive; `ℝ≥0∞` qualifies).
Layout: `calc a ≤ b := h₁` then on the next line, indented, `_ ≤ c := h₂`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | closed, given `h₁ : a ≤ b` and `h₂ : b ≤ c` |

**R4 · `measure_mono`** **closes** `μ S ≤ μ T`. The lemma is `measure_mono : S ⊆ T → μ S ≤ μ T`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S T : Set Ω)`.

| Before | After |
|---|---|
| `hST : S ⊆ T ⊢ μ S ≤ μ T` | closed by `exact measure_mono hST` |

**R5 · `measure_iUnion_le`** **closes** a subadditivity goal. The lemma is
`measure_iUnion_le (B : ι → Set Ω) : μ (⋃ i, B i) ≤ ∑' i, μ (B i)`, for `[Countable ι]`, with no
measurability assumption. Placeholders: `{Ω ι : Type} [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω)
(B : ι → Set Ω)`. In the exercise `B` is `fun k => s (k + n)` (write `measure_iUnion_le _`) or `ι` is the
subtype `{x // x ∉ F}` (countable because `ι` is).

| Before | After |
|---|---|
| `⊢ μ (⋃ i, B i) ≤ ∑' (i : ι), μ (B i)` | closed |

---

## Part 3 · `setOf_not_eventually` (milestone)

Statement: `{ω | ¬ ∀ᶠ n in atTop, ω ∉ s n} = limsup s atTop`. Equality of sets: `ext ω` (R6), then one
`simp` call with the unshifted limsup formula (R7) turns both sides into `∀ n, ∃ k, n ≤ k ∧ ω ∈ s k` (R8 on
the right, R9 on the left) and closes the goal.

**R6 · `ext ω`** changes the **goal and the context**. It uses `Set.ext`: two sets are equal when they have
the same members. Placeholders: `{Ω : Type} (S T : Set Ω)`.

| Before | After |
|---|---|
| `⊢ S = T` | `ω : Ω ⊢ ω ∈ S ↔ ω ∈ T` |

**R7 · `limsup_eq_iInf_iSup_of_nat`** changes the **goal**. The lemma is
`limsup u atTop = ⨅ n, ⨆ i ≥ n, u i` (no shift; the bound `i ≥ n` is an inner `⨆` over proofs).
Placeholders: `{Ω : Type} (A : ℕ → Set Ω)`, `P : Set Ω → Prop`. Pass it to `simp`, not `rw`, in the
exercise: `simp [limsup_eq_iInf_iSup_of_nat]`.

| Before | After |
|---|---|
| `⊢ P (limsup A atTop)` | `⊢ P (⨅ n, ⨆ i, ⨆ (_ : i ≥ n), A i)` |

**R8 · `simp` on membership** changes the **goal**. `simp` applies `Set.mem_iInter`
(`ω ∈ ⋂ n, S n ↔ ∀ n, ω ∈ S n`), `Set.mem_iUnion` (R16) and `exists_prop` by itself. Placeholders:
`{Ω : Type} (A : ℕ → Set Ω) (ω : Ω)`. (`simp` renames the inner bound variable `i_1`.)

| Before | After |
|---|---|
| `⊢ ω ∈ ⨅ n, ⨆ i, ⨆ (_ : i ≥ n), A i` | `⊢ ∀ (i : ℕ), ∃ i_1, i ≤ i_1 ∧ ω ∈ A i_1` |

**R9 · `Filter.not_eventually`, `not_not`, `Filter.frequently_atTop`** change the **goal**; all three are
`simp` lemmas. `not_eventually : (¬∀ᶠ x in f, p x) ↔ ∃ᶠ x in f, ¬p x`; `frequently_atTop :
(∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b`. Placeholders: `(p : ℕ → Prop)`, `P : Prop → Prop`. In the
exercise `p n` is `ω ∈ s n` and `¬p n` is `ω ∉ s n`.

| Before | After `rw [Filter.not_eventually]` | After `simp only [not_not]` | After `rw [Filter.frequently_atTop]` |
|---|---|---|---|
| `⊢ P ¬∀ᶠ (n : ℕ) in atTop, ¬p n` | `⊢ P (∃ᶠ (x : ℕ) in atTop, ¬¬p x)` | `⊢ P (∃ᶠ (x : ℕ) in atTop, p x)` | `⊢ P (∀ (a : ℕ), ∃ b, a ≤ b ∧ p b)` |

---

## Part 4 · `setOf_infinite_subset` (milestone)

Statement: `{ω | ¬ {i | ω ∈ s i}.Finite} ⊆ ⋃ i : {x // x ∉ F}, s i` for a finset `F : Finset ι`. Open the
`⊆` (R10). From `hω` (infinitely many `i` with `ω ∈ s i`) and `↑F` finite (R11), the difference is infinite
(R12), hence nonempty (R13); take the element apart (R14), pack it into the subtype (R15), and prove
membership in the union (R16).

**R10 · `intro ω hω`** changes the **goal and the context**: `S ⊆ T` is by definition
`∀ ⦃x⦄, x ∈ S → x ∈ T`, so `intro` opens it. In the exercise `hω : ω ∈ {ω | ¬{i | ω ∈ s i}.Finite}`, which
is by definition `{i | ω ∈ s i}.Infinite`. Placeholders: `{Ω : Type} (S T : Set Ω)`.

| Before | After |
|---|---|
| `⊢ S ⊆ T` | `ω : Ω, hω : ω ∈ S ⊢ ω ∈ T` |

**R11 · `F.finite_toSet`** (`Finset.finite_toSet`) changes the **context** (with `have`): a finset seen as a
set is finite, `(↑F : Set ι).Finite`. Placeholders: `{ι : Type} (F : Finset ι)`.

| Before | After `have h := F.finite_toSet` |
|---|---|
| `⊢ G` | `h : (↑F).Finite ⊢ G` |

**R12 · `Set.Infinite.sdiff`** changes the **context**. The lemma is
`S.Infinite → T.Finite → (S \ T).Infinite`. Placeholders: `{ι : Type} (S T : Set ι)`.

| Before | After `have h := hS.sdiff hT` |
|---|---|
| `hS : S.Infinite, hT : T.Finite ⊢ G` | `h : (S \ T).Infinite ⊢ G` |

**R13 · `Set.Infinite.nonempty`** changes the **context**. The lemma is `S.Infinite → S.Nonempty`.
Placeholders: `{ι : Type} (S : Set ι)`.

| Before | After `have h := hS.nonempty` |
|---|---|
| `hS : S.Infinite ⊢ G` | `h : S.Nonempty ⊢ G` |

**R14 · `obtain ⟨i, hi, hiT⟩ := hne`** changes the **context**. `(S \ T).Nonempty` unfolds to
`∃ i, i ∈ S ∧ i ∉ T`, so one pattern gives the element and both facts. Placeholders: `{ι : Type} (S T : Set ι)`.

| Before | After |
|---|---|
| `hne : (S \ T).Nonempty ⊢ G` | `i : ι, hi : i ∈ S, hiT : i ∉ T ⊢ G` |

In the exercise `T` is `↑F`, so `hiT : i ∉ ↑F`, which is by definition `i ∉ F` (what R15 needs).

**R15 · subtype `{x // x ∉ F}`** (no change; a term). An element is `⟨x, hx⟩` with `hx : x ∉ F`; the
coercion `↑` (also `.1`) gives back `x`, and `↑⟨x, hx⟩` reduces to `x` by definition. Placeholders:
`{ι : Type} (F : Finset ι) (x : ι) (hx : x ∉ F)`.

| Before | After |
|---|---|
| `⊢ P ↑⟨x, hx⟩` | closed by `exact h` with `h : P x` |

**R16 · `Set.mem_iUnion`** changes the **goal**. The lemma is `ω ∈ ⋃ i, B i ↔ ∃ i, ω ∈ B i`; in term form,
`Set.mem_iUnion.mpr ⟨i, h⟩ : ω ∈ ⋃ i, B i`. Placeholders: `{Ω ι : Type} (B : ι → Set Ω) (ω : Ω) (i : ι)`.
In the exercise the index is the subtype element `⟨i, hiF⟩` (R15).

| Before | After `rw [Set.mem_iUnion]` |
|---|---|
| `⊢ ω ∈ ⋃ j, B j` | `⊢ ∃ i, ω ∈ B i` |

---

## Part 5 · `borel_cantelli`

Statement: `∑' i, μ (s i) ≠ ∞ → μ (limsup s atTop) = 0`. A one-term proof:
`le_antisymm (ge_of_tendsto' tails bound) bot_le`, where `tails` is R20 and `bound` is the milestone
`measure_limsup_le μ s : ∀ n, μ (limsup s atTop) ≤ ∑' k, μ (s (k + n))`.

**R17 · `le_antisymm`** changes the **goal list**: `a = b` becomes `a ≤ b` and `b ≤ a`. The lemma is
`le_antisymm : a ≤ b → b ≤ a → a = b`. Placeholders: `{α : Type} [PartialOrder α] (a b : α)` (`ℝ≥0∞`
qualifies).

| Before | After `apply le_antisymm` |
|---|---|
| `⊢ a = b` | `⊢ a ≤ b`, `⊢ b ≤ a` |

**R18 · `bot_le`** **closes** `0 ≤ a` in `ℝ≥0∞`. The lemma is `bot_le : ⊥ ≤ a`, and `⊥` (the least element)
of `ℝ≥0∞` is `0` by definition. Placeholders: `(a : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a` | closed |

**R19 · `ge_of_tendsto'`** changes the **goal**. The lemma is
`Tendsto f l (𝓝 a) → (∀ c, b ≤ f c) → b ≤ a`: a constant below every term is below the limit. `l` must be
a proper filter (`[l.NeBot]`); `atTop` on `ℕ` and on `Finset ι` are. Placeholders:
`(f : ℕ → ℝ≥0∞) (a b : ℝ≥0∞)`.

| Before | After `apply ge_of_tendsto' hf` |
|---|---|
| `⊢ b ≤ a` | `⊢ ∀ (c : ℕ), b ≤ f c` |

**R20 · `ENNReal.tendsto_sum_nat_add`** **closes** a tail limit. The lemma is
`ENNReal.tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0)`. In the exercise `f` is `fun i => μ (s i)`; write `_`.
Placeholders: `(f : ℕ → ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun i => ∑' (k : ℕ), f (k + i)) atTop (𝓝 0)` | closed by `exact ENNReal.tendsto_sum_nat_add f hf` |

---

## Part 6 · `ae_finitely_many`

Statement: `∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n`. Rewrite `∀ᵐ` into a null set (R21); the set is then the
left side of the milestone `setOf_not_eventually` (up to the bound variable's name), so `rw` with it, and
the goal is `borel_cantelli`.

**R21 · `rw [ae_iff]`** changes the **goal**. The lemma is `ae_iff : (∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Prop)`.

```lean-goal
⊢ ∀ᵐ (ω : Ω) ∂μ, p ω
⊢ μ {a | ¬p a} = 0
```

---

## Part 7 · `ae_finite`

Statement: `[Countable ι] → ∑' i, μ (s i) ≠ ∞ → ∀ᵐ ω ∂μ, {i | ω ∈ s i}.Finite`. After R21 the goal is
`μ {a | ¬{i | a ∈ s i}.Finite} = 0`. Same squeeze as Part 5, but along the filter `atTop` on `Finset ι`:
the tails are `∑' b : {x // x ∉ F}, μ (s ↑b)` (R22), and for each `F` the bound is the milestone
`setOf_infinite_subset s F` (R4) followed by R5, chained with R23. The hole for the bound is opened with
R24.

**R22 · `ENNReal.tendsto_tsum_compl_atTop_zero`** **closes** a "tail over finsets" limit. The lemma is
`∑' x, f x ≠ ∞ → Tendsto (fun F : Finset ι => ∑' b : {x // x ∉ F}, f ↑b) atTop (𝓝 0)`: the sum over the
indices outside `F` tends to `0` as `F` grows. Placeholders: `{ι : Type} (f : ι → ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun F => ∑' (b : { x // x ∉ F }), f ↑b) atTop (𝓝 0)` | closed by `exact ENNReal.tendsto_tsum_compl_atTop_zero hf` |

**R23 · `h₁.trans h₂`** (`LE.le.trans`) **closes** `a ≤ c` from `h₁ : a ≤ b` and `h₂ : b ≤ c`: the one-term
form of a two-step `calc` (R3). Placeholders: `{α : Type} [Preorder α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | closed by `exact h₁.trans h₂` |

**R24 · `refine … fun F => ?_`** changes the **goal list**: a `?_` under a `fun F =>` becomes a goal with
`F` in the context. In the exercise it is the second argument of `ge_of_tendsto'` (R19), and the new goal
is `μ {a | ¬{i | a ∈ s i}.Finite} ≤ ∑' (b : { x // x ∉ F }), μ (s ↑b)`.
Placeholders: `{ι : Type} (Q : Finset ι → Prop)`.

| Before | After `refine k fun F => ?_` |
|---|---|
| `⊢ G` | `F : Finset ι ⊢ Q F` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a countable union of null sets is null.** `apply le_antisymm` (R17); the first goal is
`(measure_iUnion_le B).trans (by simp [hB])` (R5, R23: `simp [hB]` rewrites each `μ (B i)` to `0` and `∑' i, 0` to `0`); the
second is `bot_le` (R18).

| Before | After `apply le_antisymm` |
|---|---|
| `⊢ μ (⋃ i, B i) = 0` | `⊢ μ (⋃ i, B i) ≤ 0`, `⊢ 0 ≤ μ (⋃ i, B i)` |

**W2: a squeeze in `ℝ≥0∞`.** If `b ≤ (↑n)⁻¹` for every `n`, then `b = 0`: R17, then
`ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero hb` (R19 with the limit `(↑n)⁻¹ → 0`), then R18. In
`ℝ≥0∞`, `(↑0)⁻¹ = ∞`, so `n = 0` costs nothing. This is the shape of `borel_cantelli`.

| Before | After `apply le_antisymm` |
|---|---|
| `⊢ b = 0` | `⊢ b ≤ 0`, `⊢ 0 ≤ b` |

**W3: `∀ᵐ` from a null set.** R21, then `exact h`: `{a | ¬f a = 0}` and `{ω | f ω ≠ 0}` differ only in the
bound variable's name and the spelling of `≠`, which are the same by definition.

```lean-goal
⊢ ∀ᵐ (ω : Ω) ∂μ, f ω = 0
⊢ μ {a | ¬f a = 0} = 0
```

---

## Traps

- `hω.sdiff` fails: `hω : ω ∈ {ω | ¬ …}` unfolds to a function type (`… → False`), and dot notation looks
  for `Function.sdiff`. Write the lemma name: `Set.Infinite.sdiff hω F.finite_toSet`.
- `rw [limsup_eq_iInf_iSup_of_nat']` (with `'`) is the shifted form `u (i + n)` that matches
  `⋃ k, s (k + n)`; the unshifted `limsup_eq_iInf_iSup_of_nat` gives `⨆ i ≥ n` and is the one `simp` needs in
  Part 3. Mixing them up leaves goals that differ by `k + n` versus `k ≥ n`.
- Only `≠ ∞` makes a series in `ℝ≥0∞` "convergent": `∑'` there always exists, and R20/R22 need the
  hypothesis `hs`.
- After `rw [ae_iff]` the bound variable is renamed `a`; `rw [setOf_not_eventually]` still matches (names of
  bound variables do not matter), but it must match the statement exactly otherwise: `¬∀ᶠ …, a ∉ s n`.
- `measure_iUnion_le` needs `[Countable ι]` on the index. For `⋃ i : {x // x ∉ F}, …` Lean finds it from
  `[Countable ι]` automatically.
- `ge_of_tendsto'` (with `'`) takes `∀ c, b ≤ f c`; plain `ge_of_tendsto` wants `∀ᶠ c in l, b ≤ f c`.
- The Mathlib versions of these theorems are BANNED (`measure_limsup_atTop_eq_zero`, `ae_eventually_notMem`,
  …), and so are `exact?`, `apply?`, `rw?`, `hint`, `observe`, `try?`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| limsup of sets as `⋂ₙ ⋃ₖ s (k + n)` | `rw [limsup_eq_iInf_iSup_of_nat']` | R1 |
| limsup of sets as `⋂ₙ ⋃_{k ≥ n} s k` | `simp [limsup_eq_iInf_iSup_of_nat]` | R7, R8 |
| intersection ⊆ one member | `exact iInf_le _ n` | R2 |
| chain two inequalities | `calc a ≤ b := h₁` / `_ ≤ c := h₂`, or `h₁.trans h₂` | R3, R23 |
| `S ⊆ T → μ S ≤ μ T` | `measure_mono h` | R4 |
| `μ (⋃ i, B i) ≤ ∑' i, μ (B i)` | `measure_iUnion_le _` | R5 |
| equality of sets | `ext ω` | R6 |
| `¬∀ᶠ n, ¬p n` → `∀ a, ∃ b ≥ a, p b` | `simp` (`not_eventually`, `frequently_atTop`) | R9 |
| open `S ⊆ T` | `intro ω hω` | R10 |
| finset is finite | `F.finite_toSet` | R11 |
| infinite minus finite | `Set.Infinite.sdiff hS hT` | R12 |
| infinite → an element | `obtain ⟨i, hi, hiT⟩ := (…).nonempty` | R13, R14 |
| subtype element | `⟨i, hiF⟩ : {x // x ∉ F}` | R15 |
| member of `⋃ i, B i` | `Set.mem_iUnion.mpr ⟨i, h⟩` | R16 |
| `a = 0` in `ℝ≥0∞` from `a ≤ 0` | `le_antisymm h bot_le` | R17, R18 |
| `b ≤ lim f` from `∀ c, b ≤ f c` | `ge_of_tendsto' hf (fun c => …)` | R19 |
| tails `∑' k, f (k + i) → 0` | `ENNReal.tendsto_sum_nat_add _ hs` | R20 |
| `∀ᵐ` → null set | `rw [ae_iff]` | R21 |
| tails over finsets → 0 | `ENNReal.tendsto_tsum_compl_atTop_zero hs` | R22 |
| leave a hole under `fun F =>` | `refine … fun F => ?_` | R24 |
| see the state | infoview | |
