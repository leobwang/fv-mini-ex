# H046 · Heine–Borel for [0, 1]: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `have`, `obtain`/`rcases`
patterns, `refine`, `constructor`, anonymous constructors `⟨_, _⟩`, `∃`/`∧`/`∨`/`¬`, `<;>`, `·`.
H044 and H045 use the same `sSup` lemmas (R27, R28, R30); if you did them, Part 3 will look familiar.
**New here:** Mathlib's sets (`{x | p x}`, `Set.Icc`, `⊆`, indexed unions `⋃`), finite sets `Finset`
(`{i}`, `insert`), metric balls and `dist`, absolute value `|·|`, `IsOpen`, least upper bounds
`sSup`/`BddAbove`/`Set.Nonempty`, `min`, and the tactics `classical`, `by_cases`, `push Not`, `set`,
`linarith`.

**The maths.** `ι` is any index type and `U : ι → Set ℝ` a family of open subsets of `ℝ` whose union
contains `[0, 1]` (`hcov`). Goal: finitely many indices, a `t : Finset ι`, already cover `[0, 1]`.
Compactness in any form is banned, so you prove it by "creeping along the interval":

1. Let `S = {x ∈ [0, 1] | [0, x] is covered by finitely many U i}`. *`0 ∈ S`* (`zero_mem_S`): `0` lies in
   some `U i` (by `hcov`), and `[0, 0] = {0}` is covered by the one-element finset `{i}`.
2. `S` is nonempty and bounded above by `1`, so `s = sSup S` (its least upper bound) exists, with
   `0 ≤ s ≤ 1`. Hence `s ∈ [0, 1]` lies in some `U j`, and `U j` open gives `ε > 0` with
   `ball s ε = (s - ε, s + ε) ⊆ U j`.
3. `s - ε < s = sup S`, so some `x ∈ S` has `s - ε < x`: `[0, x]` is covered by a finset `t`.
4. *Extend* (`extend_cover`): `[0, min (s + ε/2) 1]` is covered by `insert j t` (`t` plus the index `j`). A
   point `z ≤ x` is covered by `t`; a point `x < z ≤ s + ε/2` has `|z - s| < ε`, so `z ∈ ball s ε ⊆ U j`.
5. So `y = min (s + ε/2) 1 ∈ S`, hence `y ≤ s`. But `y = s + ε/2 > s` is impossible, so `y = 1`, and the
   finset from `y ∈ S` covers `[0, 1]`.

The guide never uses the exercise's `U`, `S` or `s`; it uses placeholders and toy goals.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`/`refine`/`obtain`/`exact`. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement and its placeholders with their types,
then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`), or the whole goal (`P : Prop`). A hypothesis `k` or `h`
  in an entry is only there to finish the example.
- `{α : Type}` is any type. A bracket such as `[DecidableEq ι]` or `[Preorder α]` is a requirement on the
  type (a *type class*). `ℝ` is a linear order, an ordered field, a metric space and a conditionally complete
  lattice, so it meets every bracket the lemmas here ask for.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A state
  containing `|` (set-builder braces, absolute values) cannot sit in a table's code span, so it is printed
  plainly in the table and repeated, checked, in a `lean-goal` block (before, then after) below it.

## Reading the goals

| You see | It means |
|---|---|
| `Set ℝ` | sets of reals, i.e. predicates `ℝ → Prop`; `x ∈ A` is `A x` |
| `{x \| p x}` | the set of `x` with `p x` (`setOf p`); `a ∈ {x \| p x}` is by definition `p a` (R2) |
| `Icc a b` | `Set.Icc a b = {x \| a ≤ x ∧ x ≤ b}`, the closed interval `[a, b]` (`open Set`); R3 |
| `A ⊆ B` | `∀ ⦃z⦄, z ∈ A → z ∈ B`: apply it to a membership (R7), prove it with `intro` (R9) |
| `⋃ i, U i` | `Set.iUnion U`, the union of the family; membership: R8 |
| `⋃ i ∈ t, U i` | `⋃ i, ⋃ (_ : i ∈ t), U i`: the union over the indices in `t`; membership: R11 |
| `⋃ i_1 ∈ {i}, U i_1` | the same union; Lean renames the bound `i` to `i_1` because a variable `i` is already in the context |
| `∃ t, Icc 0 x ⊆ …` | `∃ t : Finset ι, …`: the infoview omits the binder's type |
| `∃ i, ∃ (_ : i ∈ t), x ∈ U i` | "some `i ∈ t` has `x ∈ U i`" (the second `∃` is over proofs of `i ∈ t`) |
| `Finset ι` | a finite set of elements of `ι` (a list up to order and duplicates) |
| `{i}`, `{i, j}` | finsets: one element; `insert i {j}` |
| `insert j t` | the finset `t` with `j` added; needs `DecidableEq ι` (R1) |
| `inst✝ : DecidableEq ι` | an anonymous type-class hypothesis: equality on `ι` is decidable |
| `ι : Type u_1` | `ι` is a type in some universe; `Type*` in the source. Treat it as `Type` |
| `Metric.ball c ε` | `{y \| dist y c < ε}`, the open ball; in `ℝ` the interval `(c - ε, c + ε)` |
| `dist y x` | the distance; in `ℝ`, `dist y x = \|y - x\|` (R19) |
| `\|a\|` | absolute value of `a` |
| `IsOpen V` | `V` is open; for metric spaces unfold it with R29 |
| `∃ ε > 0, p ε` | `∃ ε, ε > 0 ∧ p ε`: the pattern `⟨ε, hε, hp⟩` takes it apart |
| `∀ x ∈ S, p x` | `∀ x, x ∈ S → p x` |
| `sSup S` | least upper bound of `S : Set ℝ`; meaningful only when `S` is nonempty and bounded above (the `cs…` lemmas ask for that) |
| `BddAbove S` | `∃ b, b ∈ upperBounds S`: some `b` bounds `S` (R26) |
| `S.Nonempty` | `Set.Nonempty S`, i.e. `∃ x, x ∈ S`; write it as `⟨x, hx⟩` |
| `min a b` | the smaller of `a` and `b` |
| `S : Set ℝ := e` | a local definition made by `set` (R25): `S` stands for `e` |
| `case pos`, `case neg` | the two goals of `by_cases` (R14); `case inl`, `case inr`: the two of `rcases … with h \| h` |

---

## Part 1 · `zero_mem_S` (milestone)

Statement: `0 ∈ {x | x ∈ Icc 0 1 ∧ ∃ t : Finset ι, Icc 0 x ⊆ ⋃ i ∈ t, U i}`: `0 ∈ [0, 1]`, and some finset
of indices covers `[0, 0]`.

**R1 · `classical`** changes the **context** invisibly: from here on every proposition is decidable, in
particular `i = j` for `i j : ι`, so `insert j t` elaborates. The goal does not change. Only `heine_borel`
really needs it (to call `extend_cover`, which asks for `[DecidableEq ι]`); it does no harm elsewhere.
Placeholders: `{ι : Type} (j : ι) (t : Finset ι) (P : Finset ι → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ u, P u` | `⊢ ∃ u, P u` (and now `⟨insert j t, k _⟩` is accepted) |

**R2 · `rw [Set.mem_setOf_eq]`** changes the **goal**. Statement: `(a ∈ {x | p x}) = p a`. Placeholders:
`{α : Type} (p : α → Prop) (a : α)`. It holds by definition, so you rarely need the `rw`.

| Before | After |
|---|---|
| ⊢ a ∈ {x \| p x} | ⊢ p a |

```lean-goal
⊢ a ∈ {x | p x}
⊢ p a
```

**R3 · `rw [Set.mem_Icc]`** changes the **goal**. Statement: `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b`. Also by
definition, so `⟨ha, hb⟩ : x ∈ Icc a b` and, for `hx : x ∈ Icc a b`, `hx.1 : a ≤ x`, `hx.2 : x ≤ b`.
Placeholders: `(a b x : ℝ)`.

| Before | After |
|---|---|
| `⊢ x ∈ Icc a b` | `⊢ a ≤ x ∧ x ≤ b` |
| `hx : x ∈ Icc a b ⊢ P` | `h2 : x ≤ b ⊢ P` (from `have h2 : x ≤ b := hx.2`) |

**R4 · `le_rfl`** **closes** `a ≤ a`. Placeholders: `{α : Type} [Preorder α] (a : α)` (a preorder has a
reflexive, transitive `≤`; `ℝ` qualifies).

**R5 · `zero_le_one`** **closes** `0 ≤ 1` in `ℝ` (and any ordered semiring).

**R6 · `refine ⟨⟨ha, hb⟩, ?_⟩`** changes the **goal**: by R2 and R3, `x ∈ {y | y ∈ Icc a b ∧ Q y}` *is*
`(a ≤ x ∧ x ≤ b) ∧ Q x`. The inner pair proves the interval part, `?_` leaves `Q x`. In the exercise
`ha, hb` are R4 and R5. Placeholders: `(a b x : ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| ⊢ x ∈ {y \| y ∈ Icc a b ∧ Q y} | `⊢ Q x` |

```lean-goal
⊢ x ∈ {y | y ∈ Icc a b ∧ Q y}
⊢ Q x
```

**R7 · `h hx`** changes the **context** (with `have`): `h : A ⊆ B` applied to `hx : x ∈ A` gives `x ∈ B`.
In the exercise: `hcov ⟨…, …⟩ : 0 ∈ ⋃ i, U i`, and later `ht ⟨hz.1, hzx⟩`, `hball ?_`.
Placeholders: `{α : Type} (A B : Set α) (x : α)`.

| Before | After |
|---|---|
| `h : A ⊆ B, hx : x ∈ A ⊢ P` | `hB : x ∈ B ⊢ P` |

**R8 · `Set.mem_iUnion`** changes the **context**. Statement: `x ∈ ⋃ i, U i ↔ ∃ i, x ∈ U i`. Write
`obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h` to name the index. Placeholders:
`{ι : Type} (U : ι → Set ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `h : x ∈ ⋃ i, U i` and `⊢ P` | `i : ι, hi : x ∈ U i ⊢ P` |

**R9 · `intro z hz`** on `A ⊆ B` changes the **goal and the context**: `⊆` unfolds to a `∀`, so it
introduces like one. In a term, `refine ⟨t, fun z hz => ?_⟩` gives the finset and opens the subset at once.
Placeholders: `{α : Type} (A B : Set α)`.

| Before | After |
|---|---|
| `⊢ A ⊆ B` | `z : α, hz : z ∈ A ⊢ z ∈ B` |

**R10 · `le_antisymm`** changes the **context**. Statement: `a ≤ b → b ≤ a → a = b`. In the exercise
`z ∈ Icc 0 0` gives both inequalities (R3), hence `z = 0`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b ≤ a ⊢ P` | `h : a = b ⊢ P` |

**R11 · `Set.mem_iUnion₂`** changes the **goal** (with `.mpr` or `rw`) or the **context** (with `.mp`).
Statement: `x ∈ ⋃ i, ⋃ j, s i j ↔ ∃ i j, x ∈ s i j`; for `⋃ i ∈ t, U i` the `j` is a proof of `i ∈ t`. So
`Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩` proves `x ∈ ⋃ i ∈ t, U i`, and
`obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h` takes it apart. Placeholders:
`{ι : Type} (U : ι → Set ℝ) (t : Finset ι) (x : ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ x ∈ ⋃ i ∈ t, U i` | `⊢ ∃ i, ∃ (_ : i ∈ t), x ∈ U i` |
| `h : x ∈ ⋃ i ∈ t, U i` and `⊢ P` | `i : ι, hi : i ∈ t, hxi : x ∈ U i ⊢ P` |

**R12 · `Finset.mem_singleton_self i`** **closes** `i ∈ ({i} : Finset ι)`: the middle component of R11 for
the one-element finset.

**R13 · `h ▸ e`** **closes** the goal: from `h : a = b` and `e` proving the goal with `a` replaced by `b`.
`▸` rewrites with `h` (it tries both directions) until `e` fits. In the exercise: `hz0 : z = 0`,
`hi : 0 ∈ U i`, goal `z ∈ U i`; and at the very end `hy1 : y = 1` turns a cover of `Icc 0 y` into one of
`Icc 0 1`. Placeholders: `{α : Type} (P : α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `h : a = b, e : P b ⊢ P a` | closed by `exact h ▸ e` |

---

## Part 2 · `extend_cover` (milestone)

Statement: if `t` covers `Icc 0 x`, `ball s ε ⊆ U j` and `s - ε < x`, then `insert j t` covers
`Icc 0 (min (s + ε / 2) 1)`. Open the subset (R9), then split on `z ≤ x`.

**R14 · `by_cases h : p`** changes the **goal list**: two goals, one with `h : p` (`case pos`), one with
`h : ¬p` (`case neg`). Placeholders: `(p Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `h : p ⊢ Q`, `h : ¬p ⊢ Q` |

**R15 · `Finset.mem_insert_of_mem`** changes the **context** (or proves the middle component of R11).
Statement: `a ∈ s → a ∈ insert b s`: what was in `t` is still in `insert j t`. Placeholders:
`{ι : Type} [DecidableEq ι] (i j : ι) (t : Finset ι)`.

| Before | After |
|---|---|
| `hi : i ∈ t ⊢ P` | `h : i ∈ insert j t ⊢ P` |

**R16 · `push Not at h`** changes the **context**: it pushes `¬` inward, and `¬(a ≤ b)` becomes `b < a`. It
is Mathlib's newer spelling of `push_neg`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : ¬a ≤ b ⊢ P` | `h : b < a ⊢ P` |

**R17 · `Finset.mem_insert_self j t`** **closes** `j ∈ insert j t`: the new index is in the new finset.

**R18 · `rw [Metric.mem_ball]`** changes the **goal**. Statement: `y ∈ Metric.ball x ε ↔ dist y x < ε`.
Placeholders: `(x y ε : ℝ) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (y ∈ Metric.ball x ε)` | `⊢ P (dist y x < ε)` |

**R19 · `rw [Real.dist_eq]`** changes the **goal**. Statement: `dist x y = |x - y|` on `ℝ`. Placeholders:
`(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (dist y x)` | ⊢ P \|y - x\| |

```lean-goal
⊢ P (dist y x)
⊢ P |y - x|
```

**R20 · `rw [abs_lt]`** changes the **goal**. Statement: `|a| < b ↔ -b < a ∧ a < b`. Then `constructor`
gives the two linear goals. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ \|a\| < b | `⊢ -b < a ∧ a < b` |

```lean-goal
⊢ |a| < b
⊢ -b < a ∧ a < b
```

**R21 · `min_le_left a b : min a b ≤ a`** and **R22 · `min_le_right a b : min a b ≤ b`** are terms: they
**close** such a goal, or feed R23 and R24. In the exercise `_` may stand for `a` and `b`.

**R23 · `h1.trans h2`** (`le_trans`) changes the **context**. Statement: `a ≤ b → b ≤ c → a ≤ c`. In the
exercise `hz.2.trans (min_le_left _ _) : z ≤ s + ε / 2`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b ≤ c ⊢ P` | `h : a ≤ c ⊢ P` |

**R24 · `linarith [t₁, t₂]`** **closes** a goal that follows linearly (with `+`, `-`, numeric `*`, `<`, `≤`,
`=`) from the context plus the extra terms `tᵢ`. It treats `min a b`, `|a|`, `sSup S` as unknowns, so facts
about them must be in the context or in the list. `constructor <;> linarith [t]` closes both halves of R20.
Placeholders: `(a b c : ℝ)`. In the example plain `linarith` fails; `linarith [min_le_left a b]` succeeds.

| Before | After |
|---|---|
| `h : c ≤ min a b ⊢ c ≤ a + 1` | closed by `linarith [min_le_left a b]` |

---

## Part 3 · `heine_borel`

Statement: `∃ t : Finset ι, Set.Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ t, U i`, given `hU : ∀ i, IsOpen (U i)` and
`hcov : Set.Icc 0 1 ⊆ ⋃ i, U i`.

**R25 · `set S : Set ℝ := e`** changes the **context and the goal**: it adds the local definition
`S : Set ℝ := e` and replaces every `e` in the goal and context by `S`. Use it twice: for the set `S` and for
`s := sSup S` (also `y := min (s + ε / 2) 1`). Placeholders: `(a b : ℝ) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Icc a b)` | `S : Set ℝ := Icc a b ⊢ P S` |

**R26 · `⟨b, fun x hx => _⟩ : BddAbove S`** changes the **goal**. `BddAbove S` unfolds to
`∃ b, b ∈ upperBounds S`, and `b ∈ upperBounds S` to `∀ ⦃x⦄, x ∈ S → x ≤ b`. In the exercise `b = 1` and
`hx.1.2 : x ≤ 1` (the `Icc` part, R3). Placeholders: `(S : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddAbove S` | `x : ℝ, hx : x ∈ S ⊢ x ≤ b` |

**R27 · `le_csSup`** changes the **context**. Statement: `BddAbove S → a ∈ S → a ≤ sSup S` (every element
is below the supremum). Used twice: `0 ≤ s`, and `y ≤ s` once `y ∈ S`. Placeholders: `(S : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `hb : BddAbove S, ha : a ∈ S ⊢ P` | `h : a ≤ sSup S ⊢ P` |

**R28 · `csSup_le`** changes the **context**. Statement: `S.Nonempty → (∀ b ∈ S, b ≤ a) → sSup S ≤ a` (the
supremum is below every upper bound). Give the nonemptiness as `⟨x, hx⟩`. Used for `s ≤ 1`. Placeholders:
`(S : Set ℝ) (x a : ℝ)`, with `hS : ∀ b ∈ S, b ≤ a`.

| Before | After |
|---|---|
| `hx : x ∈ S ⊢ P` | `h : sSup S ≤ a ⊢ P` |

**R29 · `Metric.isOpen_iff`** changes the **context**. Statement:
`IsOpen V ↔ ∀ x ∈ V, ∃ ε > 0, Metric.ball x ε ⊆ V` (open = every point has a ball inside). Write
`obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV c hc`. Placeholders: `(V : Set ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `hV : IsOpen V, hc : c ∈ V ⊢ P` | `ε : ℝ, hε : ε > 0, hball : Metric.ball c ε ⊆ V ⊢ P` |

**R30 · `exists_lt_of_lt_csSup`** changes the **context**. Statement:
`S.Nonempty → b < sSup S → ∃ a ∈ S, b < a` (anything below the supremum is beaten by an element).
Placeholders: `(S : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `hne : S.Nonempty, hb : b < sSup S ⊢ P` | `a : ℝ, ha : a ∈ S, hba : b < a ⊢ P` |

**R31 · `sub_lt_self a hb`** changes the **context**. Statement: `0 < b → a - b < a`; it supplies the `hb`
of R30 with `b := s - ε`. `hε : ε > 0` is the same as `0 < ε`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ P` | `h : a - b < a ⊢ P` |

**R32 · `obtain ⟨x, -, hB⟩ := h`** changes the **context**: `-` drops a component. In the exercise
`⟨x, ⟨-, t, ht⟩, hx⟩` takes apart `∃ a ∈ S, s - ε < a`: `x`, then `x ∈ S` = `x ∈ Icc 0 1 ∧ ∃ t, …` (drop the
`Icc` part, keep `t` and `ht`), then `hx : s - ε < x`. Placeholders: `(A B : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : ∃ x, A x ∧ B x` and `⊢ P` | `x : ℝ, hB : B x ⊢ P` |

**R33 · `le_min`** **closes** `a ≤ min b c` from `a ≤ b` and `a ≤ c`. Used for `0 ≤ y`, the left half of
`y ∈ Icc 0 1`; the right half is R22.

| Before | After |
|---|---|
| `hb : a ≤ b, hc : a ≤ c ⊢ a ≤ min b c` | closed by `exact le_min hb hc` |

**R34 · `rcases min_choice a b with h | h`** changes the **goal list**. Statement:
`min a b = a ∨ min a b = b`; the two goals are `case inl` and `case inr`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (min a b)` | `h : min a b = a ⊢ P (min a b)`, `h : min a b = b ⊢ P (min a b)` |

**R35 · `have h' : y = a := h`** changes the **context**: after `set y := min a b`, a hypothesis made later
(R34) still says `min a b`. Since `y` *is* `min a b` by definition, `h` itself proves `y = a`; the new
hypothesis states the fact in the `set` name. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `y : ℝ := min a b, h : min a b = a ⊢ P y` | `h' : y = a ⊢ P y` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a point of `V j` lies in the union over `{i, j}`** (R11, R15, R12). `{i, j}` is `insert i {j}`, so
the membership proof is `Finset.mem_insert_of_mem (Finset.mem_singleton_self j)`:

```lean-goal
⊢ x ∈ ⋃ k ∈ {i, j}, V k
⊢ ∃ i_1, ∃ (_ : i_1 ∈ {i, j}), x ∈ V i_1
```

**W2: a concrete ball** (R18, R19, R20). `rw [Metric.mem_ball, Real.dist_eq, abs_lt]`, then
`constructor <;> norm_num`:

```lean-goal
⊢ 5 / 4 ∈ Metric.ball 1 (1 / 2)
⊢ -(1 / 2) < 5 / 4 - 1 ∧ 5 / 4 - 1 < 1 / 2
```

**W3: `sSup` of `[0, 2]` lies in `[0, 2]`** (R25, R26, R27, R28). After `set T`, prove `h0 : 0 ∈ T` and
`hbdd : BddAbove T`, then give the pair `⟨le_csSup hbdd h0, csSup_le ⟨0, h0⟩ …⟩`:

```lean-goal
⊢ sSup {x | 0 ≤ x ∧ x ≤ 2} ∈ Icc 0 2
⊢ sSup T ∈ Icc 0 2
```

**W4: a `min` that is `≤ a` must be its other argument** (R25, R34, R35, R24). With `m := min (a + 1) 5`
and `hle : m ≤ a`: in `case inl`, `m = a + 1` contradicts `hle`, so `linarith` closes the goal; in
`case inr`, `h` is the goal. This is step 5 of the maths with `s + ε/2` in place of `a + 1`:

```lean-goal
⊢ m = 5
```

---

## Traps

- **No compactness in any form**, including the `CompactSpace` instance on the subtype `Icc 0 1`. Every compactness name (`IsCompact`, `CompactSpace`, `isCompact_Icc`, the Lebesgue
  number lemma, `unitInterval`, …) is on the `BANNED:` line, and so are `Set.image`, `Set.preimage`,
  `fun_prop` and `continuity`. The checker matches the last name component, so `open` does not dodge it.
- `insert j t` needs `DecidableEq ι`. Start `heine_borel` with `classical` (R1), or `extend_cover`'s
  `[DecidableEq ι]` argument cannot be found.
- `set` only rewrites what exists *when it runs*. A hypothesis made later by `rcases min_choice …` says
  `min (s + ε / 2) 1`, not `y` (R35).
- `sSup` of an arbitrary `Set ℝ` is junk (`0`) when the set is empty or unbounded: every `cs…` lemma asks for
  `BddAbove` or `Nonempty`. Prove `h0 : 0 ∈ S` and `hbdd : BddAbove S` first, and reuse them.
- `hε : ε > 0` is `0 < ε`; `sub_lt_self s hε` accepts it as is.
- The ball is `Metric.ball s ε`, so `Metric.mem_ball` gives `dist z s < ε` (point first, centre second), and
  `Real.dist_eq` gives `|z - s|`.
- `t1 ; t2` runs `t2` on the first goal only. After `constructor`, write `constructor <;> linarith [...]`.
- `hz : z ∈ Icc 0 (min (s + ε / 2) 1)`: `hz.2 : z ≤ min (s + ε / 2) 1`, which `linarith` cannot see through;
  give it `hz.2.trans (min_le_left _ _)` (R23, R21).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| decidable equality for `insert` | `classical` | R1 |
| prove `x ∈ {y \| y ∈ Icc a b ∧ Q y}` | `refine ⟨⟨ha, hb⟩, ?_⟩` | R2, R3, R6 |
| `a ≤ a`, `0 ≤ 1` | `le_rfl`, `zero_le_one` | R4, R5 |
| use `h : A ⊆ B` on `hx : x ∈ A` | `h hx` | R7 |
| prove `A ⊆ B` | `intro z hz` / `fun z hz => ?_` | R9 |
| index from `x ∈ ⋃ i, U i` | `obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h` | R8 |
| in / out of `⋃ i ∈ t, U i` | `Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩` / `.mp` | R11 |
| `a ≤ b`, `b ≤ a` → `a = b` | `le_antisymm h1 h2` | R10 |
| finset membership | `Finset.mem_singleton_self`, `Finset.mem_insert_self`, `Finset.mem_insert_of_mem` | R12, R17, R15 |
| transport along `h : a = b` | `h ▸ e` | R13 |
| case split on `p` | `by_cases h : p` | R14 |
| `¬ a ≤ b` → `b < a` | `push Not at h` | R16 |
| ball in `ℝ` → two inequalities | `rw [Metric.mem_ball, Real.dist_eq, abs_lt]` | R18–R20 |
| `min` bounds | `min_le_left`, `min_le_right`, `le_min` | R21, R22, R33 |
| chain `≤` | `h1.trans h2` | R23 |
| linear arithmetic | `linarith [extra facts]` | R24 |
| name an expression | `set S : Set ℝ := …` | R25 |
| `BddAbove S` | `⟨b, fun x hx => …⟩` | R26 |
| `a ∈ S → a ≤ sSup S` | `le_csSup hbdd ha` | R27 |
| `sSup S ≤ a` | `csSup_le ⟨x, hx⟩ fun b hb => …` | R28 |
| ball inside an open set | `Metric.isOpen_iff.mp (hU j) s hj` | R29 |
| element of `S` above `sSup S - ε` | `exists_lt_of_lt_csSup ⟨x, hx⟩ (sub_lt_self _ hε)` | R30, R31 |
| drop a component | `obtain ⟨x, -, h⟩ := …` | R32 |
| which side `min` is | `rcases min_choice a b with h \| h` | R34 |
| restate through a `set` name | `have h' : y = a := h` | R35 |
| see the state | infoview | |
