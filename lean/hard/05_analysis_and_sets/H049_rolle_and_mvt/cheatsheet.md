# H049 · Rolle and the mean value theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, intervals as
sets, compactness and the extreme value theorem (EVT), neighbourhoods `nhds`, local and set-wise
extrema, the derivative predicate `HasDerivAt` and its arithmetic, and `ContinuousOn`.

The plan: Rolle from EVT + Fermat (an interior extremum has derivative 0), MVT from Rolle applied to `f`
minus a line, and "derivative 0 ⇒ constant" from MVT on `[a, x]`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`exact`/`simp only`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal. Most lemmas here are *forward* facts: `have h := lemma args` adds `h`
  to the context; in the guide a hypothesis `k : … → G` then consumes it.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[Preorder α]` is
  a requirement on `α` (a *type class*: here, that `≤` and `<` exist). `ℝ` meets every bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`), an ordered field: `linarith`, `field_simp` work on it |
| `Set ℝ`, `x ∈ s` | a set of reals (a predicate `ℝ → Prop`), and membership in it |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}` ("I-closed-closed") |
| `Set.Ioo a b` | the open interval `(a, b) = {x \| a < x ∧ x < b}` ("I-open-open") |
| `x ∈ Set.Icc a b` | *by definition* `a ≤ x ∧ x ≤ b`: `hx.1`, `hx.2`, `⟨h1, h2⟩` work on it directly (R8, R31) |
| `x ∉ s` | `¬ (x ∈ s)`; R2 unfolds `c ∉ Set.Ioo a b` to `¬(a < c ∧ c < b)` |
| `t ⊆ s` | every element of `t` is in `s`; `hts hx : x ∈ s` for `hx : x ∈ t` |
| `{x \| p x}` | the set of `x` with `p x`; `y ∈ {x \| p x}` is by definition `p y` (R28) |
| `s.Nonempty` | `∃ x, x ∈ s` |
| `IsCompact s` | `s` is compact; for subsets of `ℝ`: closed and bounded. `Set.Icc a b` is (R18) |
| `ContinuousOn f s` | `f` restricted to `s` is continuous (no condition outside `s`) |
| `HasDerivAt f d x` | `f` is differentiable at `x` with derivative `f'(x) = d`. A *proposition*, not a function |
| `id` | the identity function, `id y = y` |
| `fun y => c * g y` | the function `y ↦ c · g(y)`. Lean may rename the bound variable (`fun x => …`) |
| `g - l` (functions) | the pointwise difference `fun y => g y - l y`; both spellings are accepted by `exact` (R33, R35) |
| `nhds x` | the neighbourhood filter of `x`; `s ∈ nhds x` means `s` contains an open interval around `x` |
| `IsMaxOn f s c` | `c` maximises `f` on `s`: `∀ x ∈ s, f x ≤ f c` (by definition, up to unfolding; R27, R29) |
| `IsMinOn f s c` | `c` minimises `f` on `s`: `∀ x ∈ s, f c ≤ f x` |
| `IsLocalMax f c` | `f x ≤ f c` for all `x` near `c` (in some neighbourhood); `IsLocalMin` likewise |
| `∃ c ∈ s, Q c` | `∃ c, c ∈ s ∧ Q c`; take it apart with R21, build it with R23 |
| `f'` | an ordinary name (the prime is part of it): here the function giving the derivative at each point |
| `k : ℝ := e` | a local definition made by `set` (R32): `k` abbreviates `e` |
| `inst✝ : Preorder α` | an anonymous type-class instance from a `[Preorder α]` binder |
| `case inl`, `case inr` | after `rcases h with … \| …`: the left / right side of an `∨` |
| `case pos`, `case neg` | after `by_cases`: the branch where the condition holds / fails |

---

## Part 1 · `endpoint` (milestone)

Statement: a point `c ∈ [a, b]` with `c ∉ (a, b)` is `a` or `b`. Unfold both memberships into
inequalities, split the negated `∧`, finish each case with `linarith`.

**R1 · `simp only [Set.mem_Icc] at h`** changes the **context**. The lemma is
`Set.mem_Icc : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b`; `simp only [l] at h` rewrites with `l` inside `h`.
Placeholders: `{α : Type} [Preorder α] (a b x : α)`.

| Before | After |
|---|---|
| `h : x ∈ Set.Icc a b ⊢ G` | `h : a ≤ x ∧ x ≤ b ⊢ G` |

**R2 · `simp only [Set.mem_Ioo] at h`** changes the **context**. The lemma is
`Set.mem_Ioo : x ∈ Set.Ioo a b ↔ a < x ∧ x < b`. Placeholders as in R1. For `hc' : c ∉ Set.Ioo a b`
(that is, `¬ c ∈ …`) it gives `¬(a < c ∧ c < b)`.

| Before | After |
|---|---|
| `h : x ∈ Set.Ioo a b ⊢ G` | `h : a < x ∧ x < b ⊢ G` |

**R3 · `not_and_or`** changes the **context** (used inside `simp only [...] at h`). The lemma is
`not_and_or : ¬(A ∧ B) ↔ ¬A ∨ ¬B` (De Morgan; classical). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `h : ¬(A ∧ B) ⊢ G` | `h : ¬A ∨ ¬B ⊢ G` |

**R4 · `not_lt`** changes the **context**. The lemma is `not_lt : ¬a < b ↔ b ≤ a`. Placeholders:
`{α : Type} [LinearOrder α] (a b : α)` (a total order; `ℝ` qualifies). R1–R4 go in one call:
`simp only [Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at hc hc'`.

| Before | After |
|---|---|
| `h : ¬a < b ⊢ G` | `h : b ≤ a ⊢ G` |

**R5 · `rcases h with h1 | h2`** changes the **goal list and the context**: `h : A ∨ B` is replaced by
two goals, one with `h1 : A`, one with `h2 : B`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h1 : A ⊢ G`, `h2 : B ⊢ G` |

**R6 · `left` / `right`** changes the **goal**: to prove `A ∨ B`, commit to one side.

| Before | After `right` |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R7 · `linarith`** **closes** a goal (`=`, `≤`, `<`, or `False`) that is a linear consequence of the
hypotheses over an ordered field such as `ℝ`. It proves `x = a` from `x ≤ a` and `a ≤ x`. It reads both
halves of a hypothesis `h : A ∧ B`, but **not** a membership `hx : x ∈ Set.Icc a b` (its `∧` is hidden
behind the definition of `Set.Icc`): unfold it first with R1/R2 or take `hx.1`, `hx.2` (R8).

| Before | After |
|---|---|
| `h1 : x ≤ a, h2 : a ≤ x ⊢ x = a` | no goals |

---

## Part 2 · `interior_max` (milestone)

Statement: if `c ∈ (a, b)` maximises `f` on `[a, b]` and `HasDerivAt f d c`, then `d = 0`. Chain:
`[a, b]` is a neighbourhood of `c` (R9), so the max on `[a, b]` is a local max (R10), so Fermat (R11).

**R8 · `hx.1`, `hx.2`** change the **context** (with `have`): membership in an interval *is* a
conjunction, so its projections work without R1/R2. Placeholders: `(a b x : ℝ) (hx : x ∈ Set.Ioo a b)`.

| Before | After `have h1 : a < x := hx.1` |
|---|---|
| `hx : x ∈ Set.Ioo a b ⊢ G` | `h1 : a < x ⊢ G` |

**R9 · `Icc_mem_nhds`** changes the **context**. The lemma is
`Icc_mem_nhds : a < x → x < b → Set.Icc a b ∈ nhds x`: a closed interval is a neighbourhood of each
interior point. Placeholders: `(a b x : ℝ) (h1 : a < x) (h2 : x < b)`.

| Before | After `have hn := Icc_mem_nhds h1 h2` |
|---|---|
| `h1 : a < x, h2 : x < b ⊢ G` | `hn : Set.Icc a b ∈ nhds x ⊢ G` |

**R10 · `IsMaxOn.isLocalMax`** changes the **context**. The lemma is
`IsMaxOn.isLocalMax : IsMaxOn f s c → s ∈ nhds c → IsLocalMax f c`. Dot notation: `hmax.isLocalMax hn`.
Placeholders: `(f : ℝ → ℝ) (s : Set ℝ) (c : ℝ)`.

| Before | After `have hl := hmax.isLocalMax hn` |
|---|---|
| `hmax : IsMaxOn f s c, hn : s ∈ nhds c ⊢ G` | `hl : IsLocalMax f c ⊢ G` |

**R11 · `IsLocalMax.hasDerivAt_eq_zero`** changes the **context** (or closes a goal `d = 0` with
`exact`). The lemma (Fermat) is `IsLocalMax f c → HasDerivAt f d c → d = 0`. Placeholders:
`(f : ℝ → ℝ) (c d : ℝ)`.

| Before | After `have h0 := hl.hasDerivAt_eq_zero hd` |
|---|---|
| `hl : IsLocalMax f c, hd : HasDerivAt f d c ⊢ G` | `h0 : d = 0 ⊢ G` |

---

## Part 3 · `line_hasDerivAt` (milestone)

Statement: `y ↦ k * (y - a)` has derivative `k` at every `x`. Build it from the identity: subtract a
constant, multiply by a constant, then clean up `k * 1` and `id`.

**R12 · `hasDerivAt_id x`** changes the **context**: `hasDerivAt_id x : HasDerivAt id 1 x`.
Placeholders: `(x : ℝ)`. (`hasDerivAt_id' x` is the same fact with `fun x => x` instead of `id`.)

| Before | After `have h1 := hasDerivAt_id x` |
|---|---|
| `⊢ G` | `h1 : HasDerivAt id 1 x ⊢ G` |

**R13 · `HasDerivAt.sub_const`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt (fun y => g y - c) d x` (the constant `c` is explicit: `hg.sub_const c`).
Placeholders: `(g : ℝ → ℝ) (d c x : ℝ)`.

| Before | After `have h2 := hg.sub_const c` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `h2 : HasDerivAt (fun x => g x - c) d x ⊢ G` |

**R14 · `HasDerivAt.const_mul`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt (fun y => c * g y) (c * d) x` (`c` explicit: `hg.const_mul c`).
Placeholders as in R13.

| Before | After `have h3 := hg.const_mul c` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `h3 : HasDerivAt (fun y => c * g y) (c * d) x ⊢ G` |

**R15 · `simpa using h`** **closes** the goal: it simplifies both the goal and `h` with `simp`, then
closes the goal with `h`. Here it turns `c * 1` into `c`; it also rewrites `id y` to `y`. Applied to the
chain R12 → R13 → R14, `h` reads `HasDerivAt (fun y => k * (id y - a)) (k * 1) x` before cleaning.

| Before | After |
|---|---|
| `h : HasDerivAt (fun y => c * g y) (c * 1) x ⊢ HasDerivAt (fun y => c * g y) c x` | no goals |

---

## Part 4 · `rolle`

Statement: `a < b`, `f` continuous on `[a, b]`, `f` has derivative `f' x` at each `x ∈ (a, b)`, and
`f a = f b` ⇒ some `c ∈ (a, b)` has `f' c = 0`. EVT gives a max point `c` and a min point `d`. If one is
interior, Fermat. If both are endpoints, max value = min value = `f a`, so `f` is constant on `[a, b]` and
the midpoint `(a + b) / 2` is a max point.

**R16 · `Set.nonempty_Icc`** changes the **context**. The lemma is
`Set.nonempty_Icc : (Set.Icc a b).Nonempty ↔ a ≤ b`; `.mpr` is the direction `a ≤ b → …`.
Placeholders: `(a b : ℝ) (hab : a ≤ b)`.

| Before | After `have hne := Set.nonempty_Icc.mpr hab` |
|---|---|
| `hab : a ≤ b ⊢ G` | `hne : (Set.Icc a b).Nonempty ⊢ G` |

**R17 · `h.le`** changes the **context**: `LT.lt.le : a < b → a ≤ b`, by dot notation on `h : a < b`.

| Before | After `have hle := h.le` |
|---|---|
| `h : a < b ⊢ G` | `hle : a ≤ b ⊢ G` |

**R18 · `isCompact_Icc`** changes the **context**: `isCompact_Icc : IsCompact (Set.Icc a b)` (`a b`
implicit, so give the type or use it as `isCompact_Icc.exists_isMaxOn …`).

| Before | After `have hK : IsCompact (Set.Icc a b) := isCompact_Icc` |
|---|---|
| `⊢ G` | `hK : IsCompact (Set.Icc a b) ⊢ G` |

**R19 · `IsCompact.exists_isMaxOn`** closes an existence **goal** (or, with `have`, adds it to the **context**). The lemma (EVT) is
`IsCompact s → s.Nonempty → ContinuousOn f s → ∃ c ∈ s, IsMaxOn f s c`. Placeholders:
`(f : ℝ → ℝ) (s : Set ℝ)`.

| Before | After `exact hK.exists_isMaxOn hne hf` |
|---|---|
| `hK : IsCompact s, hne : s.Nonempty, hf : ContinuousOn f s ⊢ ∃ c ∈ s, IsMaxOn f s c` | no goals |

**R20 · `IsCompact.exists_isMinOn`** closes the **goal**: the same with `IsMinOn`.

| Before | After `exact hK.exists_isMinOn hne hf` |
|---|---|
| `hK : IsCompact s, hne : s.Nonempty, hf : ContinuousOn f s ⊢ ∃ c ∈ s, IsMinOn f s c` | no goals |

**R21 · `obtain ⟨c, hc, hP⟩ := h`** changes the **context**: `h : ∃ c ∈ s, Q c` is replaced by the point,
its membership and its property. Write `-` for a part you do not need (`obtain ⟨c, -, hP⟩ := h`).
Combine with R19: `obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn hne hfc`. Placeholders:
`(s : Set ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : ∃ c ∈ s, Q c` in the context, `⊢ G` | `c : ℝ, hc : c ∈ s, hP : Q c ⊢ G` |

**R22 · `by_cases h : p`** changes the **goal list**: two copies of the goal, one with `h : p`, one with
`h : ¬p` (classical). In the exercise, `p` is `c ∈ Set.Ioo a b`; close the first copy with
`· exact …` and continue in the second.

| Before | After |
|---|---|
| `⊢ G` | `h : p ⊢ G`, `h : ¬p ⊢ G` |

**R23 · `exact ⟨c, hc, hP⟩`** **closes** `∃ x ∈ s, Q x`: give the witness, its membership, its property.

| Before | After |
|---|---|
| `hc : c ∈ s, hP : Q c ⊢ ∃ x ∈ s, Q x` | no goals |

**R24 · `IsMinOn.isLocalMin`** changes the **context**: `IsMinOn f s c → s ∈ nhds c → IsLocalMin f c`.

| Before | After `have hl := hmin.isLocalMin hn` |
|---|---|
| `hmin : IsMinOn f s c, hn : s ∈ nhds c ⊢ G` | `hl : IsLocalMin f c ⊢ G` |

**R25 · `IsLocalMin.hasDerivAt_eq_zero`** changes the **context**: Fermat at a minimum,
`IsLocalMin f c → HasDerivAt f d c → d = 0`.

| Before | After `have h0 := hl.hasDerivAt_eq_zero hd` |
|---|---|
| `hl : IsLocalMin f c, hd : HasDerivAt f d c ⊢ G` | `h0 : d = 0 ⊢ G` |

**R26 · `rcases h with rfl | rfl`** changes the **goal list and the context**: it splits `h : c = a ∨ c = b`
and *substitutes* each equation: one of the two variables disappears and the other takes its place
everywhere. Which one survives is Lean's choice (here `c`), so do not rely on the names afterwards; close
with something name-independent such as `simp [hfab]`. With `rcases h with rfl | h2`, only the left side
is substituted. Placeholders: `(a b c : ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : c = a ∨ c = b, ha : P a, hb : P b ⊢ P c` | `ha : P c ⊢ P c` (`a` gone), `hb : P c ⊢ P c` (`b` gone) |

**R27 · `intro x hx`** on an `IsMaxOn` goal changes the **goal and the context**. `IsMaxOn f s c` unfolds
to "for every `x ∈ s`, `x` lies in the set `{x | f x ≤ f c}`", so `intro` works, but the new goal is
printed as a set-builder membership:

```lean-goal
⊢ IsMaxOn f s c
⊢ x ∈ {x | (fun x => f x ≤ f c) x}
```

(context gains `x : ℝ` and `hx : x ∈ s`). `linarith` cannot read this goal: use R28 first.

**R28 · `show T`** changes the **goal** to `T`, which must be definitionally equal to it. It turns a
set-builder membership into the inequality it stands for:

```lean-goal
⊢ x ∈ {y | f y ≤ f c}
⊢ f x ≤ f c
```

**R29 · `have h1 : f x ≤ f c := hmax hx`** changes the **context**: `hmax : IsMaxOn f s c` is a function
from `x ∈ s` to the inequality. Write the type, or the fact is recorded as
`x ∈ {x | (fun x => f x ≤ f c) x}`, which `linarith` cannot use. `IsMinOn` works the same way:
`have h2 : f c ≤ f x := hmin hx` for `hmin : IsMinOn f s c`.

| Before | After |
|---|---|
| `hmax : IsMaxOn f s c, hx : x ∈ s ⊢ G` | `h1 : f x ≤ f c ⊢ G` |

**R30 · `Set.Ioo_subset_Icc_self`** changes the **context**: `Set.Ioo a b ⊆ Set.Icc a b`, applied to a
membership (a `⊆` is a function on memberships).

| Before | After `have hx' := Set.Ioo_subset_Icc_self hx` |
|---|---|
| `hx : x ∈ Set.Ioo a b ⊢ G` | `hx' : x ∈ Set.Icc a b ⊢ G` |

**R31 · `⟨h1, h2⟩`** builds a membership `x ∈ Set.Ioo a b` from `h1 : a < x` and `h2 : x < b` (it is a
conjunction, R8). Each part may be a proof term `(by linarith)`.

| Before | After `have hx : x ∈ Set.Ioo a b := ⟨h1, h2⟩` |
|---|---|
| `h1 : a < x, h2 : x < b ⊢ G` | `hx : x ∈ Set.Ioo a b ⊢ G` |

---

## Part 5 · `mvt`

Statement: same hypotheses without `f a = f b` ⇒ some `c ∈ (a, b)` has `f' c = (f b - f a) / (b - a)`.
With `k` the slope of the chord, `g x = f x - k * (x - a)` has `g a = g b`; apply `rolle` to `g` and
`g' x = f' x - k`. `rolle` is a theorem with explicit arguments, so
`obtain ⟨c, hc, h⟩ := rolle g g' a b hab h1 h2 h3` works, and Lean β-reduces the applied `fun`s in `h`
for you (`h : f' c - k = 0`). Each argument must be a finished proof: a name from a `have`, or an inline
term `(hfc.sub (by fun_prop))`. A `_` or `?_` there does **not** open a new goal; it is an error. The
hypotheses may be stated β-reduced, e.g. `h3 : f a - k * (a - a) = f b - k * (b - a)` for `g a = g b`.

**R32 · `set k := e with hk`** changes the **goal and the context**: every `e` is replaced by the new
local definition `k`, and `hk : k = e` is added. Placeholders: `(u v : ℝ)`, `e = u - v`.

| Before | After |
|---|---|
| `h : P (u - v) ⊢ P (u - v)` | `k : ℝ := u - v, h : P k, hk : k = u - v ⊢ P k` |

**R33 · `ContinuousOn.sub`** changes the **context**. The lemma is
`ContinuousOn g s → ContinuousOn l s → ContinuousOn (g - l) s`. The result is stated for `g - l`, which is
by definition `fun y => g y - l y`. Placeholders: `(g l : ℝ → ℝ) (s : Set ℝ)`.

| Before | After `have hc := hg.sub hl` |
|---|---|
| `hg : ContinuousOn g s, hl : ContinuousOn l s ⊢ G` | `hc : ContinuousOn (g - l) s ⊢ G` |

**R34 · `fun_prop`** **closes** a continuity goal for a function built from `+`, `-`, `*`, constants and
the variable (also `Continuous`, and `ContinuousOn` on any set). Use it as the second argument of R33:
`hfc.sub (by fun_prop)`.

| Before | After |
|---|---|
| `⊢ ContinuousOn (fun y => c * (y + d)) s` | no goals |

**R35 · `HasDerivAt.sub`** **closes** (via `exact`) a derivative goal for a difference. The lemma is
`HasDerivAt g d x → HasDerivAt l e x → HasDerivAt (g - l) (d - e) x`. Placeholders:
`(g l : ℝ → ℝ) (d e x : ℝ)`. In the exercise: `(hff' x hx).sub (line_hasDerivAt k a x)`.

| Before | After `exact hg.sub hl` |
|---|---|
| `hg : HasDerivAt g d x, hl : HasDerivAt l e x ⊢ HasDerivAt (fun y => g y - l y) (d - e) x` | no goals |

**R36 · `simp only [sub_self, mul_zero, sub_zero]`** changes the **goal**: it applies the `fun` to its
argument (β-reduction) and cleans up `g a - c * (a - a)`. The lemmas: `sub_self : a - a = 0`,
`mul_zero : a * 0 = 0`, `sub_zero : a - 0 = a`. Add `hk` (R32) to the list to expand `k`.
Placeholders: `(g : ℝ → ℝ) (c a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((fun y => g y - c * (y - a)) a)` | `⊢ P (g a)` |

**R37 · `field_simp`** changes the **goal**: it cancels or multiplies out denominators it can prove
nonzero, using hypotheses such as `hd : d ≠ 0` in the context. Prove that fact first:
`have hba : b - a ≠ 0 := by linarith` works from `hab : a < b` (`≠` is `= → False`, which `linarith`
refutes). Then `ring` (TACTIC_STATES) finishes. Placeholders: `(u v d : ℝ) (hd : d ≠ 0)`.

| Before | After |
|---|---|
| `hd : d ≠ 0 ⊢ v = u + (v - u) / d * d` | `hd : d ≠ 0 ⊢ v = u + (v - u)` |

---

## Part 6 · `const_of_deriv_zero`

Statement: `f` continuous on `[a, b]` with derivative `0` on `(a, b)` ⇒ `f x = f a` for all
`x ∈ [a, b]`. For `x = a` it is `rfl`; for `a < x`, apply `mvt` on `[a, x]` with `f' = fun _ => 0`: then
`0 = (f x - f a) / (x - a)`.

**R38 · `eq_or_lt_of_le`** changes the **context**: `eq_or_lt_of_le : a ≤ b → a = b ∨ a < b`. Use it
inside R26: `rcases eq_or_lt_of_le hx.1 with rfl | hax`.

| Before | After `have h' := eq_or_lt_of_le h` |
|---|---|
| `h : a ≤ b ⊢ G` | `h' : a = b ∨ a < b ⊢ G` |

**R39 · `ContinuousOn.mono`** changes the **context**: `ContinuousOn g s → t ⊆ s → ContinuousOn g t`
(continuity restricts to a smaller set). Placeholders: `(g : ℝ → ℝ) (s t : Set ℝ)`.

| Before | After `have hgt := hg.mono hts` |
|---|---|
| `hg : ContinuousOn g s, hts : t ⊆ s ⊢ G` | `hgt : ContinuousOn g t ⊢ G` |

**R40 · `Set.Icc_subset_Icc_right`** changes the **context**:
`b₁ ≤ b₂ → Set.Icc a b₁ ⊆ Set.Icc a b₂` (shrink the right end). Its implicit names are not `a b₁ b₂`,
so give the result type (or use it directly as the second argument of R39).

| Before | After `have hsub : Set.Icc a b₁ ⊆ Set.Icc a b₂ := Set.Icc_subset_Icc_right h` |
|---|---|
| `h : b₁ ≤ b₂ ⊢ G` | `hsub : Set.Icc a b₁ ⊆ Set.Icc a b₂ ⊢ G` |

**R41 · `h1.trans_le h2`** changes the **context**: `LT.lt.trans_le : a < b → b ≤ c → a < c`. It gives
`y < b` from `y < x` and `x ≤ b`, so a point of `(a, x)` lies in `(a, b)`: `⟨hy.1, hy.2.trans_le hx.2⟩`.

| Before | After `have h3 := h1.trans_le h2` |
|---|---|
| `h1 : a < b, h2 : b ≤ c ⊢ G` | `h3 : a < c ⊢ G` |

**R42 · `field_simp at h`** changes the **context**: it clears the denominator of `h`, using
`hd : d ≠ 0` from the context. `linarith` then reads `0 * d = u` correctly.

| Before | After |
|---|---|
| `h : 0 = u / d ⊢ G` | `h : 0 * d = u ⊢ G` |

---

## Worked combinations (W1–W5, on objects that are not the exercise's)

**W1. EVT on `[0, 1]`** (R16, R18, R20): `Set.nonempty_Icc.mpr zero_le_one`, then
`isCompact_Icc.exists_isMinOn hne hg` closes

```lean-goal
⊢ ∃ x ∈ Set.Icc 0 1, IsMinOn g (Set.Icc 0 1) x
```

**W2. Fermat at an interior minimum of `[0, 2]`** (R9, R24, R25): first
`have hn : Set.Icc (0 : ℝ) 2 ∈ nhds 1 := Icc_mem_nhds (by norm_num) (by norm_num)`, then
`exact (hmin.isLocalMin hn).hasDerivAt_eq_zero hd`.

**W3. Slope of `y ↦ 2 * y - c`** (R12, R14, R13, R15):
`simpa using ((hasDerivAt_id x).const_mul 2).sub_const c`.

**W4. Tilting `g` by `2 * y`** (R33, R34, R35): `hg.sub (by fun_prop)` and
`hd.sub (by simpa using (hasDerivAt_id x).const_mul 2)` give

```lean-goal
⊢ ContinuousOn (fun y => g y - 2 * y) s
⊢ HasDerivAt (fun y => g y - 2 * y) (g' x - 2) x
```

**W5. Restrict continuity from `[0, 2]` to `[0, 1]`** (R39, R40):
`hg.mono (Set.Icc_subset_Icc_right (by norm_num))`.

---

## Traps

- Mathlib's own Rolle/MVT, the derivative-sign monotonicity lemmas, Darboux, the fundamental theorem of
  calculus and ODE uniqueness are **banned** (see `BANNED:`), and so are `deriv`, `derivWithin`,
  `HasDerivWithinAt` and the differentiability predicates: work with `HasDerivAt` only. EVT (R19, R20),
  Fermat (R11, R25) and the `HasDerivAt` arithmetic (R12–R14, R35) are allowed.
- `IsMaxOn` is not literally `∀ x ∈ s, …`: `intro` works, but the goal and `hmax hx` print as
  `x ∈ {x | …}`. Use `show` (R28) and typed `have` (R29) before `linarith`.
- `linarith` reads `h : A ∧ B`, but not `hx : x ∈ Set.Icc a b`: that must become `hx.1`, `hx.2` (or go
  through R1/R2) first.
- After `rcases h with rfl | rfl` the surviving variable may be the *other* one (R26): `hfab : f a = f b`
  can become `f c = f b`. Close with `simp [hfab]` rather than by names.
- `obtain ⟨…⟩ := rolle … _ _ _` (or `?_ ?_ ?_`) fails with "don't know how to synthesize placeholder".
  Prove the three hypotheses as `have`s first, or pass them inline as terms (Part 5).
- `rolle` needs `g a = g b` for the tilted function `g`. As an inline `(by …)` argument the goal is
  already β-reduced, `f a - k * (a - a) = f b - k * (b - a)`; if a goal still shows
  `(fun x => …) a`, `simp only` with R36 performs the application.
- `field_simp` only clears a denominator it can prove nonzero: have `hba : b - a ≠ 0` (or
  `x - a ≠ 0`) in the context first.
- In `const_of_deriv_zero` the interval may be degenerate (`x = a`); split on `eq_or_lt_of_le hx.1`
  before calling `mvt`, which needs `a < x`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| membership → inequalities | `simp only [Set.mem_Icc, Set.mem_Ioo, not_and_or, not_lt] at h` | R1–R4 |
| parts of a membership | `hx.1`, `hx.2`; build with `⟨h1, h2⟩` | R8, R31 |
| case split on `∨` | `rcases h with h1 \| h2` (`rfl` to substitute) | R5, R26 |
| choose a side of `∨` | `left` / `right` | R6 |
| linear arithmetic | `linarith` | R7 |
| `[a, b]` is a neighbourhood of an interior `x` | `Icc_mem_nhds h1 h2` | R9 |
| max/min on a set → local | `hmax.isLocalMax hn` / `hmin.isLocalMin hn` | R10, R24 |
| Fermat | `hl.hasDerivAt_eq_zero hd` | R11, R25 |
| derivative of a line | `simpa using ((hasDerivAt_id x).sub_const a).const_mul k` | R12–R15 |
| `[a, b]` nonempty | `Set.nonempty_Icc.mpr hab.le` | R16, R17 |
| EVT | `obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn hne hfc` | R18–R21 |
| case split on a proposition | `by_cases h : c ∈ Set.Ioo a b` | R22 |
| prove `∃ c ∈ s, Q c` | `exact ⟨c, hc, hQ⟩` | R23 |
| prove `IsMaxOn f s c` | `intro x hx; show f x ≤ f c` | R27, R28 |
| use `IsMaxOn` | `have h1 : f x ≤ f c := hmax hx` | R29 |
| `(a, b) ⊆ [a, b]` | `Set.Ioo_subset_Icc_self hx` | R30 |
| name a subterm | `set k := e with hk` | R32 |
| continuity of `f - line` | `hfc.sub (by fun_prop)` | R33, R34 |
| derivative of a difference | `(hff' x hx).sub hline` | R35 |
| evaluate `(fun y => …) a` | `simp only [sub_self, mul_zero, sub_zero, hk]` | R36 |
| clear denominators | `field_simp` / `field_simp at h` (needs `d ≠ 0`) | R37, R42 |
| `a ≤ b` → `a = b ∨ a < b` | `eq_or_lt_of_le h` | R38 |
| restrict continuity | `hfc.mono (Set.Icc_subset_Icc_right hx.2)` | R39, R40 |
| `a < b ≤ c` → `a < c` | `h1.trans_le h2` | R41 |
| see the state | infoview | |
