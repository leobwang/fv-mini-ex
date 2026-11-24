# H045 · Extreme value theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `have`, `obtain`/`rcases`
patterns, `refine`, anonymous constructors `⟨_, _⟩`, `∃`/`∧`/`¬`. H044 (Bolzano–Weierstrass) uses the same
`sSup` lemmas (R19, R20, R22, R23, R27); if you did it, Part 3 will look familiar.
**New here:** Mathlib's limits as *filters* (`Tendsto`, `𝓝`, `atTop`, `∀ᶠ`), `Continuous`, `StrictMono`,
`Set.range`, least upper bounds `sSup`/`BddAbove`/`upperBounds`, casts `ℕ → ℝ`, `⌈x⌉₊`, and the tactics
`by_contra`, `push Not`, `choose`, `set`, `suffices`, `filter_upwards`, `gcongr`, `positivity`,
`exact_mod_cast`, `linarith`, `nlinarith`.

**The maths.** `X` is a topological space (a type with a notion of open sets, hence of limits). The
hypothesis `hX` says `X` is *sequentially compact*: every sequence `x : ℕ → X` has a subsequence `x ∘ φ`
(`φ : ℕ → ℕ` strictly increasing) converging to some `c : X`. `f : X → ℝ` is continuous. Route:

1. *Subsequence of values* (`seq_limit`). For any `x`, take `c, φ` from `hX`; continuity of `f` at `c` turns
   `x (φ n) → c` into `f (x (φ n)) → f c`.
2. *Bounded above* (`bdd`). If not, pick `x n` with `n < f (x n)`. By 1, `f (x (φ n)) → f c`, so for large
   `n`, `f (x (φ n)) < f c + 1`. But `n ≤ φ n < f (x (φ n))`, and `n ≥ f c + 1` for large `n`. Contradiction.
3. *Maximizing sequence* (`maximizing_seq`). With `M = sSup (range f)` (the least upper bound of the values),
   `M - 1/(n+1) < M`, so some value `f (x n)` exceeds `M - 1/(n+1)`.
4. *The maximum* (`extreme_value`). By 1 applied to that `x`, `f (x (φ k)) → f c`. Each `f y ≤ M` (2 makes
   `sSup` meaningful), so it suffices to show `M ≤ f c`, i.e. `M < f c + ε` for every `ε > 0`. Take
   `n > 1/ε`; for `k ≥ n`, `M - 1/(n+1) ≤ M - 1/(φ k + 1) < f (x (φ k))`, so in the limit
   `M - 1/(n+1) ≤ f c`, and `1/(n+1) < ε`.

The guide never uses the exercise's `f`, `X` or `hX`; it uses placeholders `g`, `u`, `s` and toy goals.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`/`refine`/`obtain`. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement and its placeholders with their types,
then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`), or the whole goal (`P : Prop`). A hypothesis `k` or `h`
  in an entry is only there to finish the example.
- `{X : Type}` is any type. A bracket such as `[TopologicalSpace X]` is a requirement on `X` (a *type
  class*). `ℝ` is a topological space, a linear order, and an ordered field, so it meets every bracket the
  lemmas here ask for (`ConditionallyCompleteLinearOrder`, `ClosedIciTopology`, `Archimedean`, …).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `𝓝 c` | the *neighbourhood filter* of `c`: "points close to `c`" (notation from `open Topology`) |
| `atTop` | the filter "`n` large" on `ℕ`: `Filter.atTop` |
| `Tendsto u atTop (𝓝 c)` | `u n → c` as `n → ∞` |
| `Tendsto g (𝓝 c) (𝓝 (g c))` | `g y → g c` as `y → c`: `g` is continuous at `c` |
| `∀ᶠ (n : ℕ) in atTop, p n` | `p n` holds for all large `n` (`∃ N, ∀ n ≥ N, p n`); `Filter.Eventually` |
| `Continuous[inst✝, _] f` | `Continuous f` with its two topologies printed (the one on `X`, named `inst✝` or `inst✝¹`, and `ℝ`'s as `_`) |
| `StrictMono φ` | `∀ ⦃a b⦄, a < b → φ a < φ b` |
| `X : Type u_1` | `{X : Type*}` in the source: `X` is a type in some universe `u_1`; read it as `X : Type` |
| `x ∘ φ` | composition: `(x ∘ φ) n = x (φ n)`; `g ∘ u` and `fun n => g (u n)` are the same term |
| `f ∘ x ∘ φ` | `f ∘ (x ∘ φ)` (`∘` groups to the right), i.e. `fun n => f (x (φ n))`: what R3 gives in `seq_limit` |
| `∃ c φ, A ∧ B` | `∃ c, ∃ φ, A ∧ B`: one pattern `⟨c, φ, hA, hB⟩` takes it apart |
| `range f` | `Set.range f = {y \| ∃ x, f x = y}`, the set of values of `f` (`open Set`) |
| `∃ a ∈ s, p a` | `∃ a, a ∈ s ∧ p a` |
| `s.Nonempty` | `∃ x, x ∈ s` |
| `sSup s` | least upper bound of `s : Set ℝ`; meaningful only when `s` is nonempty and bounded above (the `cs…` lemmas ask for that) |
| `upperBounds s` | `{b \| ∀ ⦃y⦄, y ∈ s → y ≤ b}` |
| `BddAbove s` | `(upperBounds s).Nonempty`: some upper bound exists |
| `↑n` | the natural number `n` cast into `ℝ` (`(n : ℝ)` in source) |
| `⌈a⌉₊` | `Nat.ceil a`: the least `n : ℕ` with `a ≤ ↑n` |
| `M : ℝ := sSup (range f)` | a local definition made by `set` (R24): `M` stands for that value |
| `id ≤ φ` | pointwise: `∀ n, id n ≤ φ n`, i.e. `n ≤ φ n` |
| `inst✝ : TopologicalSpace X`, `inst✝¹ …` | anonymous type-class hypotheses from the `[…]` binders: here the topology on `X` |
| `inst✝ : Nonempty X` | the same for `[Nonempty X]`: `X` has at least one element |
| `↑(φ k)` | the natural number `φ k` cast into `ℝ`; `↑(φ k) + 1` is computed in `ℝ` |
| `case a` | a goal name left by `gcongr`; ignore it |

---

## Part 1 · `seq_limit` (milestone)

Statement: for every sequence `x : ℕ → X` there are `c` and a strictly increasing `φ` with
`f (x (φ n)) → f c`.

**R1 · `obtain ⟨c, φ, hφ, hlim⟩ := h`** changes the **context**: a nested `∃ c, ∃ φ, A ∧ B` becomes four
hypotheses. In the exercise `h` is `hX x`. Placeholders: `{X : Type} [TopologicalSpace X] (u : ℕ → X)`.

| Before | After |
|---|---|
| `h : ∃ c φ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 c)` and `⊢ P` | `c : X, φ : ℕ → ℕ, hφ : StrictMono φ, hlim : Tendsto (u ∘ φ) atTop (𝓝 c) ⊢ P` |

**R2 · `Continuous.tendsto`** changes the **context** (with `have`). Statement:
`Continuous g → ∀ c, Tendsto g (𝓝 c) (𝓝 (g c))`; write `hg.tendsto c`. Placeholders:
`{X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y) (c : X)`.

| Before | After |
|---|---|
| `⊢ P` | `h2 : Tendsto g (𝓝 c) (𝓝 (g c)) ⊢ P` |

**R3 · `Filter.Tendsto.comp`** changes the **context**. Statement:
`Tendsto g y z → Tendsto u x y → Tendsto (g ∘ u) x z` (limits compose: if `u → c` and `g` is continuous at
`c`, then `g ∘ u → g c`). Write `hg.comp hu`. `g ∘ u` unfolds to `fun n => g (u n)`, so `exact h3` closes a
goal written either way. In the exercise `u` is `x ∘ φ`, and `f ∘ (x ∘ φ)` unfolds to `fun n => f (x (φ n))`.
Placeholders as in R2, plus `(u : ℕ → X)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => g (u n)) atTop (𝓝 (g c))` | `h3 : Tendsto (g ∘ u) atTop (𝓝 (g c)) ⊢ Tendsto (fun n => g (u n)) atTop (𝓝 (g c))` |

---

## Part 2 · `bdd` (milestone)

Statement: `BddAbove (range f)`: the values of `f` have an upper bound.

**R4 · `by_contra hnb`** changes the **goal and the context**: to prove `Q`, assume `hnb : ¬Q` and prove
`False`. Used twice: for `BddAbove (range f)`, and inside the `have` for `∃ x, ↑n < f x`.
Placeholders: `(Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `hnb : ¬Q ⊢ False` |

**R5 · `push Not at h`** changes the **context**: it pushes `¬` inward through `∃`, `∀` and `<`
(`¬∃ x, p x` ↦ `∀ x, ¬p x`, `¬(b < a)` ↦ `a ≤ b`). It is Mathlib's newer spelling of `push_neg`.
Placeholders: `{X : Type} (g : X → ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `h : ¬∃ x, b < g x` and `⊢ P` | `h : ∀ (x : X), g x ≤ b` and `⊢ P` |

**R6 · `refine ⟨b, ?_⟩` on `BddAbove s`** changes the **goal**: `BddAbove s` unfolds to
`∃ b, b ∈ upperBounds s`, so give the bound and prove it is one. In the exercise you write the term
`hnb ⟨↑n, …⟩` directly. Placeholders: `{X : Type} (g : X → ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddAbove (range g)` | `⊢ b ∈ upperBounds (range g)` |

**R7 · `rintro _ ⟨x, rfl⟩`** changes the **goal and the context**: `b ∈ upperBounds (range g)` unfolds to
`∀ ⦃y⦄, y ∈ range g → y ≤ b`, and `y ∈ range g` to `∃ x, g x = y`; the pattern names `x` and substitutes
`y := g x`. Placeholders as in R6.

| Before | After |
|---|---|
| `⊢ b ∈ upperBounds (range g)` | `x : X ⊢ g x ≤ b` |

**R8 · `choose x hx using h`** changes the **context**: from `h : ∀ n, ∃ y, A n y` it makes a function
`x : ℕ → X` and the fact `hx : ∀ n, A n (x n)` (the axiom of choice as a tactic). Used in Parts 2 and 3.
Placeholders: `{X : Type} (A : ℕ → X → Prop)`.

| Before | After |
|---|---|
| `h : ∀ (n : ℕ), ∃ y, A n y` and `⊢ P` | `x : ℕ → X ⊢ P` with `hx : ∀ (n : ℕ), A n (x n)` |

**R9 · `Filter.Tendsto.eventually_lt_const`** changes the **context**. Statement:
`v < w → Tendsto u l (𝓝 v) → ∀ᶠ n in l, u n < w` (a sequence with limit `v < w` is eventually `< w`). Write
`hu.eventually_lt_const hvw`. Placeholders: `(u : ℕ → ℝ) (v w : ℝ) (hvw : v < w)`.

| Before | After |
|---|---|
| `hu : Tendsto u atTop (𝓝 v) ⊢ P` | `h9 : ∀ᶠ (a : ℕ) in atTop, u a < w` and `⊢ P` |

**R10 · `lt_add_one`** changes the **context**: `lt_add_one a : a < a + 1`. It supplies `hvw` for R9 with
`w := f c + 1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h10 : a < a + 1 ⊢ P` |

**R11 · `Filter.eventually_ge_atTop`** changes the **context**: `eventually_ge_atTop N : ∀ᶠ n in atTop, N ≤ n`
("eventually `n ≥ N`"). Placeholders: `(N : ℕ)`.

| Before | After |
|---|---|
| `⊢ P` | `h11 : ∀ᶠ (x : ℕ) in atTop, N ≤ x` and `⊢ P` |

**R12 · `Filter.Eventually.and`** changes the **context**: two eventual facts hold together eventually.
Statement: `(∀ᶠ n in l, p n) → (∀ᶠ n in l, q n) → ∀ᶠ n in l, p n ∧ q n`; write `h1.and h2`.
Placeholders: `(p q : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `h12 : ∀ᶠ (x : ℕ) in atTop, p x ∧ q x` and `⊢ P` |

**R13 · `Filter.Eventually.exists`** changes the **context**: what holds eventually holds somewhere.
Statement: `(∀ᶠ n in atTop, p n) → ∃ n, p n` (it needs the filter to be non-trivial, automatic for
`atTop` on `ℕ`). Write `h.exists`, usually as `obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists` (W1).
Placeholders: `(p : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `h13 : ∃ x, p x` and `⊢ P` |

**R14 · `StrictMono.id_le`** changes the **context**. Statement: `StrictMono φ → id ≤ φ` on `ℕ`, so
`hφ.id_le n : n ≤ φ n` (a strictly increasing `φ : ℕ → ℕ` never falls below the identity). Its type prints as
`id n ≤ φ n`; state it with `have h : n ≤ φ n := hφ.id_le n` to see the clean form.
Placeholders: `(φ : ℕ → ℕ) (n : ℕ)`.

| Before | After |
|---|---|
| `hφ : StrictMono φ ⊢ P` | `h14 : n ≤ φ n ⊢ P` |

**R15 · `exact_mod_cast h`** **closes** a goal that is `h` with casts inserted: from `h : m ≤ n` in `ℕ` it
proves `↑m ≤ ↑n` in `ℝ`. Use `by exact_mod_cast …` inside a term. Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ ↑m ≤ ↑n` | closed |

**R16 · `Nat.le_ceil`** changes the **context**: `Nat.le_ceil a : a ≤ ↑⌈a⌉₊`. Use it with
`a := f c + 1` to get a natural number `N = ⌈f c + 1⌉₊` above `f c + 1`, for R11. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h16 : a ≤ ↑⌈a⌉₊ ⊢ P` |

**R17 · `h1.trans h2`** (`le_trans`) changes the **context**: `a ≤ b → b ≤ c → a ≤ c`. In the exercise
`(Nat.le_ceil _).trans (by exact_mod_cast hn2)` and `hk.trans (hφ.id_le k)`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b ≤ c ⊢ P` | `h17 : a ≤ c ⊢ P` |

**R18 · `linarith`** **closes** a linear (in)equality, or `False`, that follows by adding up hypotheses
(with nonnegative coefficients). `linarith [t]` also uses the term `t`. Terms such as `f (x (φ n))` or
`1 / (↑n + 1)` are treated as unknowns.

| Before | After |
|---|---|
| `h1 : a < b, h2 : b ≤ c, h3 : c ≤ a ⊢ False` | closed |

---

## Part 3 · `maximizing_seq` (milestone)

Statement: there is `x : ℕ → X` with `sSup (range f) - 1 / (n + 1) < f (x n)` for every `n`.
It needs only `[Nonempty X]`, not boundedness: if `range f` were unbounded, `sSup` would be a junk value, and
the statement would still hold but be useless; `bdd` is what makes it meaningful in Part 4.

**R19 · `Set.range_nonempty`** changes the **context**: `range_nonempty g : (range g).Nonempty` when the
domain is nonempty (`[Nonempty X]`). Placeholders: `{X : Type} [Nonempty X] (g : X → ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h19 : (range g).Nonempty ⊢ P` |

**R20 · `sub_lt_self`** changes the **context**: `sub_lt_self a hb : a - b < a` from `hb : 0 < b`.
Placeholders: `(a b : ℝ)`. In the exercise `b := 1 / (↑n + 1)` and `hb` comes from R21.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ P` | `h20 : a - b < a ⊢ P` |

**R21 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` when `e` is built from positive pieces
(numerals, casts `↑n`, `+`, `*`, `/`). Write `(by positivity : (0 : ℝ) < 1 / (n + 1))` to give the type.

| Before | After |
|---|---|
| `⊢ 0 < 1 / (↑n + 1)` | closed |

**R22 · `exists_lt_of_lt_csSup`** changes the **context**. Statement: `s.Nonempty → b < sSup s → ∃ a ∈ s, b < a`
(anything below the least upper bound is beaten by an element). `cs` means *conditionally complete*: in `ℝ`
`sSup` behaves only for nonempty bounded sets, so the lemma asks for `s.Nonempty`. Placeholders:
`(s : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `hs : s.Nonempty, hb : b < sSup s ⊢ P` | `h22 : ∃ a ∈ s, b < a` and `⊢ P` |

**R23 · `obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h`** changes the **context**: for `s = range g`, the inner pattern
`⟨x, rfl⟩` names the point `x` and replaces the element `a` by `g x`. Write it directly as
`obtain ⟨_, ⟨x, rfl⟩, h⟩ := exists_lt_of_lt_csSup … …` (W3). Placeholders: `{X : Type} (g : X → ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `h : ∃ a ∈ range g, b < a` and `⊢ P` | `x : X, hx : b < g x ⊢ P` |

---

## Part 4 · `extreme_value`

Statement: `∃ c, ∀ x, f x ≤ f c`: `f` attains its maximum.

**R24 · `set M := e`** changes the **context and the goal**: it adds the local definition `M : ℝ := e` and
replaces `e` by `M` in the goal and in every hypothesis present now. Facts you obtain later still print
`e`; `M` and `e` are definitionally equal, so `exact` and `linarith` accept either, but `rw` does not.
Placeholders: `(s : Set ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : P (sSup s) ⊢ P (sSup s)` | `M : ℝ := sSup s, h : P M ⊢ P M` |

**R25 · `refine ⟨c, fun y => ?_⟩`** changes the **goal and the context**: give the witness `c` of
`∃ c, ∀ y, …` and introduce `y` in one step. Placeholders: `{X : Type} (Q : X → X → Prop) (c : X)`.

| Before | After |
|---|---|
| `⊢ ∃ c, ∀ (y : X), Q y c` | `y : X ⊢ Q y c` |

**R26 · `Set.mem_range_self`** changes the **context**: `mem_range_self y : g y ∈ range g` (`g` is implicit:
Lean reads it from the expected type, so give the type in a `have`, or pass it straight to R27).
Placeholders: `{X : Type} (g : X → ℝ) (y : X)`.

| Before | After |
|---|---|
| `⊢ P` | `h26 : g y ∈ range g ⊢ P` |

**R27 · `le_csSup`** changes the **context**. Statement: `BddAbove s → a ∈ s → a ≤ sSup s`. In the exercise:
`le_csSup (bdd hX hf) (mem_range_self y) : f y ≤ sSup (range f)`. Placeholders: `(s : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `hb : BddAbove s, ha : a ∈ s ⊢ P` | `h27 : a ≤ sSup s ⊢ P` |

**R28 · `suffices T by tac`** changes the **goal**: the new goal is `T`, and `tac` must prove the old goal from
`this : T` right away. Here `suffices M ≤ f c by linarith` (with `f y ≤ M` in the context).
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b ⊢ a ≤ c` | `⊢ b ≤ c` |

**R29 · `le_of_forall_pos_lt_add`** changes the **goal and the context**. Statement:
`(∀ ε, 0 < ε → a < b + ε) → a ≤ b`. Use as `refine le_of_forall_pos_lt_add fun ε hε => ?_`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ b` | `ε : ℝ, hε : 0 < ε ⊢ a < b + ε` |

**R30 · `exists_nat_gt`** changes the **context**: `exists_nat_gt x : ∃ n : ℕ, x < ↑n` (`ℝ` is
*Archimedean*: the naturals are unbounded in it). Use with `x := 1 / ε`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `n : ℕ, hn : x < ↑n ⊢ P` |

**R31 · `filter_upwards [h₁, …] with k hk …`** changes the **goal and the context**: to prove
`∀ᶠ k in atTop, Q k`, it is enough to prove `Q k` for a `k` satisfying the eventual facts `hᵢ` listed; each
becomes a plain hypothesis named after `with k`. Placeholders: `(N : ℕ) (Q : ℕ → Prop)`, list
`[eventually_ge_atTop N]` (R11).

| Before | After |
|---|---|
| `⊢ ∀ᶠ (k : ℕ) in atTop, Q k` | `k : ℕ, hk : N ≤ k ⊢ Q k` |

**R32 · `gcongr`** changes the **goal**: for a goal `lhs ≤ rhs` whose two sides have the same shape, it
reduces to the inequality between the parts that differ, using monotonicity (`1 / t` is antitone for
`t > 0`). It proves the side goals `0 < …` itself (by `positivity`), strips casts, and closes the remaining
goal when a hypothesis states it (in the exercise `h2 : ↑n ≤ ↑(φ k)` is in the context, so `gcongr` alone
closes it). Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ 1 / (↑n + 1) ≤ 1 / (↑m + 1)` | `⊢ m ≤ n` |

**R33 · `ge_of_tendsto`** changes the **context**. Statement:
`Tendsto u l (𝓝 a) → (∀ᶠ n in l, b ≤ u n) → b ≤ a` (a lower bound that holds eventually passes to the
limit). Placeholders: `(u : ℕ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `hu : Tendsto u atTop (𝓝 a) ⊢ P` | `h33 : b ≤ a ⊢ P` |

**R34 · `rw [div_lt_iff₀ hc]`** changes the **goal** (or, with `at h`, the **context**). Statement:
`0 < c → (b / c < a ↔ b < a * c)`. Write `rw [div_lt_iff₀ (by positivity)]` for the goal
`1 / (↑n + 1) < ε`, and `rw [div_lt_iff₀ hε] at hn` for `hn : 1 / ε < ↑n`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ b / c < a` | `⊢ b < a * c` |

**R35 · `nlinarith`** **closes** a goal like `linarith`, after also adding products of pairs of hypotheses;
use it when the goal has products of unknowns such as `ε * ↑n`.

| Before | After |
|---|---|
| `hx : 0 < x, h : 1 < y * x ⊢ 1 < x * (y + 1)` | closed |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: one index where two eventual facts hold** (R10, R9, R11, R12, R13). From `Tendsto u atTop (𝓝 v)`:

```lean-goal
⊢ ∃ n, u n < v + 1 ∧ 10 ≤ n
```

After `have h := (hu.eventually_lt_const (lt_add_one v)).and (eventually_ge_atTop 10)` and
`obtain ⟨n, hn1, hn2⟩ := h.exists` the context has `hn1 : u n < v + 1` and `hn2 : 10 ≤ n`.

**W2: an eventual lower bound passes to the limit** (R31, R33): `filter_upwards [eventually_ge_atTop 3] with n hn`
proves `hev : ∀ᶠ n in atTop, 2 ≤ u n`, then `ge_of_tendsto hu hev` closes:

```lean-goal
⊢ 2 ≤ a
```

**W3: a value beats `sSup - 1`** (R19, R20, R22, R23), in one `obtain`:
`obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (range_nonempty u) (sub_lt_self _ one_pos)`.

```lean-goal
⊢ ∃ N, sSup (range u) - 1 < u N
```

**W4: the ε-argument** (R29, R30, R34, R21, R35, R18): from `∀ n, a ≤ b + 1 / (↑n + 1)`, prove `a ≤ b`.

```lean-goal
⊢ a ≤ b
⊢ a < b + ε
```

`obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)` gives `hn : 1 / ε < ↑n`; the fact `h3 : 1 / (↑n + 1) < ε` is
R34 on the goal, R34 `at hn`, then `nlinarith`; finally `linarith [h n]`.

---

## Traps

- **No compactness.** `X` has no compactness instance, and the BANNED line lists every Mathlib bridge to one
  (`IsCompact`, `CompactSpace`, `IsSeqCompact`, `Continuous.exists_forall_ge`, `IsCompact.exists_isMaxOn`, …).
  The only compactness you have is the hypothesis `hX`; build everything from it.
- `sSup s` in `ℝ` is a junk value (`0`) when `s` is empty or unbounded. Every `cs…` lemma asks for
  `s.Nonempty` (R22) or `BddAbove s` (R27): that is why `bdd` comes before the main proof.
- Next to a real number, `1 / (n + 1)` with `n : ℕ` is elaborated as `1 / (↑n + 1)` in `ℝ`. With no real
  number in sight it stays in `ℕ`, where `1 / (n + 1) = 0` for `n ≥ 1`: write the type out in a `have`,
  `(0 : ℝ) < 1 / (n + 1)` or `1 / ((n : ℝ) + 1)`.
- `hφ.id_le n` has type `id n ≤ φ n`; it works with `.trans` and `exact_mod_cast`, but give it the type
  `n ≤ φ n` in a `have` before `linarith` or `rw` (R14).
- `set M := …` rewrites only what exists at that moment (R24).
- `Filter.Eventually.exists` gives one index; to have two eventual facts at the same index, merge them with
  `.and` first (R12, W1). Getting them separately gives two unrelated indices.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| take apart `hX x` | `obtain ⟨c, φ, hφ, hlim⟩ := hX x` | R1 |
| continuity at `c` as a limit | `hf.tendsto c` | R2 |
| compose limits | `(hf.tendsto c).comp hlim` | R3 |
| proof by contradiction | `by_contra h` | R4 |
| push `¬` inside | `push Not at h` | R5 |
| prove `BddAbove (range g)` | `⟨b, by rintro _ ⟨x, rfl⟩; …⟩` | R6, R7 |
| a function from `∀ n, ∃ y, …` | `choose x hx using h` | R8 |
| eventually below a constant | `hlim.eventually_lt_const (lt_add_one _)` | R9, R10 |
| eventually `n ≥ N` | `eventually_ge_atTop N` | R11 |
| one index for two eventual facts | `obtain ⟨n, h1, h2⟩ := (ha.and hb).exists` | R12, R13 |
| `n ≤ φ n` | `hφ.id_le n` | R14 |
| move a `ℕ` fact into `ℝ` | `by exact_mod_cast h` | R15 |
| a natural number above `a : ℝ` | `Nat.le_ceil a` or `exists_nat_gt a` | R16, R30 |
| chain `≤` | `h1.trans h2` | R17 |
| linear arithmetic | `linarith [t]` | R18 |
| below `sSup`, beaten by a value | `obtain ⟨_, ⟨x, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) (sub_lt_self _ hb)` | R19, R20, R22, R23 |
| `0 < 1 / (↑n + 1)` | `by positivity` | R21 |
| name an expression | `set M := sSup (range f)` | R24 |
| witness, then `∀ y` | `refine ⟨c, fun y => ?_⟩` | R25 |
| `f y ≤ sSup (range f)` | `le_csSup hbdd (mem_range_self y)` | R26, R27 |
| prove something stronger first | `suffices T by linarith` | R28 |
| `a ≤ b` via every `ε > 0` | `refine le_of_forall_pos_lt_add fun ε hε => ?_` | R29 |
| prove `∀ᶠ k in atTop, Q k` | `filter_upwards [eventually_ge_atTop n] with k hk` | R31 |
| compare `1 / (s + 1)` and `1 / (t + 1)` | `gcongr` | R32 |
| pass `b ≤ u n` to the limit | `ge_of_tendsto hlim hev` | R33 |
| clear a denominator | `rw [div_lt_iff₀ (by positivity)]` | R34 |
| products of unknowns | `nlinarith` | R35 |
| see the state | infoview | |
