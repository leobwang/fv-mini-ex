# M159 · Density of states of N two-level systems: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rw`, `simp`, `have`, `funext`,
`refine` with `?_`, `·` focusing, anonymous projections `h.1`, `h.2`. **New here:** Mathlib's finite
sets (`Finset`), finite types (`Fintype`), sets (`Set`) and the coercion `Finset → Set`, binomial
coefficients, `Finset.powersetCard`, counting by a bijection (`Finset.card_nbij'`), big-operator sums
`∑`, and regrouping a sum by the fibres of a map (`Finset.sum_fiberwise_of_maps_to`).

Physics: a configuration of `N` two-level systems is `σ : Fin N → Bool` (`true` = excited, energy `ε`).
`nUp σ` is the number of excited sites, so `E(σ) = ε · nUp σ`. The degeneracy `g(m)` of level
`E = ε m` is the number of configurations with `nUp σ = m`. Part (a): `g(m) = C(N, m)`. Part (b): the
partition function `Z = ∑_σ e^{-b E(σ)}` (`b` = inverse temperature β, `k_B = 1`) equals
`∑_{m=0}^{N} g(m) e^{-b ε m}`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal when only a hypothesis changes.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket is a requirement on the
  type (a *type class*): `[Fintype α]` says `α` is finite (`Fin N` and `Fin N → Bool` qualify),
  `[DecidablePred p]` says `p x` can be decided by computation (any `σ i = true`, `nUp σ = m` qualifies),
  `[DecidableEq α]` says `=` on `α` is decidable (`ℕ`, `Fin N` qualify).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin N → Bool` | a configuration: site `i : Fin N = {0, …, N-1}` is excited iff `σ i = true` |
| `Finset α` | a finite set of elements of `α` (a list without order or repeats). Its own type, not `Set α` |
| `Finset.univ` | the finset of all elements of a finite type `α` (`[Fintype α]`) |
| `s.card` | the number of elements of the finset `s` |
| `Fintype.card α` | the number of elements of the finite type `α`; `Fintype.card (Fin N) = N` |
| `Finset.filter p s`, `s.filter p` | the finset of `x ∈ s` with `p x` (printed `Finset.filter p s` when `p` is a name). `s.filter p` is dot notation for `Finset.filter p s`; the spec's `Finset.univ.filter fun σ => …` is `Finset.filter (fun σ => …) Finset.univ` |
| `{x ∈ t \| p x}` | the same `Finset.filter (fun x => p x) t`, a **finset** |
| `{σ \| nUp σ = m}` | `Finset.univ.filter (fun σ => nUp σ = m)`, a **finset** (`∈ univ` is not printed). Every `{x \| …}` that comes from `Finset.filter` (the statement, `nUp`, the fibres of R20, hypotheses like `hσ : σ ∈ {i \| nUp i = m}`) is a finset; it is a `Set` only after R6 rewrote a `↑(…)`. Hover over it to see its type |
| `↑s` | the finset `s` coerced to a `Set α` (the problem's `Set.MapsTo` goals need sets) |
| `{x \| p x}` after `Finset.coe_filter` | a genuine `Set α`; `x ∈ {y \| p y}` unfolds to `p x` (R7) |
| `N.choose m` | the binomial coefficient `C(N, m)` |
| `s ⊆ t` | every element of `s` is in `t` (finsets or sets) |
| `∀ x ∈ s, Q x` | `∀ x, x ∈ s → Q x`; `intro x hx` opens it |
| `∀ ⦃x⦄, …` | a *strict-implicit* binder: `x` is filled in only once a later explicit argument (here `x ∈ A`) is given; for `intro` it is an ordinary `∀` |
| `Finset.powersetCard m s` | the finset of all `m`-element subsets of `s` |
| `decide p` | the `Bool` that is `true` iff the decidable proposition `p` holds |
| `!b` | Boolean negation |
| `Set.MapsTo f A B` | `∀ x ∈ A, f x ∈ B` (R5) |
| `Set.LeftInvOn g f A` / `Set.RightInvOn g f B` | `∀ x ∈ A, g (f x) = x` / `∀ y ∈ B, f (g y) = y` (R15) |
| `(fun σ => {i \| σ i = true}) σ` | a function applied to `σ`, not yet β-reduced; `simp` reduces it, `rw` often cannot see through it |
| `∑ x ∈ s, f x` | the finite sum of `f x` over `x ∈ s` |
| `∑ σ : α, f σ` | the sum over `Finset.univ` |
| `∑ i ∈ s with g i = j, f i` | the sum over `{i ∈ s \| g i = j}`, the fibre of `g` over `j`; `∑ i with …` when `s = univ` |
| `rexp x` | `Real.exp x` |
| `↑(nUp σ)`, `↑m`, `↑(N.choose m)` | a natural number cast to `ℝ` |
| `n • a` | `n`-fold sum `a + … + a` (`n : ℕ`), turned into `↑n * a` by R24 |
| `Finset.range n` | `{0, 1, …, n - 1}` as a finset of `ℕ` |
| `x✝`, `a✝` | a hypothesis you introduced as `_`; it exists but has no usable name |
| `case refine_1`, `case h` | goal labels: the four `?_` of R4, the side goal of R20 |

---

## Part 1 · `degeneracy`

Statement: `(univ.filter fun σ : Fin N → Bool => nUp σ = m).card = N.choose m`: exactly `C(N, m)`
configurations have `m` excited sites. The infoview prints the left side as `{σ | nUp σ = m}.card`.
Idea: `σ ↦ {i | σ i = true}` (its set of excited sites) is a bijection onto the `m`-subsets of `Fin N`.

### Counting subsets

**R1 · `Finset.card_powersetCard`** changes the **goal**. The lemma is
`(powersetCard n s).card = s.card.choose n`. Placeholders: `{α : Type} (s : Finset α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Finset.powersetCard n s).card` | `⊢ P (s.card.choose n)` |

**R2 · `Finset.card_univ`** changes the **goal**: `univ.card = Fintype.card α`. Placeholders:
`{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card α)` |

**R3 · `Fintype.card_fin`** changes the **goal**: `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.
`simp` applies R1–R3 by itself once you name R1: that is how `N.choose m` is turned into
`(powersetCard m univ).card` (step 1 of the skeleton).

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

### Counting by a bijection

**R4 · `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_`** changes the **goal list**: `s.card = t.card` becomes
four goals. You supply the maps `i : α → β` and `j : β → α`. The lemma:
`Set.MapsTo i ↑s ↑t → Set.MapsTo j ↑t ↑s → Set.LeftInvOn j i ↑s → Set.RightInvOn j i ↑t → s.card = t.card`.
Placeholders: `{α β : Type} (s : Finset α) (t : Finset β) (i : α → β) (j : β → α)`. In the problem,
`i = fun σ => Finset.univ.filter fun i => σ i = true` (excited sites) and
`j = fun s i => decide (i ∈ s)` (the configuration that is excited exactly on `s`).

| Before | After |
|---|---|
| `⊢ s.card = t.card` | `⊢ Set.MapsTo i ↑s ↑t`, `⊢ Set.MapsTo j ↑t ↑s`, `⊢ Set.LeftInvOn j i ↑s`, `⊢ Set.RightInvOn j i ↑t` |

**R5 · `intro x hx`** on `Set.MapsTo` changes the **context and the goal**. `Set.MapsTo f A B` is by
definition `∀ ⦃x⦄, x ∈ A → f x ∈ B`, so `intro` works directly. Placeholders:
`{α β : Type} (f : α → β) (A : Set α) (B : Set β)`.

| Before | After |
|---|---|
| `⊢ Set.MapsTo f A B` | `x : α, hx : x ∈ A ⊢ f x ∈ B` |

### Membership: casts, filters, set-builder

In the first `MapsTo` goal, `hσ : σ ∈ ↑{σ | nUp σ = m}`: a configuration in the coerced filter. R6, R7,
R8 (in this order, all in one `simp only … at hσ`) bring it down to `hσ : nUp σ = m`. In the goal, R9–R11 do the same for the powerset.

**R6 · `Finset.coe_filter`** changes the **goal**, or with `at hx` (as in the problem) the **context**. The
lemma is `↑(s.filter p) = {x | x ∈ s ∧ p x}`: the coerced filter is a set-builder set. Placeholders:
`{α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) (x : α)`. Before, then after:

```lean-goal
⊢ x ∈ ↑(Finset.filter p s)
⊢ x ∈ {x | x ∈ s ∧ p x}
```

**R7 · `Set.mem_setOf_eq`** changes the **goal**, or with `at hx` the **context**:
`(x ∈ {y | q y}) = q x`. Placeholders: `{α : Type} (q : α → Prop) (x : α)`. Before, then after:

```lean-goal
⊢ x ∈ {y | q y}
⊢ q x
```

**R8 · `Finset.mem_univ`, `true_and`** change the **context**: `simp` rewrites `x ∈ univ` to `True` and
`True ∧ A` to `A`. Placeholders: `{α : Type} [Fintype α] (x : α) (A : Prop)`.

| Before | After |
|---|---|
| `hx : x ∈ Finset.univ ∧ A ⊢ G` | `hx : A ⊢ G` |

**R9 · `Finset.mem_coe`** changes the **context**: `a ∈ ↑s ↔ a ∈ s` (set membership in the coercion is
finset membership). `simp` may show it as `SetLike.mem_coe`. Placeholders: `{α : Type} (s : Finset α) (a : α)`.

| Before | After |
|---|---|
| `ha : a ∈ ↑s ⊢ G` | `ha : a ∈ s ⊢ G` |

**R10 · `Finset.mem_powersetCard`** changes the **context** (or the goal): `s ∈ powersetCard n t ↔ s ⊆ t ∧ s.card = n`.
Placeholders: `{α : Type} (s t : Finset α) (n : ℕ)`.

| Before | After |
|---|---|
| `hs : s ∈ Finset.powersetCard n t ⊢ G` | `hs : s ⊆ t ∧ s.card = n ⊢ G` |

**R11 · `Finset.subset_univ`** changes the **goal**: `s ⊆ univ` is always true, so `simp` turns it into
`True` and `true_and` drops it. Placeholders: `{α : Type} [Fintype α] (s : Finset α) (A : Prop)`.

| Before | After |
|---|---|
| `⊢ s ⊆ Finset.univ ∧ A` | `⊢ A` |

**R12 · `simpa [lemmas] using e`** **closes** the goal: it simplifies the type of `e` and the goal with the
same lemmas, then closes the goal with the simplified `e`. Add the name of a definition (`nUp`) to the
list to unfold it on both sides. Placeholders: `{α : Type} [Fintype α] (s : Finset α) (n : ℕ) (hs : s.card = n)`.

| Before | After |
|---|---|
| `hs : s.card = n ⊢ s ∈ Finset.powersetCard n Finset.univ` | no goals |

**R13 · `decide_eq_true_eq`** changes the **goal**: `(decide p = true) = p`. This is what turns the
configuration `fun i => decide (i ∈ s)` back into membership in `s`. Placeholders:
`(p : Prop) [Decidable p]`.

| Before | After |
|---|---|
| `⊢ P (decide p = true)` | `⊢ P p` |

**R14 · `Finset.filter_mem_eq_of_subset`** changes the **goal**. The lemma is
`s ⊆ t → {x ∈ t | x ∈ s} = s`: filtering `t` by membership in a subset `s` gives `s`. With `t = univ`
the hypothesis is R11. Placeholders: `{α : Type} [DecidableEq α] (s t : Finset α) (hst : s ⊆ t)`.
Before, then after:

```lean-goal
⊢ P ({x ∈ t | x ∈ s})
⊢ P s
```

For the second `MapsTo` goal, `simp [nUp, hs.2]` uses R6, R7, R8, R13, R11, R14 and `hs.2 : s.card = m`.

### The two inverse laws

**R15 · `intro x hx`** on `Set.LeftInvOn g f A` changes the **context and the goal**:
`Set.LeftInvOn g f A` is `∀ ⦃x⦄, x ∈ A → g (f x) = x`. `Set.RightInvOn g f B` unfolds to
`Set.LeftInvOn f g B`, i.e. `∀ ⦃y⦄, y ∈ B → f (g y) = y`; `intro` works the same. Placeholders:
`{α β : Type} (f : α → β) (g : β → α) (A : Set α)`.

| Before | After |
|---|---|
| `⊢ Set.LeftInvOn g f A` | `x : α, hx : x ∈ A ⊢ g (f x) = x` |

**R16 · `funext i`** changes the **goal and the context**: an equation of functions (configurations) becomes
an equation of values at a fresh `i`. Placeholders: `{α β : Type} (F G : α → β)`.

| Before | After |
|---|---|
| `⊢ F = G` | `i : α ⊢ F i = G i` |

**R17 · `Finset.mem_filter`** changes the **goal** (or, with `at`, the context): `a ∈ s.filter p ↔ a ∈ s ∧ p a`.
Placeholders: `{α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) (a : α)`.

| Before | After |
|---|---|
| `⊢ a ∈ Finset.filter p s` | `⊢ a ∈ s ∧ p a` |

**R18 · `Bool.decide_eq_true`** changes the **goal**: `decide (b = true) = b` for `b : Bool`. After
`funext i; simp` in the left inverse law, `simp` uses R17, R8, R18 to turn
`decide (i ∈ {j | σ j = true})` into `σ i`. Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `⊢ P (decide (b = true))` | `⊢ P b` |

**R19 · `ext i`** on finsets (lemma `Finset.ext`) changes the **goal and the context**: two finsets are equal
when they have the same members. Placeholders: `{α : Type} (s t : Finset α)`. In the right inverse law,
`simp` then closes the goal with R13, R11, R14.

| Before | After |
|---|---|
| `⊢ s = t` | `i : α ⊢ i ∈ s ↔ i ∈ t` |

### Worked combination W1 (not the exercise's objects)

Flipping every spin, `σ ↦ fun i => !σ i`, is its own inverse and swaps "`σ 0 = true`" and
"`σ 0 = false`". After R4 the four goals are:

```lean-goal
⊢ Set.MapsTo (fun σ i => !σ i) ↑{σ | σ 0 = true} ↑{σ | σ 0 = false}
⊢ Set.MapsTo (fun σ i => !σ i) ↑{σ | σ 0 = false} ↑{σ | σ 0 = true}
⊢ Set.LeftInvOn (fun σ i => !σ i) (fun σ i => !σ i) ↑{σ | σ 0 = true}
⊢ Set.RightInvOn (fun σ i => !σ i) (fun σ i => !σ i) ↑{σ | σ 0 = false}
```

Each `MapsTo` goal: R5, then R6–R8 at the hypothesis, then `simp [hσ]`. Each inverse law: R15, R16, `simp`.

---

## Part 2 · `Z_from_dos`

Statement: `∑ σ : Fin N → Bool, rexp (-b * (ε * ↑(nUp σ))) = ∑ m ∈ range (N + 1), ↑(N.choose m) * rexp (-b * (ε * ↑m))`.
Idea: group the `2^N` configurations by `nUp σ ∈ {0, …, N}`. On the fibre `nUp σ = m` the summand is the
constant `e^{-b ε m}`, and the fibre has `C(N, m)` elements by Part 1.

### Regrouping the sum

**R20 · `rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := t)]`** changes the **goal and the goal list**.
The lemma is `(∀ i ∈ s, g i ∈ t) → ∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`; used right to left,
it splits a sum over `s` into a sum over the values `j ∈ t` of `g` of the sum over the fibre `g i = j`.
`rw` cannot guess `g` and `t` from the goal, so name them. The hypothesis becomes a second goal
(`case h`). Placeholders: `{ι κ : Type} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℝ)`.
In the problem, `g = nUp` and `t = Finset.range (N + 1)`.

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ s, f x)` | `⊢ P (∑ j ∈ t, ∑ i ∈ s with g i = j, f i)`, `⊢ ∀ i ∈ s, g i ∈ t` |

**R21 · `refine Finset.sum_congr rfl fun y hy => ?_`** changes the **goal and the context**: two sums over the
same finset are equal if the summands agree on it. The lemma is
`s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`. Write `_` for `hy` if
you do not need it (it then shows as `x✝`). Placeholders: `{κ : Type} (t : Finset κ) (u v : κ → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ y ∈ t, u y = ∑ y ∈ t, v y` | `y : κ, hy : y ∈ t ⊢ u y = v y` |

**R22 · `rw [Finset.sum_congr rfl (g := fun _ => c)]`** changes the **goal and the goal list**: the same
lemma used to replace the summand by a constant `c` of your choice, leaving the proof that they agree as a
second goal. In the problem, `c = Real.exp (-b * (ε * m))`. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ s, f x)` | `⊢ P (∑ x ∈ s, c)`, `⊢ ∀ x ∈ s, f x = c` |

In the second goal, `intro σ hσ`, then R17 at `hσ` gives `hσ : σ ∈ Finset.univ ∧ nUp σ = m`, and
`rw [hσ.2]` closes it.

**R23 · `Finset.sum_const`** changes the **goal**: `∑ _x ∈ s, c = s.card • c`. Placeholders:
`{ι : Type} (s : Finset ι) (c : ℝ)`. In the problem `s.card` is then Part 1's left side:
`rw [degeneracy]`.

| Before | After |
|---|---|
| `⊢ P (∑ _x ∈ s, c)` | `⊢ P (s.card • c)` |

**R24 · `nsmul_eq_mul`** changes the **goal**: `n • a = ↑n * a`. After it both sides are the same, and `rw`
closes the goal by `rfl`. Placeholders: `(n : ℕ) (a : ℝ)` (any semiring in place of `ℝ`).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

### The side goal `nUp σ ∈ range (N + 1)`

After `intro σ _`, R25, R26 and unfolding `nUp` (all in one `simp only`), the goal is
`{i | σ i = true}.card ≤ N`: at most `N` sites are excited.

**R25 · `Finset.mem_range`** changes the **goal**: `k ∈ range n ↔ k < n`. Placeholders: `(k n : ℕ)`.

| Before | After |
|---|---|
| `⊢ k ∈ Finset.range n` | `⊢ k < n` |

**R26 · `Nat.lt_succ_iff`** changes the **goal**: `k < n.succ ↔ k ≤ n`; `n.succ` and `n + 1` are the same
for `rw` and `simp`. Placeholders: `(k n : ℕ)`.

| Before | After |
|---|---|
| `⊢ k < n + 1` | `⊢ k ≤ n` |

**R27 · `Finset.card_le_univ`** is a term: `s.card ≤ Fintype.card α` for every `s : Finset α`
(`[Fintype α]`). Use it as the first half of R28.

**R28 · `refine hab.trans ?_`** changes the **goal**: `hab.trans` is `le_trans hab : b ≤ c → a ≤ c`, so the
goal becomes the second half. With `hab = Finset.card_le_univ _` the rest is
`Fintype.card (Fin N) ≤ N`, which `simp` closes with R3. Placeholders: `(a b c : ℕ) (hab : a ≤ b)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

### Worked combination W2 (not the exercise's objects)

Grouping `x ∈ range 4` by parity, with `g = (· % 2)` and `t = range 2`. After R20 the goals are:

```lean-goal
⊢ ∑ j ∈ Finset.range 2, ∑ i ∈ Finset.range 4 with i % 2 = j, c (i % 2) = ∑ r ∈ Finset.range 2, ↑{x ∈ Finset.range 4 | x % 2 = r}.card * c r
⊢ ∀ i ∈ Finset.range 4, i % 2 ∈ Finset.range 2
```

Then R21, R22 with `c := c r`, R23, R24 on the first; R17 and `rw [hx.2]` on the constant-summand side goal;
R25 and `Nat.mod_lt` on the maps-to goal.

---

## Traps

- Don't rewrite `N` into `Fintype.card (Fin N)` everywhere: `rw` also rewrites the `N` inside the type
  `Fin N`, and the goal stops making sense. Go the other way: rewrite `N.choose m` into
  `(powersetCard m univ).card` with a `have` proved by `simp [Finset.card_powersetCard]` (R1–R3).
- `{σ | nUp σ = m}` in a `.card` or a `∑` is a **finset** (a filter of `univ`), printed in set-builder
  notation. `↑{σ | …}` is its coercion to a `Set`. Set lemmas such as `Set.mem_setOf_eq` apply only after
  `Finset.coe_filter` (R6); finset lemmas such as `Finset.mem_filter` (R17) apply to the un-coerced finset.
- The goals of R4 contain β-redexes like `(fun σ => {i | σ i = true}) σ ∈ …`. `simp` reduces them; `rw`
  may fail to find a pattern inside them.
- `rw [← Finset.sum_fiberwise_of_maps_to]` without `(g := …) (t := …)` fails: the right-hand side
  `∑ i ∈ s, f i` does not mention `g` or `t`. The same holds for `rw [Finset.sum_congr rfl]`: give `g`.
- The four goals of R4 come in the order `MapsTo i`, `MapsTo j`, `LeftInvOn`, `RightInvOn`. Use `·` to
  work on each in turn.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `N.choose m` as a card | `have hc : N.choose m = (Finset.powersetCard m Finset.univ).card := by simp [Finset.card_powersetCard]` | R1–R3 |
| `s.card = t.card` by a bijection | `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_` | R4 |
| open `MapsTo` / `LeftInvOn` / `RightInvOn` | `intro x hx` | R5, R15 |
| `x ∈ ↑(s.filter p)` → `p x` | `simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx` | R6–R8 |
| `s ∈ ↑(powersetCard n t)` → `s ⊆ t ∧ s.card = n` | `simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs` | R9, R10 |
| close from a hypothesis after simplifying | `simpa [lemmas, nUp] using h` | R12 |
| `decide p = true` → `p`, `decide (b = true)` → `b` | `simp` | R13, R18 |
| `{x ∈ univ \| x ∈ s}` → `s` | `simp` | R11, R14 |
| equal configurations / finsets | `funext i` / `ext i` | R16, R19 |
| `a ∈ s.filter p` | `Finset.mem_filter` | R17 |
| regroup `∑ x ∈ s, f x` by `g` | `rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := t)]` | R20 |
| compare summands | `refine Finset.sum_congr rfl fun y _ => ?_` | R21 |
| make the summand a constant `c` | `rw [Finset.sum_congr rfl (g := fun _ => c)]` | R22 |
| `∑ _ ∈ s, c` → `↑s.card * c` | `rw [Finset.sum_const, nsmul_eq_mul]` | R23, R24 |
| `k ∈ range (n + 1)` → `k ≤ n` | `simp only [Finset.mem_range, Nat.lt_succ_iff]` | R25, R26 |
| `s.card ≤ N` for `s : Finset (Fin N)` | `exact (Finset.card_le_univ _).trans (by simp)` | R27, R28, R3 |
| see the state | infoview | |
