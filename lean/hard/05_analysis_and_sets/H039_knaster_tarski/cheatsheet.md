# H039 · Knaster–Tarski: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `def`, `intro`, `apply`, `exact`, `refine`
with `?_`, `have`, `rw`, `.`-notation on hypotheses (`h.trans`). **New here** (Mathlib): sets `Set α`,
families of sets `Set (Set α)`, set-builder notation `{A | p A}`, the inclusion `⊆`, the intersection
`⋂₀` and union `⋃₀` of a family, and the order `≤` on sets.

The math. Let $f : \mathcal P(\alpha) \to \mathcal P(\alpha)$ be monotone ($A \subseteq B \Rightarrow
f A \subseteq f B$). Call $A$ *closed* if $f A \subseteq A$ and *consistent* if $A \subseteq f A$.
Set $\mathrm{lfp} = \bigcap\{A \mid f A \subseteq A\}$ and $\mathrm{gfp} = \bigcup\{A \mid A \subseteq f A\}$.

1. *Least:* a closed $A$ is one of the sets intersected, so $\mathrm{lfp} \subseteq A$.
2. *Fixed:* for every closed $A$, $\mathrm{lfp} \subseteq A$ gives $f(\mathrm{lfp}) \subseteq f A \subseteq A$;
   so $f(\mathrm{lfp})$ is below every closed set, hence $f(\mathrm{lfp}) \subseteq \mathrm{lfp}$. Applying
   $f$ to that inclusion shows $f(\mathrm{lfp})$ is closed, so by 1, $\mathrm{lfp} \subseteq f(\mathrm{lfp})$.
3. *Greatest* and *fixed* for $\mathrm{gfp}$: the same with $\bigcup$, $\supseteq$ and "consistent".
4. $\mathrm{gfp}$ is a fixed point, so in particular closed; by 1, $\mathrm{lfp} \subseteq \mathrm{gfp}$.

## How to read an entry

Each entry is one tactic or one lemma used with `apply`/`rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Set α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `a b c t : Set α` are sets of
  elements of `α`; `S : Set (Set α)` is a family of sets; `g : Set α → Set α` plays the role of `f`.
  No type-class brackets occur in this problem.
- "closes" means the step leaves no goal; then only the Before state is shown.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Set α` | the type of sets of elements of `α` (a set is a predicate `α → Prop`) |
| `Set (Set α)` | a family of sets: a set whose elements are sets |
| `A ⊆ B` | every element of `A` is in `B`. Mathlib's order `A ≤ B` on sets is the same thing and is printed as `⊆` |
| `A ∈ S` | the set `A` is a member of the family `S` |
| `{A \| p A}` | `setOf p`: the family of sets `A` with property `p A`. `X ∈ {A \| p A}` is `p X` by definition (R3) |
| `⋂₀ S` | `Set.sInter S`: the intersection of all sets in `S` (elements in every member) |
| `⋃₀ S` | `Set.sUnion S`: the union of all sets in `S` (elements in some member) |
| `∀ t' ∈ S, Q t'` | `∀ t', t' ∈ S → Q t'`: `intro` needs two names (R6) |
| `hf : Mono f` | the problem's own `def`; it unfolds to `∀ A B, A ⊆ B → f A ⊆ f B`, so `hf _ _ h` works (R8) |
| `lfp f`, `gfp f` | the problem's own `def`s; Lean keeps the names in the goal until you `unfold` them (R1) |
| `case a` | the name `apply` gives to a goal it creates from a lemma argument `a` |

---

## Part 1 · `lfp_least`

Statement: if `f A ⊆ A` then `lfp f ⊆ A`. In words: the intersection of all closed sets is below each
closed set.

**R1 · `unfold D`** changes the **goal**: the defined name `D` is replaced by its body. Optional here:
`apply` and `exact` unfold `lfp`/`gfp` by themselves; `unfold lfp` only lets you see the `⋂₀`.
Placeholders: `{α : Type} (S : Set (Set α))`, with `def bigInter (S : Set (Set α)) : Set α := ⋂₀ S`.

| Before | After |
|---|---|
| `⊢ P (bigInter S)` | `⊢ P (⋂₀ S)` |

**R2 · `Set.sInter_subset_of_mem`** changes the **goal**. The lemma is `t ∈ S → ⋂₀ S ⊆ t`: a member of the
family contains the intersection. With `apply`, the goal becomes the membership. Placeholders:
`{α : Type} (S : Set (Set α)) (t : Set α)`. In term mode: `Set.sInter_subset_of_mem h`.

| Before | After |
|---|---|
| `⊢ ⋂₀ S ⊆ t` | `⊢ t ∈ S` |

**R3 · `rw [Set.mem_setOf_eq]`** changes the **goal**. The lemma is `(a ∈ {x | p x}) = p a`, where
`{x | p x}` is notation for `setOf p`. The two sides are equal by definition, so `exact h` with `h : p a`
closes the membership goal without this step; the rewrite only makes the goal readable.
`rw [Set.mem_setOf_eq] at hA` does the same to a hypothesis. Placeholders:
`{α : Type} (p : Set α → Prop) (a : Set α)`; in the exercise `p` is `fun X => f X ⊆ X`, printed `{A | f A ⊆ A}`.

| Before | After |
|---|---|
| `⊢ a ∈ setOf p` | `⊢ p a` |

---

## Part 2 · `lfp_fixed`

Statement: for monotone `f`, `f (lfp f) = lfp f`. Prove `h1 : f (lfp f) ⊆ lfp f` first (R5 → R6 → R8, R7),
then split the equation (R4); the second inclusion comes from `lfp_least` and monotonicity applied to `h1`.

**R4 · `apply subset_antisymm`** changes the **goal list**. The lemma is `a ⊆ b → b ⊆ a → a = b`: two sets
are equal when each is contained in the other. One goal becomes two. Placeholders:
`{α : Type} (a b : Set α)`. In term mode: `subset_antisymm h1 h2`.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ a ⊆ b`, `⊢ b ⊆ a` |

**R5 · `apply Set.subset_sInter`** changes the **goal**. The lemma is `(∀ t' ∈ S, t ⊆ t') → t ⊆ ⋂₀ S`:
to be below the intersection, be below every member. Placeholders: `{α : Type} (S : Set (Set α)) (t : Set α)`.
In `lfp_fixed` the family is `{A | f A ⊆ A}`, so the new goal reads `∀ t' ∈ {A | f A ⊆ A}, f (lfp f) ⊆ t'`.

| Before | After |
|---|---|
| `⊢ t ⊆ ⋂₀ S` | `⊢ ∀ t' ∈ S, t ⊆ t'` |

**R6 · `intro A hA`** changes the **context and the goal**. A bounded quantifier `∀ t' ∈ S, Q t'` is
`∀ t', t' ∈ S → Q t'`, so it takes two names: the set and the proof that it is in the family.
Placeholders: `{α : Type} (S : Set (Set α)) (b : Set α)`.

| Before | After |
|---|---|
| `⊢ ∀ t' ∈ S, b ⊆ t'` | `A : Set α, hA : A ∈ S ⊢ b ⊆ A` |

In `lfp_fixed`, `S` is `{A | f A ⊆ A}`, so `hA : A ∈ {A | f A ⊆ A}`. It is usable as `f A ⊆ A` directly (R3):
`exact hA`, `hA.trans`, `lfp_least f A hA`.

**R7 · `refine h1.trans ?_`** changes the **goal**. `HasSubset.Subset.trans` is `a ⊆ b → b ⊆ c → a ⊆ c`;
`h1.trans` fixes the first link, and the goal becomes the second. Placeholders: `{α : Type} (a b c : Set α)`,
`h1 : a ⊆ b`. In term mode: `h1.trans h2 : a ⊆ c`.

| Before | After |
|---|---|
| `h1 : a ⊆ b ⊢ a ⊆ c` | `h1 : a ⊆ b ⊢ b ⊆ c` |

**R8 · `apply hg`**, for a monotonicity hypothesis `hg : ∀ A B, A ⊆ B → g A ⊆ g B`, changes the **goal**:
to show `g a ⊆ g b`, show `a ⊆ b`. In term mode: `hg _ _ h : g a ⊆ g b` for `h : a ⊆ b` (the two `_` are
`a` and `b`, read off `h`). `hf : Mono f` works the same way because `Mono f` is a `def` that unfolds to this
`∀`. Placeholders: `{α : Type} (g : Set α → Set α) (a b : Set α)`.

| Before | After |
|---|---|
| `⊢ g a ⊆ g b` | `⊢ a ⊆ b` |

**W2 (R8, R7).** From `h1 : a ⊆ b` and `h2 : g b ⊆ c`, `refine (hg _ _ h1).trans ?_` leaves only the
second link:

```lean-goal
⊢ g a ⊆ c
⊢ g b ⊆ c
```

**W1 (R4, R2, R5).** A family `S` with a least member `b` (`hb : b ∈ S`, `hlow : ∀ t ∈ S, b ⊆ t`) has
`⋂₀ S = b`. `apply subset_antisymm` gives the two inclusions; the first is R2 with `hb`, the second R5 with
`hlow`:

```lean-goal
⊢ ⋂₀ S = b
⊢ ⋂₀ S ⊆ b
⊢ b ⊆ ⋂₀ S
```

---

## Part 3 · `gfp_greatest`

Statement: if `A ⊆ f A` then `A ⊆ gfp f`. The dual of Part 1, with the union.

**R9 · `apply Set.subset_sUnion_of_mem`** changes the **goal**. The lemma is `t ∈ S → t ⊆ ⋃₀ S`: a member of
the family is contained in the union. Placeholders: `{α : Type} (S : Set (Set α)) (t : Set α)`. In term mode:
`Set.subset_sUnion_of_mem h`.

| Before | After |
|---|---|
| `⊢ t ⊆ ⋃₀ S` | `⊢ t ∈ S` |

---

## Part 4 · `gfp_fixed`

Statement: for monotone `f`, `f (gfp f) = gfp f`. The dual of Part 2: prove `h1 : gfp f ⊆ f (gfp f)` first
(R10 → R6 → R7, R8), then R4; the other inclusion is `gfp_greatest` at `f (gfp f)`, whose hypothesis
`f (gfp f) ⊆ f (f (gfp f))` is monotonicity applied to `h1`.

**R10 · `apply Set.sUnion_subset`** changes the **goal**. The lemma is `(∀ t' ∈ S, t' ⊆ t) → ⋃₀ S ⊆ t`: the
union is below `t` when every member is. Placeholders: `{α : Type} (S : Set (Set α)) (t : Set α)`.
In `gfp_fixed` the new goal reads `∀ t' ∈ {A | A ⊆ f A}, t' ⊆ f (gfp f)`.

| Before | After |
|---|---|
| `⊢ ⋃₀ S ⊆ t` | `⊢ ∀ t' ∈ S, t' ⊆ t` |

**W3 (R10, R6, R3).** The union of all sets below `b` is below `b`:

```lean-goal
⊢ ⋃₀ {X | X ⊆ b} ⊆ b
⊢ ∀ t' ∈ {X | X ⊆ b}, t' ⊆ b
⊢ A ⊆ b
```

After `intro A hA`, `rw [Set.mem_setOf_eq] at hA` turns `hA : A ∈ {X | X ⊆ b}` into `hA : A ⊆ b`.

---

## Part 5 · `lfp_subset_gfp`

Statement: for monotone `f`, `lfp f ⊆ gfp f`. Use `lfp_least` at `A := gfp f`; its hypothesis
`f (gfp f) ⊆ gfp f` follows from the equation `gfp_fixed f hf`.

**R11 · `h.le`** (lemma `Eq.le : a = b → a ≤ b`) changes the **context** when used in `have`: an equation
becomes an inclusion, because on `Set α` the order `≤` is `⊆` (Lean prints it as `⊆`). `h.ge` gives the other
direction `b ⊆ a`. Placeholders: `{α : Type} (a b : Set α)`, `h : a = b`.

| Before | After `have h2 := h.le` |
|---|---|
| `h : a = b ⊢ a ⊆ b` | `h2 : a ⊆ b ⊢ a ⊆ b` |

**W4 (R11, R7, R9).** From `h : c = d` and `hd : d ∈ S`, one term closes `⊢ c ⊆ ⋃₀ S`:
`h.le.trans (Set.subset_sUnion_of_mem hd)`.

---

## Traps

- `hA : A ∈ {A | f A ⊆ A}` looks like a membership, but it *is* `f A ⊆ A`: pass it straight to `.trans`,
  `lfp_least` or `exact`. `rw [Set.mem_setOf_eq] at hA` only changes how it is printed (R3).
- `intro A` alone on `∀ t' ∈ S, …` leaves `A ∈ S → …` as the goal; give two names (R6).
- `lfp f` stays folded in the goal. You do not need `unfold lfp` for R2, R5, R9, R10; `apply` sees through it.
- The direction of the dual lemmas: `sInter_subset_of_mem`/`subset_sInter` (below the intersection) versus
  `subset_sUnion_of_mem`/`sUnion_subset` (above the union). Swapping them gives a unification error.
- In `lfp_fixed`, prove `h1 : f (lfp f) ⊆ lfp f` *before* `subset_antisymm`: the second inclusion needs `h1`
  again (monotonicity applied to it), and a `have` inside one branch is not visible in the other.
- `subset_antisymm h1 h2` proves `a = b` from `h1 : a ⊆ b` and `h2 : b ⊆ a`, in that order. For the goal
  `f (lfp f) = lfp f`, the first argument is `f (lfp f) ⊆ lfp f`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see a definition's body | `unfold lfp` | R1 |
| `⋂₀ S ⊆ t` from `t ∈ S` | `Set.sInter_subset_of_mem h` | R2 |
| `a ∈ {x \| p x}` ↔ `p a` | `exact h` (definitional) or `rw [Set.mem_setOf_eq]` | R3 |
| `a = b` from two inclusions | `subset_antisymm h1 h2` / `apply subset_antisymm` | R4 |
| `t ⊆ ⋂₀ S` | `apply Set.subset_sInter; intro A hA` | R5, R6 |
| chain `a ⊆ b ⊆ c` | `h1.trans h2` / `refine h1.trans ?_` | R7 |
| `g a ⊆ g b` from `a ⊆ b` | `hf _ _ h` / `apply hf` | R8 |
| `t ⊆ ⋃₀ S` from `t ∈ S` | `Set.subset_sUnion_of_mem h` | R9 |
| `⋃₀ S ⊆ t` | `apply Set.sUnion_subset; intro A hA` | R10, R6 |
| `a ⊆ b` from `a = b` | `h.le` (`h.ge` for `b ⊆ a`) | R11 |
| use an earlier theorem | `lfp_least f A hA`, `gfp_fixed f hf` | |
| see the state | infoview | |
