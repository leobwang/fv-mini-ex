# H040 · Schröder–Bernstein: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `theorem`, `intro`, `exact`, `apply`, `have`,
`rw`, `simp`, `rcases`/`obtain`, `∃`/`∧`/`∨`/`¬`, anonymous constructors `⟨_, _⟩`. **New here:**
Mathlib's sets (`Set α`, `∈`, `⊆`, complement `ᶜ`, image `''`, intersection of a family `⋂₀`,
set-builder `{x | …}`), `IsEmpty`/`Nonempty`, `Function.Injective`/`Surjective`/`Bijective`, the
choice inverse `Function.invFun`, `classical` and `if … then … else …` on a `Prop`, and the tactics
`let`, `set`, `by_cases`, `▸`.

**The maths.** Given injections `f : α → β`, `g : β → α`, let `F S = (g '' (f '' S)ᶜ)ᶜ` for `S ⊆ α`
(`f '' S` is the image of `S` under `f`, `ᶜ` the complement). `F` is monotone (`S ⊆ T → F S ⊆ F T`:
two complements reverse `⊆` twice). Its least fixed point `A = ⋂₀ {S | F S ⊆ S}` (Knaster–Tarski,
milestone `lfp_fixed`) satisfies `F A = A`, i.e. `Aᶜ = g '' (f '' A)ᶜ`: every `x ∉ A` is `g y` for a
(unique, `g` injective) `y ∉ f '' A`. Define `h x = f x` on `A` and `h x = g⁻¹ x` off `A`:

```
      α                        β
   ┌──────┐   f (bijective)   ┌───────────┐
   │  A   │ ────────────────▶ │  f '' A   │
   ├──────┤                   ├───────────┤
   │  Aᶜ  │ ◀──────────────── │ (f '' A)ᶜ │
   └──────┘   g (bijective)   └───────────┘
```

`h` is injective: two points of `A` use `hf`; two points off `A` use `g (g⁻¹ x) = x`; a mixed pair
would put `g⁻¹ x ∉ f '' A` equal to some `f x' ∈ f '' A`. `h` is surjective: `y ∈ f '' A` is `f x` with
`x ∈ A`; otherwise `g y ∉ A` and `h (g y) = g⁻¹ (g y) = y`. If `β` is empty, so is `α`, and `f` itself
is a bijection (this case is separate only because `invFun g` needs `Nonempty β`).

## How to read an entry

Each entry is one tactic or one lemma used with `apply`/`rw`/`simp`/`exact`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders: `{α β : Type}` any types; `(s t u : Set α)` sets of
  elements of `α`; `(S : Set (Set α))` a family of sets; `(p G : Prop)` propositions. A bracket
  `[Nonempty β]` or `[Decidable p]` is a requirement (a *type class*) explained in the entry.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Set α` | a set of elements of `α`; really a predicate `α → Prop` |
| `x ∈ s`, `x ∉ s` | membership, and `¬ (x ∈ s)` |
| `s ⊆ t` | `∀ x, x ∈ s → x ∈ t` |
| `sᶜ` | complement: `x ∈ sᶜ` is by definition `x ∉ s` |
| `f '' s` | image `{f x \| x ∈ s}`: `y ∈ f '' s` is `∃ x, x ∈ s ∧ f x = y` |
| `{x \| Q x}` | set-builder: `a ∈ {x \| Q x}` is by definition `Q a` (R2) |
| `Set (Set α)`, `⋂₀ S` | a family of sets, and its intersection: `x ∈ ⋂₀ S` iff `x` is in every member |
| `∀ x ∈ s, P x`, `∀ x ∉ s, P x` | bounded quantifiers: `∀ x, x ∈ s → P x` and `∀ x, x ∉ s → P x`; `intro x hx` takes both binders |
| `Mono F` | this file's definition `∀ A B, A ⊆ B → F A ⊆ F B`: `hF A B hAB : F A ⊆ F B`, and `intro A B hAB` proves it |
| `lfp F` | this file's definition `⋂₀ {A \| F A ⊆ A}`; `apply` and `exact` unfold it, so R1 and R3 apply to `lfp F` directly |
| `IsEmpty β`, `Nonempty β` | `β` has no element; `β` has at least one (`isEmpty_or_nonempty β`, R7) |
| `Injective k` | `∀ a₁ a₂, k a₁ = k a₂ → a₁ = a₂` (R20) |
| `Surjective k` | `∀ b, ∃ a, k a = b` (R27) |
| `Bijective k` | `Injective k ∧ Surjective k` (R10) |
| `invFun g` | `Function.invFun g : α → β`, a preimage of each point chosen by the axiom of choice; needs `Nonempty β` (R19) |
| `LeftInverse u g` | `∀ y, u (g y) = y` |
| `if p then a else b` | `ite p a b`; needs an instance `Decidable p`, which `classical` provides (R6) |
| `inst✝ : Decidable p` | an anonymous instance hypothesis |
| `F : Set α → Set α := fun S => …` | a `let` variable: `F` with its value (R12); after some steps the value prints as `:= ⋯` |
| `A : Set α := lfp F`, `hA : A = lfp F` | what `set` leaves (R15) |
| `h : (fun x => if x ∈ A then f x else invFun g x) x1 = …` | the map applied to `x1`, not yet β-reduced; `simp only` reduces it |
| `case inl`, `case inr` | the two branches of an `∨` split (R7) |
| `case pos`, `case neg` | the two branches of `by_cases` (R21) |
| `case a`, `case refine_1` | goals created by `apply` / `refine` |

---

## Part 1 · `lfp_fixed` (milestone, prove it first)

Statement: for a monotone `F : Set α → Set α` (`Mono F`), `lfp F = ⋂₀ {A | F A ⊆ A}` is a fixed
point: `F (lfp F) = lfp F`. Proof: `lfp F ⊆ A` whenever `F A ⊆ A` (call it `least`); then
`F (lfp F) ⊆ F A ⊆ A` for every such `A`, so `F (lfp F) ⊆ lfp F`; applying `least` to `F (lfp F)`
(pre-fixed by monotonicity) gives the other inclusion. `schroeder_bernstein` uses it once, for `hfix`.

**R1 · `apply Set.sInter_subset_of_mem`** changes the **goal**. The lemma is
`Set.sInter_subset_of_mem : t ∈ S → ⋂₀ S ⊆ t`. Placeholders: `{α : Type} (S : Set (Set α)) (t : Set α)`.
For `S = {A | F A ⊆ A}`, the membership `t ∈ S` is `F t ⊆ t` by definition (R2), so
`Set.sInter_subset_of_mem hA` accepts `hA : F A ⊆ A` directly.

| Before | After |
|---|---|
| `⊢ ⋂₀ S ⊆ t` | `⊢ t ∈ S` |

**R2 · `rw [Set.mem_setOf_eq]`** changes the **goal**: `a ∈ {x | Q x}` becomes `Q a`. The two are equal by
definition, so you rarely need the rewrite; it is there to make the infoview show the unfolded form.
Placeholders: `{α : Type} (Q : α → Prop) (a : α)`.

Before, then after (shown as a block because the goal contains `|`):

```lean-goal
⊢ a ∈ {x | Q x}
⊢ Q a
```

**R3 · `apply Set.subset_sInter`** changes the **goal**. The lemma is
`Set.subset_sInter : (∀ t' ∈ S, s ⊆ t') → s ⊆ ⋂₀ S`. Follow it with `intro t ht`. Placeholders:
`{α : Type} (S : Set (Set α)) (s : Set α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ ⋂₀ S` | `⊢ ∀ t' ∈ S, s ⊆ t'` |

**R4 · `refine h₁.trans ?_`** changes the **goal**. `HasSubset.Subset.trans : s ⊆ t → t ⊆ u → s ⊆ u`,
written with dot notation `h₁.trans h₂`. Placeholders: `{α : Type} (s t u : Set α) (h₁ : s ⊆ t)`.
As a term: `(hF _ _ (least A hA)).trans hA`.

| Before | After |
|---|---|
| `⊢ s ⊆ u` | `⊢ t ⊆ u` |

**R5 · `apply subset_antisymm`** changes the **goal list**. The lemma is
`subset_antisymm : s ⊆ t → t ⊆ s → s = t`. Placeholders: `{α : Type} (s t : Set α)`. As a term:
`subset_antisymm h₁ h₂`.

| Before | After |
|---|---|
| `⊢ s = t` | `⊢ s ⊆ t`, `⊢ t ⊆ s` |

**W2** chains R5, R1, R2, R3 on `⋂₀ {A | s ⊆ A} = s`.

---

## Part 2 · `schroeder_bernstein`

Statement: injective `f : α → β` and `g : β → α` give some bijective `h : α → β`.

### Setting up: decidability and the empty case

**R6 · `classical`** changes neither goal nor context visibly: from here on every `Prop` has a
`Decidable` instance (by the axiom of choice), so `if x ∈ A then … else …` elaborates for any set `A`.
Without it Lean reports "failed to synthesize Decidable (x ∈ A)". Put it first.
Placeholders: `{α β : Type} (A : Set α) (u v : α → β)`.

| Before | After |
|---|---|
| `⊢ ∃ k, ∀ x ∈ A, k x = u x` | `⊢ ∃ k, ∀ x ∈ A, k x = u x` |

**R7 · `rcases isEmpty_or_nonempty β with hβ | hβ`** changes the **goal list and the context**:
`isEmpty_or_nonempty β : IsEmpty β ∨ Nonempty β`, one goal per side. Placeholders: `{β : Type} (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hβ : IsEmpty β ⊢ G`, `hβ : Nonempty β ⊢ G` |

**R8 · `refine ⟨fun a => ?_⟩`** changes the **goal and the context**. `IsEmpty α` is a structure with
one field, a function `α → False`; the anonymous constructor builds it. As a term:
`have : IsEmpty α := ⟨fun a => hβ.false (f a)⟩`. Placeholders: `{α β : Type} (f : α → β) (hβ : IsEmpty β)`.

| Before | After |
|---|---|
| `⊢ IsEmpty α` | `a : α ⊢ False` |

**R9 · `exact hβ.false b`** **closes** `False`. `IsEmpty.false : IsEmpty β → β → False`. Placeholders:
`{β : Type} (hβ : IsEmpty β) (b : β)`.

| Before | After |
|---|---|
| `hβ : IsEmpty β, b : β ⊢ False` | no goals |

**R10 · `refine ⟨k, ?_, ?_⟩`** changes the **goal list**: `Bijective k` is by definition
`Injective k ∧ Surjective k`, so one pattern gives the witness and splits the `∧`. Placeholders:
`{α β : Type} (k : α → β)`. In the empty case write the whole term `⟨f, hf, fun b => …⟩`.

| Before | After |
|---|---|
| `⊢ ∃ k', Bijective k'` | `⊢ Injective k`, `⊢ Surjective k` |

**R11 · `exact hβ.elim b`** **closes** any goal about an element of an empty type:
`IsEmpty.elim : IsEmpty β → ∀ b : β, Q b`. Surjectivity onto an empty `β` is `fun b => hβ.elim b`.
Placeholders: `{β : Type} (hβ : IsEmpty β) (b : β) (Q : β → Prop)`.

| Before | After |
|---|---|
| `⊢ Q b` | no goals |

### The map `F` and its fixed point

**R12 · `let F : Set α → Set α := fun S => …`** changes the **context**: it adds `F` together with its
value. Unlike `have`, the value stays visible, and `apply`, `exact` and `rw` see through `F A` to its body.
Placeholders: `{α : Type} (P : (Set α → Set α) → Prop)`.

| Before | After |
|---|---|
| `⊢ P fun S => Sᶜ` | `F : Set α → Set α := fun S => Sᶜ ⊢ P fun S => Sᶜ` |

**R13 · `apply Set.compl_subset_compl.mpr`** changes the **goal**. The lemma is
`Set.compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s` (complement reverses inclusion); `.mpr` is its `←` direction.
Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ sᶜ ⊆ tᶜ` | `⊢ t ⊆ s` |

**R14 · `apply Set.image_mono`** changes the **goal**. The lemma is `Set.image_mono : s ⊆ t → g '' s ⊆ g '' t`.
Placeholders: `{α β : Type} (g : α → β) (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ g '' s ⊆ g '' t` | `⊢ s ⊆ t` |

**W1** chains R13 → R14 → R13 on `(g '' tᶜ)ᶜ ⊆ (g '' sᶜ)ᶜ`; the goal after each step:

```lean-goal
⊢ (g '' tᶜ)ᶜ ⊆ (g '' sᶜ)ᶜ
⊢ g '' sᶜ ⊆ g '' tᶜ
⊢ sᶜ ⊆ tᶜ
⊢ t ⊆ s
```

`hF : Mono F` needs one more round (`F` has two images and two complements): `intro A B hAB` leaves
`⊢ F A ⊆ F B` with `F` still folded; `apply` sees through the `let`, so R13, R14, R13, R14 apply as they
are, and the goal after the first R13 is `g '' (f '' B)ᶜ ⊆ g '' (f '' A)ᶜ`.

**R15 · `set A := e with hA`** changes the **context and the goal**: it adds `A := e` and `hA : A = e`, and
replaces every `e` in the goal and the hypotheses by `A`. Use it on `lfp F` so the infoview stays readable.
Placeholders: `{α : Type} (e : Set α) (P : Set α → Prop)`.

| Before | After |
|---|---|
| `h : P e ⊢ P e` | `A : Set α := e, h : P A, hA : A = e ⊢ P A` |

**R16 · `rw [← compl_compl s]`** changes the **goal**. The lemma is `compl_compl s : sᶜᶜ = s`; right to left
it wraps every `s` in two complements. For `hcompl : Aᶜ = g '' (f '' A)ᶜ`, rewrite the right side as
`((g '' (f '' A)ᶜ)ᶜ)ᶜ`, then `rw [hfix]` turns the inner part into `A`. Placeholders:
`{α : Type} (s : Set α) (P : Set α → Prop)`.

| Before | After |
|---|---|
| `⊢ P s` | `⊢ P sᶜᶜ` |

### Injectivity

The witness is `fun x => if x ∈ A then f x else invFun g x`. First prove, for points off `A`,
`key : ∀ x, x ∉ A → g (invFun g x) = x ∧ invFun g x ∉ f '' A`, with R17, R18, R19.

**R17 · `have hxt : x ∈ t := e ▸ hx`** changes the **context**. `e ▸ hx` rewrites with the equation
`e : sᶜ = t` (in whichever direction makes the types match) until the type of `hx` becomes the stated type.
`hx : x ∉ s` counts as `x ∈ sᶜ`, since they are equal by definition. With `e := hcompl`, this turns
`hx : x ∉ A` into `x ∈ g '' (f '' A)ᶜ`. Placeholders: `{α : Type} (s t : Set α) (e : sᶜ = t) (x : α) (hx : x ∉ s)`.

| Before | After |
|---|---|
| `hx : x ∉ s ⊢ G` | `hxt : x ∈ t ⊢ G` |

**R18 · `obtain ⟨y, hy, rfl⟩ := hx`** changes the **context and the goal**. `x ∈ g '' s` is
`∃ y, y ∈ s ∧ g y = x`; the pattern names `y` and `hy`, and `rfl` replaces `x` by `g y` everywhere.
Placeholders: `{α β : Type} (g : β → α) (s : Set β) (x : α)`.

| Before | After |
|---|---|
| `hx : x ∈ g '' s ⊢ P x` | `y : β, hy : y ∈ s ⊢ P (g y)` |

**R19 · `rw [leftInverse_invFun hg y]`** changes the **goal**. `Function.invFun g` needs `[Nonempty β]`
(that is why the empty case is split off). `Function.leftInverse_invFun : Injective g → LeftInverse (invFun g) g`,
so `leftInverse_invFun hg y : invFun g (g y) = y`. Placeholders:
`{α β : Type} [Nonempty β] (g : β → α) (hg : Injective g) (y : β)`. In `key`, after R18 the goal is
`g (invFun g (g y)) = g y ∧ invFun g (g y) ∉ f '' A` and `hy : y ∈ (f '' A)ᶜ`; after R19, `⟨rfl, hy⟩` closes it.

| Before | After |
|---|---|
| `⊢ P (invFun g (g y))` | `⊢ P y` |

**W3** chains R18 → R19: `∀ x ∈ g '' s, invFun g x ∈ s`.

**R20 · `intro a₁ a₂ h`** on `Injective k` changes the **goal and the context**: `Injective k` is by
definition `∀ a₁ a₂, k a₁ = k a₂ → a₁ = a₂`, and `intro` unfolds it. In the exercise `h` shows the
un-reduced `(fun x => …) x1 = (fun x => …) x2`. Placeholders: `{α β : Type} (k : α → β)`.

| Before | After |
|---|---|
| `⊢ Injective k` | `a₁ a₂ : α, h : k a₁ = k a₂ ⊢ a₁ = a₂` |

**R21 · `by_cases hp : p`** changes the **goal list and the context**: one goal with `hp : p`, one with
`hp : ¬p` (printed `hp : x ∉ A` when `p` is `x ∈ A`). `by_cases h1 : x1 ∈ A <;> by_cases h2 : x2 ∈ A` gives
all four cases. Placeholders: `(p G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hp : p ⊢ G`, `hp : ¬p ⊢ G` |

**R22 · `simp only [hp, if_true] at h`** with `hp : p` changes the **context**: `simp only [hp]` rewrites `p`
to `True`, and `if_true : (if True then a else b) = a`. It also β-reduces `(fun x => …) x1`. Placeholders:
`{β : Type} (p : Prop) [Decidable p] (a b : β) (P : β → Prop)`.

| Before | After |
|---|---|
| `h : P (if p then a else b) ⊢ P a` | `h : P a ⊢ P a` |

**R23 · `simp only [hp, if_false] at h`** with `hp : ¬p` changes the **context** the same way, with
`if_false : (if False then a else b) = b`. One call `simp only [h1, h2, if_true, if_false] at h` serves all four
cases. Placeholders: as R22.

| Before | After |
|---|---|
| `h : P (if p then a else b) ⊢ P b` | `h : P b ⊢ P b` |

**R24 · `apply hf`** with `hf : Injective f` changes the **goal**: to show `a₁ = a₂`, show `f a₁ = f a₂`.
As a term: `hf h`. Placeholders: `{α β : Type} (f : α → β) (a₁ a₂ : α)`.

| Before | After |
|---|---|
| `⊢ a₁ = a₂` | `⊢ f a₁ = f a₂` |

**R25 · `refine ⟨y, ?_, rfl⟩`** changes the **goal**: membership in an image is built from a preimage,
a proof it lies in the set, and an equation. In the mixed case, `⟨x1, h1, h⟩ : invFun g x2 ∈ f '' A` from
`h1 : x1 ∈ A` and `h : f x1 = invFun g x2`. Placeholders: `{α β : Type} (g : β → α) (s : Set β) (y : β)`.

| Before | After |
|---|---|
| `⊢ g y ∈ g '' s` | `⊢ y ∈ s` |

**R26 · `apply absurd ha`** changes the **goal**: `absurd : a → ¬a → b`, so from `ha : A` it remains to
refute `A`. As a term: `absurd ⟨x1, h1, h⟩ (key x2 h2).2`. Placeholders: `(A G : Prop) (ha : A)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ ¬A` |

In the case `x1 ∉ A`, `x2 ∉ A`, `h : invFun g x1 = invFun g x2`: rewrite `x1` and `x2` backwards with
`(key x1 h1).1` and `(key x2 h2).1` (each `g (invFun g x) = x`), then `rw [h]`.

### Surjectivity

**R27 · `intro b`** on `Surjective k` changes the **goal and the context**: `Surjective k` is by definition
`∀ b, ∃ a, k a = b`. Placeholders: `{α β : Type} (k : α → β)`.

| Before | After |
|---|---|
| `⊢ Surjective k` | `b : β ⊢ ∃ a, k a = b` |

Then `by_cases hy : y ∈ f '' A` (R21). If yes, R18 gives `y = f x` with `hx : x ∈ A`, and
`⟨x, by simp [hx]⟩` works: `simp [hx]` uses `if_pos`. If not, the witness is `g y`.

**R28 · `rw [← Set.mem_compl_iff]`** changes the **goal**. The lemma is `Set.mem_compl_iff : x ∈ sᶜ ↔ x ∉ s`;
right to left it exposes `sᶜ`, so `rw [hcompl]` can replace `Aᶜ`. Then R25 proves `g y ∈ g '' (f '' A)ᶜ`.
Placeholders: `{α : Type} (s : Set α) (x : α)`.

| Before | After |
|---|---|
| `⊢ x ∉ s` | `⊢ x ∈ sᶜ` |

With `hgy : g y ∉ A`, `simp [hgy, leftInverse_invFun hg y]` evaluates `h (g y)` to `y` (R23, R19).

**W4** evaluates a piecewise function case by case (R21, then R22/R23 on the goal).

---

## Traps

- `if x ∈ A then …` needs `Decidable (x ∈ A)`. Without `classical` (R6) the witness does not elaborate.
- `invFun g` needs `Nonempty β`. In the branch `hβ : Nonempty β` of R7 it is found automatically; in the
  empty branch there is no inverse, so finish that branch with `f` itself (R8–R11).
- `x ∉ A` and `x ∈ Aᶜ` are equal by definition, but `rw [hcompl]` needs the text `Aᶜ`: first
  `rw [← Set.mem_compl_iff]` (R28), or move a hypothesis with `hcompl ▸ hx` (R17).
- After `rw [← compl_compl X]` every `X` gets wrapped, so give the argument `X` explicitly (R16).
- `t1 ; t2` runs `t2` on the first goal only. After the double `by_cases`, use `<;>`.
- The milestone `lfp` is the exercise's own definition, not Mathlib's `OrderHom.lfp`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `⋂₀ S ⊆ t` from `t ∈ S` | `Set.sInter_subset_of_mem ht` | R1 |
| unfold `a ∈ {x \| Q x}` | `rw [Set.mem_setOf_eq]` (or just use `Q a`) | R2 |
| `s ⊆ ⋂₀ S` | `apply Set.subset_sInter; intro t ht` | R3 |
| chain `s ⊆ t ⊆ u` | `h₁.trans h₂` | R4 |
| `s = t` from two inclusions | `subset_antisymm h₁ h₂` | R5 |
| allow `if p then …` on any `p` | `classical` | R6 |
| empty or not | `rcases isEmpty_or_nonempty β with hβ \| hβ` | R7 |
| build `IsEmpty α` | `⟨fun a => hβ.false (f a)⟩` | R8, R9 |
| `∃ k, Bijective k` | `refine ⟨k, ?_, ?_⟩` | R10 |
| anything about `b : β`, `β` empty | `hβ.elim b` | R11 |
| name a map with its value | `let F : Set α → Set α := fun S => …` | R12 |
| `sᶜ ⊆ tᶜ` | `apply Set.compl_subset_compl.mpr` | R13 |
| `g '' s ⊆ g '' t` | `apply Set.image_mono` | R14 |
| abbreviate `lfp F` | `set A := lfp F with hA` | R15 |
| `s` → `sᶜᶜ` | `rw [← compl_compl s]` | R16 |
| move a hypothesis along `e : a = b` | `e ▸ hx` | R17 |
| unpack `x ∈ g '' s` | `obtain ⟨y, hy, rfl⟩ := hx` | R18 |
| `invFun g (g y) = y` | `leftInverse_invFun hg y` | R19 |
| prove `Injective k` | `intro a₁ a₂ h` | R20 |
| case split on `x ∈ A` | `by_cases h1 : x ∈ A` | R21 |
| evaluate `if` in `h` | `simp only [h1, h2, if_true, if_false] at h` | R22, R23 |
| use `hf : Injective f` | `hf h` | R24 |
| prove `g y ∈ g '' s` | `⟨y, hy, rfl⟩` | R25 |
| contradiction `a`, `¬a` | `absurd ha hna` | R26 |
| prove `Surjective k` | `intro b` | R27 |
| `x ∉ s` → `x ∈ sᶜ` | `rw [← Set.mem_compl_iff]` | R28 |
| evaluate `if` in the goal | `simp [hx]` | R22, R23 |
