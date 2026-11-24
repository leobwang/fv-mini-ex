# M059 · The kernel of a homomorphism: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's groups (`Group`), monoid
homomorphisms `G →* H` and the lemmas `map_one`, `map_mul`, `map_inv`; sets `Set G` written
`{x | P x}`; `Subgroup G` as a structure you build field by field; `Function.Injective`.

## How to read an entry

Each entry is one tactic, one lemma used with `rw`, or one proof term. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : H → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{G : Type}` is any type. A bracket such as `[Group G]` is a
  requirement on `G` (a *type class*): `G` has `*`, `1`, `⁻¹` obeying the group axioms. `[Monoid M]` asks
  only for an associative `*` with unit `1`; every group is a monoid.
- In the problem the types are `{G H : Type*}` (`Type*` = a type in any universe; the infoview prints
  `G : Type u_1`). The guide uses `Type`; nothing else changes.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[Group G]`, `inst✝¹ : Group G`, `inst✝ : Group H` | `G` is a group; `inst✝` is the anonymous hypothesis a `[…]` binder creates (numbered `inst✝¹`, `inst✝²`, … when there are several) |
| `f : G →* H` | a *monoid homomorphism*: a function `G → H` bundled with proofs of `f 1 = 1` and `f (a * b) = f a * f b` |
| `f g`, `⇑f` | `f` applied to `g`; `⇑f` is `f` seen as a plain function `G → H` (a coercion, written `DFunLike.coe f`) |
| `Set G` | a set of elements of `G`, i.e. a predicate `G → Prop` |
| `{g \| f g = 1}` | the set of `g` with `f g = 1`; `a ∈ {g \| f g = 1}` *is* `f a = 1` by definition |
| `Subgroup G` | a structure: `carrier : Set G` and the proofs `one_mem'`, `mul_mem'`, `inv_mem'` |
| `{ carrier := S, one_mem' := …, … }` | a structure instance: a value of a structure type, given field by field |
| `g ∈ K` (`K : Subgroup G`) | `g` lies in the carrier of `K`; unfolds by definition to `g ∈ K.carrier` |
| `∀ {a b : G}, …` | `a`, `b` are implicit arguments: callers do not pass them, `intro` still names them |
| `∀ g ∈ K, g = 1` | `∀ g, g ∈ K → g = 1` |
| `Function.Injective ⇑f` | `∀ ⦃a b⦄, f a = f b → a = b`; `⦃a b⦄` are strict-implicit: filled in from the proof of `f a = f b` you pass, and `intro` still names them |
| `a⁻¹`, `(f a)⁻¹` | group inverse; `f a⁻¹` is `f (a⁻¹)`, the inverse of `f a` needs parentheses |
| `case mp`, `case mpr` | after `constructor` on `↔`: the `→` and the `←` direction |

---

## Part 1 · `kernel`

Statement: define `kernel f : Subgroup G` with carrier `{g | f g = 1}`. You give the set and three proofs:
`1` is in it, it is closed under `*`, it is closed under `⁻¹`.

**R1 · `refine { carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }`** changes the **goal list**:
a goal `Subgroup G` becomes the three closure obligations for `S`. In the `def` write the same braces as a
term, with `by …` or a proof term in each field; every field you leave out is an error. Lean lists the goals
as `mul_mem'`, `one_mem'`, `inv_mem'`. (The guide closes them with `exacts [hm, h1, hi]`: `exact` for each
open goal in order.) Placeholders: `{G : Type} [Group G] (S : Set G)`.

| Before | After |
|---|---|
| `⊢ Subgroup G` | `⊢ ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S`, `⊢ 1 ∈ S`, `⊢ ∀ {x : G}, x ∈ S → x⁻¹ ∈ S` |

With `S = {g | f g = 1}` the three fields become, e.g., `1 ∈ {g | f g = 1}`: `S` is substituted literally.

**R2 · set-builder membership** **closes** the goal: `a ∈ {x | P x}` is `P a` by definition, so a proof
`h : P a` is accepted as is (`exact h`, or just `h` as a field value). Placeholders: `{α : Type}
(P : α → Prop) (a : α)`.

The goal before; after `exact h` there are no goals (a `|` cannot sit in a table cell, so the states of
R2, R5 and R10 are shown as blocks):

```lean-goal
⊢ a ∈ {x | P x}
```

**R3 · `map_one`** changes the **goal**. The lemma is `map_one f : f 1 = 1` (for any hom; here
`f : G →* H`). As a term it proves `1 ∈ {g | f g = 1}` by R2. Placeholders: `{G H : Type} [Group G]
[Group H] (f : G →* H)`.

| Before | After |
|---|---|
| `⊢ P (f 1)` | `⊢ P 1` |

**R4 · `intro a b ha hb`** changes the **context**. `mul_mem'` has implicit binders `∀ {a b : G}`; `intro`
names them anyway, then the two membership hypotheses. For `inv_mem'` write `intro a ha`. Placeholders:
`(S : Set G) (Q : G → G → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ {a b : G}, a ∈ S → b ∈ S → Q a b` | `a b : G, ha : a ∈ S, hb : b ∈ S ⊢ Q a b` |

**R5 · `simp only [Set.mem_setOf_eq] at *`** changes the **context and the goal**. The lemma is
`Set.mem_setOf_eq : (a ∈ {x | p x}) = p a`; `at *` rewrites every hypothesis and the goal. It is only
cosmetic (the two forms are equal by definition, R2) but `rw` needs to see `f a = 1` literally.
Placeholders: `{α : Type} (P Q : α → Prop) (a : α)`.

Before, with `ha : a ∈ {x | P x}` in the context, and after, with `ha : P a`:

```lean-goal
⊢ a ∈ {x | Q x}
⊢ Q a
```

**R6 · `rw [map_mul]`** changes the **goal**. The lemma is `map_mul f a b : f (a * b) = f a * f b`.
Placeholders: `(f : G →* H) (a b : G)`.

| Before | After |
|---|---|
| `⊢ P (f (a * b))` | `⊢ P (f a * f b)` |

After R6, `rw [ha, hb]` (with `ha : f a = 1`, `hb : f b = 1`) leaves `1 * 1 = 1`.

**R7 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul a : 1 * a = a`. Placeholders:
`{M : Type} [Monoid M] (a : M)`; every group qualifies. A `rw` that leaves `1 = 1` closes it by `rfl`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R8 · `rw [map_inv]`** changes the **goal**. The lemma is `map_inv f a : f a⁻¹ = (f a)⁻¹` (needs groups on
both sides). Placeholders: `(f : G →* H) (a : G)`.

| Before | After |
|---|---|
| `⊢ P (f a⁻¹)` | `⊢ P (f a)⁻¹` |

**R9 · `rw [inv_one]`** changes the **goal**. The lemma is `inv_one : 1⁻¹ = 1`. Placeholders:
`{G : Type} [Group G]`.

| Before | After |
|---|---|
| `⊢ P 1⁻¹` | `⊢ P 1` |

## Part 2 · `mem_kernel`

Statement: `g ∈ kernel f ↔ f g = 1`. With the carrier of Part 1, both sides are the same proposition after
unfolding `kernel`, the membership in a `Subgroup`, and R2.

**R10 · `Iff.rfl`** **closes** a goal `A ↔ B` when `B` is `A` after unfolding definitions. It is a term:
`:= Iff.rfl`, no `by` needed. It fails if your carrier is written differently (say `{g | 1 = f g}`).
Placeholders: `{α : Type} (P : α → Prop) (a : α)`.

The goal before; after `exact Iff.rfl` there are no goals:

```lean-goal
⊢ a ∈ {x | P x} ↔ P a
```

W2 shows the same on a structure-built subgroup.

## Part 3 · `injective_iff`

Statement: `Function.Injective f ↔ ∀ g ∈ kernel f, g = 1`. (→) if `f g = 1 = f 1` then `g = 1`.
(←) if `f a = f b` then `f (a * b⁻¹) = f a * (f b)⁻¹ = 1`, so `a * b⁻¹ = 1`, so `a = b`.

**R11 · `constructor`** on `↔` changes the **goal list**: one goal per direction.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R12 · `intro g hg`** on `∀ g ∈ S, Q g` changes the **context**: the bounded quantifier is
`∀ g, g ∈ S → Q g`, so it takes two names. In (→) write `intro hf g hg` (first the injectivity
hypothesis). Placeholders: `(S : Set G) (Q : G → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ g ∈ S, Q g` | `g : G, hg : g ∈ S ⊢ Q g` |

**R13 · `hiff.mp ha`** (`Iff.mp`) changes the **context** when used in a `have`: from `hiff : A ↔ B` and
`ha : A` it gives `B` (`.mpr` goes back). Your own theorem works the same way: `(mem_kernel f g).mp hg :
f g = 1`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `ha : A ⊢ B` | `hb : B ⊢ B` |

**R14 · `h₁.trans h₂.symm`** (`Eq.trans`, `Eq.symm`) changes the **context** when used in a `have`.
`Eq.trans : a = b → b = c → a = c` and `Eq.symm : a = b → b = a`. With `h₁ : f g = 1` and `map_one f :
f 1 = 1` (R3), `h₁.trans (map_one f).symm : f g = f 1`. Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `h₁ : a = b, h₂ : c = b ⊢ a = c` | `h : a = c ⊢ a = c` |

**R15 · `hf h`** **closes** `a = b`: `hf : Function.Injective f` is a function taking `h : f a = f b`
(with `a`, `b` implicit) to `a = b`. Placeholders: `(f : G →* H) (a b : G)`.

| Before | After |
|---|---|
| `hf : Function.Injective ⇑f, h : f a = f b ⊢ a = b` | no goals |

**R16 · `intro a b hab`** on `Function.Injective f` changes the **context**: `intro` unfolds the definition
`∀ ⦃a b⦄, f a = f b → a = b`. In (←) write `intro h a b hab`. Placeholders: `(f : G →* H)`.

| Before | After |
|---|---|
| `⊢ Function.Injective ⇑f` | `a b : G, hab : f a = f b ⊢ a = b` |

**R17 · `rw [hiff]`** with `hiff : A ↔ B` changes the **goal**: `rw` rewrites propositions with an `↔` as
it rewrites terms with `=`. So `rw [mem_kernel]` turns `a * b⁻¹ ∈ kernel f` into `f (a * b⁻¹) = 1`
(Lean finds `f` and `g` by matching). Placeholders: `(A B : Prop) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P A` | `⊢ P B` |

**R18 · `rw [mul_inv_cancel]`** changes the **goal**. The lemma is `mul_inv_cancel a : a * a⁻¹ = 1`
(`inv_mul_cancel a : a⁻¹ * a = 1` is the mirror, W3). Placeholders: `{G : Type} [Group G] (a : G)`.

| Before | After |
|---|---|
| `⊢ P (a * a⁻¹)` | `⊢ P 1` |

**R19 · `mul_inv_eq_one.mp h`** **closes** `a = b`. The lemma is `mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b`.
In (←), `h _ this : a * b⁻¹ = 1` comes from applying `h : ∀ g ∈ kernel f, g = 1` to `_` (Lean infers
`a * b⁻¹`) and `this : a * b⁻¹ ∈ kernel f`. Placeholders: `{G : Type} [Group G] (a b : G)`.

| Before | After |
|---|---|
| `h : a * b⁻¹ = 1 ⊢ a = b` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** The image `{y | ∃ x, f x = y}` as a `Subgroup H`: the same structure instance (R1), `intro` on the
implicit binders (R4), then `obtain ⟨x, hx⟩ := hy` and a witness `⟨x * w, by rw [map_mul, hx, hw]⟩` (R6).

**W2.** `y ∈ img f ↔ ∃ x, f x = y := Iff.rfl` (R10): membership in a structure-built subgroup unfolds to its
carrier.

**W3.** From `hab : f a = f b`, prove `f (a⁻¹ * b) = 1` by R6, R8, `rw [hab]`, `rw [inv_mul_cancel]`:

```lean-goal
⊢ f (a⁻¹ * b) = 1
⊢ f a⁻¹ * f b = 1
⊢ (f a)⁻¹ * f b = 1
⊢ (f b)⁻¹ * f b = 1
```

---

## Traps

- Search tactics (`exact?`, `apply?`, `rw?`, `hint`, `try?`) are fine for exploring, but they close goals
  with banned lemmas (`MonoidHom.ker`, `injective_iff_map_eq_one`, …), so they cannot stay in your file.
- Each closure field of `kernel` is a proof about the literal set `{g | f g = 1}`; `rw [ha]` fails until
  R5 has turned `ha : a ∈ {g | f g = 1}` into `ha : f a = 1`.
- `f a⁻¹` means `f (a⁻¹)`. The inverse of `f a` is `(f a)⁻¹`.
- `mem_kernel` is `Iff.rfl` only if `kernel` is a structure instance with that exact carrier. If you
  build `kernel` some other way, `Iff.rfl` fails.
- `mul_inv_eq_one` is about `a * b⁻¹`; `inv_mul_eq_one` is about `a⁻¹ * b`. Pick the one that matches the
  element you put in the kernel.
- `rw [h]` needs the left side of `h` to appear literally (TACTIC_STATES, "Rewriting").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build a `Subgroup G` | `{ carrier := S, one_mem' := …, mul_mem' := …, inv_mem' := … }` | R1 |
| prove `a ∈ {x \| P x}` | a proof of `P a` | R2 |
| `f 1 = 1` | `map_one f` | R3 |
| name implicit binders | `intro a b ha hb` | R4 |
| `a ∈ {x \| P x}` → `P a` everywhere | `simp only [Set.mem_setOf_eq] at *` | R5 |
| `f (a * b)` → `f a * f b` | `rw [map_mul]` | R6 |
| `1 * a` → `a` | `rw [one_mul]` | R7 |
| `f a⁻¹` → `(f a)⁻¹` | `rw [map_inv]` | R8 |
| `1⁻¹` → `1` | `rw [inv_one]` | R9 |
| `↔` true by definition | `Iff.rfl` | R10 |
| split `↔` | `constructor` | R11 |
| `∀ g ∈ S, …` | `intro g hg` | R12 |
| use `hiff : A ↔ B` forwards | `hiff.mp ha` | R13 |
| chain / flip equations | `h₁.trans h₂.symm` | R14 |
| use injectivity | `hf h` | R15 |
| prove injectivity | `intro a b hab` | R16 |
| rewrite with an `↔` | `rw [mem_kernel]` | R17 |
| `a * a⁻¹` → `1` | `rw [mul_inv_cancel]` | R18 |
| `a * b⁻¹ = 1` → `a = b` | `mul_inv_eq_one.mp h` | R19 |
| see the state | infoview | |
