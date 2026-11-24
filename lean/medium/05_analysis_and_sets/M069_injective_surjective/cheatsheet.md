# M069 · Injective and surjective: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `apply`, `exact`, `∃` and anonymous
constructors `⟨_, _⟩`, `rfl`, `simp`. **New here:** Mathlib's `Function.Injective`,
`Function.Surjective` and function composition `∘` (`Function.comp`), and the `rfl` pattern of
`obtain` (substituting a variable away instead of naming the equation).

## How to read an entry

Each entry is one tactic, one definition, or one lemma used with `rw`/`simp`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : β → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α β γ : Type}` are arbitrary types; `f : β → γ`,
  `g : α → β` are arbitrary functions between them (no type classes are needed in this problem).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

The problem has `open Function`, so `Function.Injective f` prints as `Injective f`.

| You see | It means |
|---|---|
| `Injective f` | `∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`: equal outputs force equal inputs (R1) |
| `Surjective f` | `∀ b, ∃ a, f a = b`: every element of the codomain has a preimage (R5) |
| `f ∘ g` | the composite "first `g`, then `f`": `(f ∘ g) x = f (g x)` by definition (R4) |
| `⦃a₁ a₂ : α⦄` | strict-implicit arguments: `hf h` fills them from `h : f a₁ = f a₂`; plain `hf` stays unapplied |
| `∃ a, f a = c` | "some `a` with `f a = c`"; prove it with a witness `⟨a, proof⟩`, use it with `obtain` |
| `fun n => 2 * n + 1` | an anonymous function; `simp` beta-reduces `(fun n => e) a` to `e[a/n]` |
| `∃ a_1, (f ∘ g) a_1 = f (g a)` | Lean renamed the bound variable to `a_1` because a local `a` is already in the context; it is still a bound name |
| `{f : β → γ}` in a spec | `f` is implicit in the theorem; inside the proof it is an ordinary variable |

---

## Part 1 · `inj_comp`

Statement: if `f : β → γ` and `g : α → β` are injective, so is `f ∘ g : α → γ`. Proof idea:
`f (g a) = f (g b)` gives `g a = g b` (by `hf`), which gives `a = b` (by `hg`).

**R1 · `Function.Injective`** (seen with `unfold Function.Injective`) changes the **goal**: the name is
replaced by its definition. You never need this step in a proof (R2 does it implicitly); it shows what
`Injective` means. Placeholders: `{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Injective f` | `⊢ ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂` |

**R2 · `intro a b h`** changes the **context and the goal**: `intro` unfolds `Injective f` and introduces
the two inputs and the equation of outputs. Placeholders: `{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Injective f` | `a b : α, h : f a = f b ⊢ a = b` |

**R3 · `apply hf`** with `hf : Injective f` changes the **goal**: to show `a = b`, it suffices to show
`f a = f b`. The term form is `hf h : a = b` for `h : f a = f b`. Placeholders:
`{α β : Type} (f : α → β) (hf : Injective f) (a b : α)`.

| Before | After |
|---|---|
| `hf : Injective f ⊢ a = b` | `⊢ f a = f b` |

**R4 · `Function.comp_apply`** changes the **goal**. The lemma is `(f ∘ g) x = f (g x)`. It holds by
definition (`rfl`), so `exact`, `apply` and `rfl` already see through `∘`; you need the lemma only to make
`rw` or the infoview show the nested form, and `simp` uses it by itself. Placeholders:
`{α β γ : Type} (f : β → γ) (g : α → β) (x : α)`.

| Before | After |
|---|---|
| `⊢ P ((f ∘ g) x)` | `⊢ P (f (g x))` |

After R2 in `inj_comp`, `h` reads `(f ∘ g) a = (f ∘ g) b`. Because of R4 it *is* `f (g a) = f (g b)`, so
`hf h : g a = g b` type-checks without any rewriting.

---

## Part 2 · `surj_comp`

Statement: if `f` and `g` are surjective, so is `f ∘ g`. Proof idea: given `c : γ`, pick `b` with
`f b = c`, then `a` with `g a = b`; `a` is the preimage.

**R5 · `Function.Surjective`** (seen with `unfold Function.Surjective`) changes the **goal**: the name is
replaced by its definition. As with R1, `intro` makes this step unnecessary. Placeholders:
`{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Surjective f` | `⊢ ∀ (b : β), ∃ a, f a = b` |

**R6 · `intro c`** changes the **context and the goal**: it introduces the target point. Placeholders:
`{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Surjective f` | `c : β ⊢ ∃ a, f a = c` |

**R7 · `obtain ⟨a, ha⟩ := hf c`** changes the **context**: `hf c : ∃ a, f a = c` is taken apart into a
witness `a` and its property `ha`. The goal is unchanged. Placeholders:
`{α β : Type} (f : α → β) (hf : Surjective f) (c : β)`.

| Before | After |
|---|---|
| `⊢ P c` | `a : α, ha : f a = c ⊢ P c` |

**R8 · `obtain ⟨a, rfl⟩ := hf c`** changes the **context and the goal**: instead of naming the equation
`f a = c`, the pattern `rfl` substitutes it, so `c` disappears and every `c` (goal and hypotheses) becomes
`f a`. It needs `c` to be a local variable (introduced by R6); on `hf (c - 1)` use R7. Placeholders as in R7.

| Before | After |
|---|---|
| `c : β ⊢ P c` | `a : α ⊢ P (f a)` |

**R9 · `refine ⟨x, ?_⟩`** changes the **goal**: it supplies the witness of an `∃` and leaves its property.
In one step, `exact ⟨x, hx⟩`; when `f x` and `y` are equal by definition (after R8 they often are), write
`exact ⟨x, rfl⟩`. Placeholders: `{α β : Type} (f : α → β) (x : α) (y : β)`.

| Before | After |
|---|---|
| `⊢ ∃ a, f a = y` | `⊢ f x = y` |

In `surj_comp`, after two R8 steps the goal is `∃ a_1, (f ∘ g) a_1 = f (g a)`, and `⟨a, rfl⟩` closes it by R4.

---

## Part 3 · `inj_of_comp`

Statement: if `f ∘ g` is injective, then `g` is injective (`f` need not be). Proof idea: `g a = g b`
implies `f (g a) = f (g b)`, and injectivity of `f ∘ g` gives `a = b`.

Steps: R2 (`intro a b hab`), then R3 with `h : Injective (f ∘ g)` (`apply h`), which leaves
`(f ∘ g) a = (f ∘ g) b`, then R10.

**R10 · `simp [h]`** with `h : g x = g y` **closes** the goal `(f ∘ g) x = (f ∘ g) y`: `simp` unfolds `∘`
(R4), rewrites `g x` to `g y` with `h`, and both sides become equal. Placeholders:
`{α β γ : Type} (f : β → γ) (g : α → β) (x y : α)`. `rw [h]` alone fails here: `g x` is hidden inside
`(f ∘ g) x`, which is not literally `f (g x)`.

| Before | After |
|---|---|
| `h : g x = g y ⊢ (f ∘ g) x = (f ∘ g) y` | no goals |

---

## Part 4 · `surj_of_comp`

Statement: if `f ∘ g` is surjective, then `f` is surjective (`g` need not be). Proof idea: a preimage of
`c` under `f ∘ g` is some `a`; then `g a` is a preimage under `f`.

Steps: R6 (`intro c`), R7 on `h c` (gives `ha : (f ∘ g) a = c`), then R9 with witness `g a` and `ha`
(accepted as `f (g a) = c` by R4).

### Worked combinations (W1–W4, on concrete functions)

**W1.** `Injective (fun n : ℕ => 2 * n + 1)`: after R2 the hypothesis still shows the `fun`;
`simp at h` beta-reduces it and cancels, leaving `h : a = b`.

| Before | After `simp at h` |
|---|---|
| `h : (fun n => 2 * n + 1) a = (fun n => 2 * n + 1) b ⊢ a = b` | `h : a = b ⊢ a = b` |

**W2.** `Surjective (fun n : ℤ => n + 1)`: R6, then R9 with witness `c - 1`, then `simp`.

| Before | After `refine ⟨c - 1, ?_⟩` |
|---|---|
| `c : ℤ ⊢ ∃ a, (fun n => n + 1) a = c` | `⊢ (fun n => n + 1) (c - 1) = c` |

**W3.** `Surjective (fun n => f n + 1)` from `hf : Surjective f` (`f : ℕ → ℤ`): R6, R7 on `hf (c - 1)`
(R8 would fail: `c - 1` is not a variable), R9, then R10.

| Before | After `obtain ⟨a, ha⟩ := hf (c - 1)` |
|---|---|
| `c : ℤ ⊢ ∃ a, (fun n => f n + 1) a = c` | `a : ℕ, ha : f a = c - 1 ⊢ ∃ a, (fun n => f n + 1) a = c` |

**W4.** R3 in term form: `have e : a + 1 = b + 1 := hf h` from `h : f (a + 1) = f (b + 1)`, then `omega`.

---

## Traps

- `rw [hab]` on `(f ∘ g) a = (f ∘ g) b` fails: the pattern `g a` does not occur literally. Use `simp [hab]`,
  or `rw [Function.comp_apply, Function.comp_apply, hab]`, or `exact congrArg f hab`.
- `obtain ⟨a, rfl⟩ := e` needs one side of the equation to be a local variable that can be eliminated; with
  `e : f a = c - 1` it fails. Use a named hypothesis (R7) there.
- The order of composition: `f ∘ g` applies `g` first. In `inj_of_comp` the conclusion is about `g` (the inner
  map), in `surj_of_comp` about `f` (the outer map); the other ones are false in general.
- `hf` alone has type `Injective f`; because its binders are strict-implicit, `hf h` needs `h` explicitly, and
  `hf (a₁ := a)` is how you would give an input by hand.
- The library versions (`Function.Injective.comp`, `Function.Surjective.comp` and their `of_comp` converses)
  are banned here: prove them from the definitions.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see what `Injective` / `Surjective` mean | `unfold Function.Injective` / `unfold Function.Surjective` | R1, R5 |
| start an injectivity proof | `intro a b h` | R2 |
| `a = b` from injectivity of `f` | `apply hf` (or term `hf h`) | R3 |
| `(f ∘ g) x` → `f (g x)` | `rw [Function.comp_apply]` (or nothing: it is `rfl`) | R4 |
| start a surjectivity proof | `intro c` | R6 |
| take apart `hf c : ∃ a, f a = c` | `obtain ⟨a, ha⟩ := hf c` | R7 |
| … and substitute `c := f a` | `obtain ⟨a, rfl⟩ := hf c` | R8 |
| prove `∃ a, f a = y` | `refine ⟨x, ?_⟩` / `exact ⟨x, hx⟩` / `exact ⟨x, rfl⟩` | R9 |
| close `(f ∘ g) x = (f ∘ g) y` from `g x = g y` | `simp [h]` | R10 |
| beta-reduce `(fun n => e) a` in a hypothesis | `simp at h` | W1 |
| see the state | infoview | |
