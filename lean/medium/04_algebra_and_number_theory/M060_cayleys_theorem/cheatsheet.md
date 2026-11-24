# M060 · Cayley's theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): structures and `{ field := … }` instances, `intro`,
`rw`, `simp`, `have`, `rfl`. **New here:** Mathlib's groups (`Group G`), permutations
(`Equiv.Perm G`), monoid homomorphisms (`G →* H`), and how Lean coerces a structure to a function.

The maths. A *group* `G` has an associative `*`, a unit `1` and inverses `g⁻¹`. A *permutation* of `G`
is a bijection `G → G`, given here as a function together with its inverse. Permutations form a group
under composition. Cayley's theorem: `g ↦ (x ↦ g * x)` is an injective group homomorphism from `G` into
the permutations of `G`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Group G]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{G : Type*} [Group G]` | any type `G` (in any universe; the infoview prints `G : Type u_1`) with a group structure |
| `inst✝ : Group G` | the unnamed `[Group G]` argument, shown in the context |
| `g⁻¹` | the inverse of `g` in the group |
| `Equiv.Perm G` | `G ≃ G`: a structure with fields `toFun`, `invFun : G → G` and the two inverse laws |
| `{ toFun := f, invFun := g, left_inv := ⋯, right_inv := ⋯ }` | a permutation built by hand; `⋯` is a proof Lean does not print |
| `Function.LeftInverse g f` | `∀ x, g (f x) = x` (the `left_inv` field) |
| `Function.RightInverse g f` | `∀ x, f (g x) = x` (the `right_inv` field) |
| `σ x` | the permutation `σ` applied to `x`. Lean inserts the coercion `⇑σ` (σ's `toFun`) silently |
| `1 x` | the identity permutation `1 : Equiv.Perm G` applied to `x`, which is `x` (R8) |
| `σ * τ` | composition of permutations: `(σ * τ) x = σ (τ x)`, `τ` first (R10) |
| `G →* H` | `MonoidHom G H`: a function with fields `toFun`, `map_one' : toFun 1 = 1`, `map_mul'` |
| `leftMul g x`, `(leftMul a) 1` | two coercions: `leftMul g` is a permutation (the hom applied to `g`), then it is applied to `x` |
| `leftMul (G := G)` | `leftMul` with its implicit argument `G` given by name |
| `(fun x => g * x) a` | a function written inline, applied to `a`; not yet simplified to `g * a` (R2) |
| `fun x_1 => x * y * x_1` | Lean renames a bound variable to `x_1` when `x` is already taken |
| `Function.Injective f` | `∀ ⦃a b⦄, f a = f b → a = b`; `⦃a b⦄` are implicit arguments that `intro a b h` still names (R13) |
| `case refine_1` | the goal for the first `?_` of a `refine` |

---

## Part 1 · `leftMul`

Statement: define `leftMul : G →* Equiv.Perm G` with `leftMul g` the permutation `x ↦ g * x`. Its body is
a hole: you write two nested structure instances, the outer one a `MonoidHom`, the inner one (the value of
its `toFun g`) an `Equiv`. Four proof obligations appear: `left_inv`, `right_inv`, `map_one'`, `map_mul'`.

### Building the two structures

**R1 · `refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }`** changes the **goal list**: the
goal "a permutation" becomes the two inverse laws. You can instead fill a law directly with a term,
`left_inv := fun x => …`. Placeholders: `{α : Type} (f g : α → α)`.

| Before | After |
|---|---|
| `⊢ Equiv.Perm α` | `⊢ Function.LeftInverse g f`, `⊢ Function.RightInverse g f` |

**R2 · `intro x`** on `Function.LeftInverse g f` changes the **context and the goal**: the definition is
`∀ x, g (f x) = x`, so `intro` works. Same for `Function.RightInverse g f`, which gives `f (g x) = x`.
Placeholders: `{α : Type} (f g : α → α)`, `hl : ∀ x, g (f x) = x`. The example writes the two maps as
`fun x => …`, as your `leftMul` does, so you see what the goal really looks like:

| Before | After |
|---|---|
| `⊢ Function.LeftInverse (fun x => g x) fun x => f x` | `x : α ⊢ (fun x => g x) ((fun x => f x) x) = x` |

The applications `(fun x => …) a` are not yet reduced (substituting `a` for `x` is *β-reduction*). `rw`
matches text literally, so `rw [inv_mul_cancel_left]` fails on your goal
`(fun x => g⁻¹ * x) ((fun x => g * x) x) = x`. `exact` compares up to unfolding, so close it with a term:
`exact hl x` here, `exact` + R3 applied to `g x` in `leftMul`. (`simp` also closes it.)

**R3 · `inv_mul_cancel_left`** changes the **goal**. The lemma is `a⁻¹ * (a * b) = b`. Placeholders:
`{G : Type} [Group G] (a b : G)`; every group qualifies (here your `G`). As a term,
`inv_mul_cancel_left g x : g⁻¹ * (g * x) = x` is exactly a `left_inv` law.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * (a * b))` | `⊢ P b` |

**R4 · `mul_inv_cancel_left`** changes the **goal**. The lemma is `a * (a⁻¹ * b) = b`: the `right_inv`
law. Placeholders: `{G : Type} [Group G] (a b : G)`.

| Before | After |
|---|---|
| `⊢ P (a * (a⁻¹ * b))` | `⊢ P b` |

**R5 · `refine { toFun := φ, map_one' := ?_, map_mul' := ?_ }`** changes the **goal list**: the goal
"a homomorphism" becomes its two laws. Placeholders: `{M N : Type} [Monoid M] [Monoid N] (φ : M → N)`
(a *monoid* has `*` and `1` but maybe no inverses; every group, and `Equiv.Perm α`, is one).
The `map_mul'` goal starts with `∀ (x y : M)`, so begin it with `intro a b` (or write
`map_mul' := fun a b => by …`).

| Before | After |
|---|---|
| `⊢ M →* N` | `⊢ φ 1 = 1`, `⊢ ∀ (x y : M), φ (x * y) = φ x * φ y` |

You can nest the two: one `refine` whose `toFun := fun g => { …, left_inv := ?_, right_inv := ?_ }` and
whose `map_one'`, `map_mul'` are `?_` gives four goals, `refine_1` … `refine_4`, in the order
`left_inv`, `right_inv`, `map_one'`, `map_mul'` (handle each with `·`). Or write the whole body as a term,
with `by …` only inside the fields that need tactics.

In `leftMul`, `φ` is your `fun g => { toFun := …, … }`, so the two goals read
`{ toFun := fun x => 1 * x, … } = 1` and `{ toFun := fun x => a * b * x, … } = { … } * { … }`:
equations between permutations.

### Equations between permutations

**R6 · `ext x`** changes the **goal and the context**. It uses `Equiv.ext`: two permutations are equal when
they agree at every point. Placeholders: `{α : Type} (σ τ : Equiv.Perm α)`.

| Before | After |
|---|---|
| `⊢ σ = τ` | `x : α ⊢ σ x = τ x` |

`simp` then evaluates both sides with R7–R11. R7, R8, R9, R10 are applied by `simp` itself (it uses the
function forms `Equiv.Perm.coe_one : ⇑1 = id` and `Equiv.Perm.coe_mul : ⇑(σ * τ) = ⇑σ ∘ ⇑τ`, to the same
effect); R11 must be named: `simp [mul_assoc]`.

**R7 · `Equiv.coe_fn_mk`** changes the **goal**: a hand-built permutation applied to `x` becomes its
`toFun` applied to `x`. Placeholders: `{α : Type} (f g : α → α)`, `hl : Function.LeftInverse g f`,
`hr : Function.RightInverse g f`.

| Before | After |
|---|---|
| `⊢ P ({ toFun := f, invFun := g, left_inv := hl, right_inv := hr } x)` | `⊢ P (f x)` |

**R8 · `Equiv.Perm.one_apply`** changes the **goal**: the identity permutation applied to `x` is `x`.
Placeholders: `{α : Type} (x : α)`.

| Before | After |
|---|---|
| `⊢ P (1 x)` | `⊢ P x` |

**R9 · `one_mul`** changes the **goal**. The lemma is `1 * a = a`. Placeholders:
`{M : Type} [Monoid M] (a : M)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R10 · `Equiv.Perm.mul_apply`** changes the **goal**: a product of permutations applied to `x` is the
composition, right factor first. Placeholders: `{α : Type} (σ τ : Equiv.Perm α) (x : α)`.

| Before | After |
|---|---|
| `⊢ P ((σ * τ) x)` | `⊢ P (σ (τ x))` |

**R11 · `mul_assoc`** changes the **goal**. The lemma is `a * b * c = a * (b * c)` (`*` groups to the left,
so `a * b * c` is `(a * b) * c`). Placeholders: `{M : Type} [Monoid M] (a b c : M)`.

| Before | After |
|---|---|
| `⊢ P (a * b * c)` | `⊢ P (a * (b * c))` |

---

## Part 2 · `leftMul_apply`

Statement: `leftMul g x = g * x`, the formula for the map you built.

**R12 · `rfl`** **closes** the goal when both sides unfold to the same term. Applying a hand-built
structure just reads its `toFun` field, so this needs no rewriting. Placeholders:
`{M α : Type} [Monoid M] (φ : M → Equiv.Perm α) (a : M) (x : α)`, with `h1`, `hm` the two laws.

| Before | After |
|---|---|
| `⊢ ({ toFun := φ, map_one' := h1, map_mul' := hm } a) x = (φ a) x` | closed |

It works only because `leftMul` was built directly from structure instances. If your definition went
through other library constructions, `rfl` may fail.

---

## Part 3 · `cayley`

Statement: `Function.Injective (leftMul (G := G))`: if `leftMul a = leftMul b` as permutations, then
`a = b`. Idea: evaluate both permutations at `1`; that gives `a * 1 = b * 1`.

**R13 · `intro a b h`** on `Function.Injective f` changes the **context and the goal**. Placeholders:
`{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Function.Injective f` | `a b : α, h : f a = f b ⊢ a = b` |

**R14 · `have := congrArg (fun σ => σ x) h`** changes the **context**: from an equation of permutations
it derives the equation of their values at `x`, named `this`. `congrArg F h : F σ = F τ` for any function
`F` and `h : σ = τ`. Placeholders: `{α : Type} (σ τ : Equiv.Perm α) (x : α)`.

| Before | After |
|---|---|
| `h : σ = τ ⊢ Q` | `this : σ x = τ x ⊢ Q` |

**R15 · `mul_one`** changes the **goal** (or a hypothesis, with `at`). The lemma is `a * 1 = a`.
Placeholders: `{M : Type} [Monoid M] (a : M)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**R16 · `simpa [l] using this`** **closes** the goal: it simplifies both `this` and the goal with the simp set
plus `l`, then closes the goal with the simplified `this`. In `cayley`, `l` is the lemma you proved in
Part 2 (`simp` already knows R15). Placeholders: `{α : Type} (f : α → α) (l : ∀ x, f x = x)`.

| Before | After |
|---|---|
| `this : f a = f b ⊢ a = b` | closed |

### Worked combinations (W1–W4, on `shift k : x ↦ x + k`, a permutation of `ℤ`)

**W1.** `shift k x = x + k` is `rfl` (R12).

**W2.** `shift 0 = 1`: R6 gives

```lean-goal
⊢ (shift 0) x = 1 x
```

and `simp [shift]` (R7, R8, `add_zero`) closes it.

**W3.** `shift (a + b) = shift a * shift b`: R6, then `simp [shift]` (R7, R10) leaves

```lean-goal
⊢ x + (a + b) = x + b + a
```

which `ring` closes (`ℤ` is commutative; in a group you would use R11 instead).

**W4.** `Function.Injective shift`: R13, then R14 at the point `0`:

| Before | After |
|---|---|
| `h : shift a = shift b ⊢ a = b` | `this : (shift a) 0 = (shift b) 0 ⊢ a = b` |

then `simpa [shift] using this` (R16).

---

## Traps

- Search tactics (`exact?`, `apply?`, `rw?`, `hint`, `try?`) are fine for exploring, but they close goals
  with banned library terms (Mathlib already has this construction), so they cannot stay in your proof.
- After `intro x` on `left_inv`/`right_inv`, `rw [inv_mul_cancel_left]` fails: the goal is
  `(fun x => g⁻¹ * x) ((fun x => g * x) x) = x`, not yet `g⁻¹ * (g * x) = x` (R2). Use `exact` with R3/R4.
- `map_mul'` needs `mul_assoc` (R11): plain `simp` stops at `a * b * x = a * (b * x)`.
- `simp at this` with `this : (leftMul a) 1 = (leftMul b) 1` makes no progress: `simp` does not look inside
  your definition. Give it the formula: `simpa [leftMul_apply] using this` (R16).
- The `map_one'` goal contains `invFun := fun x => 1⁻¹ * x`; that is harmless, since `ext x` compares only
  the `toFun` side (R6).
- A field proved by tactics is written `map_one' := by …`. If the proof spans several lines, indent it
  further than the field name.
- `t1 ; t2` runs `t2` on the first goal only; after `refine` with several `?_`, use `·` per goal or `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build a permutation | `{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }` | R1 |
| open an inverse law, close it | `intro x`, then `exact` a term (not `rw`) | R2 |
| `g⁻¹ * (g * x) = x` / `g * (g⁻¹ * x) = x` | `inv_mul_cancel_left g x` / `mul_inv_cancel_left g x` | R3, R4 |
| build a homomorphism `G →* H` | `{ toFun := φ, map_one' := ?_, map_mul' := ?_ }` | R5 |
| equation of permutations → pointwise | `ext x` | R6 |
| evaluate `{…} x`, `1 x`, `(σ * τ) x` | `simp` | R7, R8, R10 |
| `1 * a`, `a * 1` | `simp` (`one_mul`, `mul_one`) | R9, R15 |
| reassociate products | `simp [mul_assoc]` | R11 |
| formula for a hand-built map | `rfl` | R12 |
| prove `Function.Injective f` | `intro a b h` | R13 |
| equal permutations → equal values | `have := congrArg (fun σ => σ x) h` | R14 |
| finish from a hypothesis | `simpa [l] using this` | R16 |
| see the state | infoview | |
