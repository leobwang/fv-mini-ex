# E081 · Quotients: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `↔` and anonymous constructors `⟨_, _⟩` (E005),
`fun` binders and term mode, `refine … ?_` (E031), `unfold` (E030), `rfl`, `show`, `simp [h]`, and `Bool`
equality `==`.
**New here:** core Lean's quotient types: a `Setoid` (a relation packaged with its equivalence proof), the
quotient type `Quotient s` of its classes, the class map `Quotient.mk`, functions out of a quotient
(`Quotient.lift`), and the two bridges between equal classes and related representatives
(`Quotient.sound`, `Quotient.exact`). No Mathlib.

## How to read an entry

Each entry is one tactic, one term construction, or one lemma. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : β → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α β : Type}` are arbitrary types; `{s : Setoid α}` is an
  arbitrary equivalence relation on `α` (in the exercise: `α := Nat`, `s := parityRel`).
- Entries that need a concrete relation use the guide's `mod3 : Setoid Nat` (`a % 3 = b % 3`), its quotient
  `Tri := Quotient mod3` and `Tri.mk n := Quotient.mk mod3 n`, never the exercise's `parityRel`.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Quotients in one paragraph

A `Setoid α` is a structure with a field `r : α → α → Prop` and a proof `iseqv` that `r` is reflexive,
symmetric and transitive. `a ≈ b` (typed `\approx`) is notation for `Setoid.r a b`, and it unfolds **by
definition** to the body of `r`: in the exercise `a ≈ b` *is* `a % 2 = b % 2`. `Quotient s` is the type of
equivalence classes; `Quotient.mk s a` is the class of `a`. The only ways in and out:

| Name | Type | Use |
|---|---|---|
| `Quotient.mk s` | `α → Quotient s` | the class of a representative |
| `Quotient.lift f hf` | `Quotient s → β`, given `f : α → β`, `hf : ∀ a b, a ≈ b → f a = f b` | define a function on classes (R1) |
| (computation) | `Quotient.lift f hf (Quotient.mk s a) ≡ f a` | by definition, so `rfl` (R4) |
| `Quotient.sound` | `a ≈ b → Quotient.mk s a = Quotient.mk s b` | prove two classes equal (R6) |
| `Quotient.exact` | `Quotient.mk s a = Quotient.mk s b → a ≈ b` | use an equation of classes (R9) |

`Quotient.sound` is where the axiom `Quot.sound` enters; `#print axioms` lists it, and the checker allows it.

## Reading the goals

| You see | It means |
|---|---|
| `Setoid Nat` | a relation on `Nat` bundled with its proof of being an equivalence |
| `a ≈ b` | `Setoid.r a b`: the relation of the setoid in play, here `a % 2 = b % 2` |
| `Quotient s` | the type of `s`-classes; `Parity` is a `def` for `Quotient parityRel` |
| `Quotient.mk s a` | the class of `a`; `Parity.mk a` is a `def` for `Quotient.mk parityRel a` |
| `Quotient.lift f hf` | the function on classes induced by `f`; `hf` proves `f` respects `≈` |
| `(Parity.mk n).isEven` | `Parity.isEven (Parity.mk n)`: dot notation, found through the type name `Parity` |
| `n % 2 == 0` | a `Bool` (`true` when `n` is even); `x = (n % 2 == 0)` compares two `Bool`s |
| `Parity.isEven._proof_1` | the name Lean gives the respect proof inside your `Quotient.lift …` (seen after `unfold Parity.isEven`) |
| `case refine_1`, `case refine_2` | the goals `?_` left by `refine`, in order |

---

## Part 1 · `Parity.isEven`

Statement: define `Parity.isEven : Parity → Bool`, the evenness of a class. A class is not a number, so you
give a function on representatives, `fun n => n % 2 == 0`, and prove that related representatives give the
same answer.

**R1 · `Quotient.lift f ?_`** changes the **goal**: a goal "construct a function `Quotient s → β`" becomes the
obligation that `f` respects `≈`. `Quotient.lift : (f : α → β) → (∀ a b, a ≈ b → f a = f b) → Quotient s → β`.
Placeholders: `{α β : Type} {s : Setoid α} (f : α → β)`. In the exercise the result is the body of a `def`, so
you write the whole thing as a term `Quotient.lift f (proof)`.

| Before | After |
|---|---|
| `⊢ Quotient s → β` | `⊢ ∀ (a b : α), a ≈ b → f a = f b` |

With `f := fun n => n % 2 == 0`, Lean shows the obligation already β-reduced (each `(fun n => …) a` evaluated):
`∀ (a b : Nat), a ≈ b → (a % 2 == 0) = (b % 2 == 0)`.

**R2 · `fun a b (h : a % 3 = b % 3) => ?_`** changes the **context**: it introduces `a`, `b` and the hypothesis,
and the type ascription `(h : …)` states `h` in its unfolded form. That is allowed because `a ≈ b` is
`mod3.r a b` is `a % 3 = b % 3` by definition. Plain `intro a b h` (or `fun a b h =>`) gives `h : a ≈ b`,
which `simp [h]` cannot use (Traps). Placeholders: `(f : Nat → Bool)`; the relation is `mod3`.

| Before | After |
|---|---|
| `⊢ ∀ (a b : Nat), a ≈ b → f a = f b` | `a b : Nat, h : a % 3 = b % 3 ⊢ f a = f b` |

**R3 · `simp [h]`** with `h : u = v` **closes** `g u = g v`: it rewrites every `u` into `v`, and the two sides
become equal. In the exercise `u` is `a % 2`, `v` is `b % 2` and `g u` is `u == 0`. Placeholders:
`{α β : Type} (g : α → β) (u v : α)`.

| Before | After |
|---|---|
| `h : u = v ⊢ g u = g v` | no goals |

**W1 (on `Tri`):** `Tri.rem := Quotient.lift (fun n => n % 3) (fun _ _ (h : _ % 3 = _ % 3) => h)`. Here the
obligation `a % 3 = b % 3` is exactly the hypothesis, so the proof is `h` itself.

---

## Part 2 · `isEven_mk`

Statement: `(Parity.mk n).isEven = (n % 2 == 0)`: on the class of `n`, `isEven` computes the evenness of `n`.
Nothing needs proving: every name on the left is a definition and the lift computes, so `rfl` closes it.

**R4 · `Quotient.lift f hf (Quotient.mk s a)` is `f a`** changes the **goal** (with `show`): `Quotient.lift`
applied to a class built by `Quotient.mk` reduces to `f` on the representative. It is a definitional equation,
not a lemma: core Lean has no name for it, and `show` or `rfl` see through it. Placeholders:
`{α β : Type} {s : Setoid α} (f : α → β) (hf : ∀ a b, a ≈ b → f a = f b) (a : α)`.

| Before | After `show P (f a)` |
|---|---|
| `⊢ P (Quotient.lift f hf (Quotient.mk s a))` | `⊢ P (f a)` |

**R5 · `unfold Tri.mk`** changes the **goal**: a wrapper definition is replaced by its body. `rfl` performs
such unfoldings by itself; `unfold` only lets you watch. In the exercise `Parity.mk` and `Parity.isEven` are
wrappers of this kind. Placeholders: `(n : Nat) (P : Tri → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Tri.mk n)` | `⊢ P (Quotient.mk mod3 n)` |

**W2 (on `Tri`):** `Tri.rem (Tri.mk n) = n % 3`, watched step by step: R5, then R4 via `show`, then `rfl`.
Note how Lean prints the start, with dot notation:

```lean-goal
⊢ (Tri.mk n).rem = n % 3
⊢ Tri.rem (Quotient.mk mod3 n) = n % 3
⊢ n % 3 = n % 3
```

`rfl` alone proves the first line already.

---

## Part 3 · `mk_three_seven`

Statement: `Parity.mk 3 = Parity.mk 7`: the classes of 3 and 7 are equal, because both are odd.

**R6 · `Quotient.sound`** changes the **goal**. The lemma is `a ≈ b → Quotient.mk s a = Quotient.mk s b`, so
`apply Quotient.sound` turns an equation of classes into the relation between representatives. As a term,
`Quotient.sound e` with `e : a ≈ b`. It also works on wrappers such as `Tri.mk 4 = Tri.mk 7` (Lean unfolds
`Tri.mk`). Placeholders: `{α : Type} {s : Setoid α} (a b : α)`.

| Before | After |
|---|---|
| `⊢ Quotient.mk s a = Quotient.mk s b` | `⊢ a ≈ b` |

**R7 · `show 4 % 3 = 7 % 3`** changes the **goal**: `4 ≈ 7` is displayed as the relation it unfolds to. Both
remainders evaluate to `1`, so `rfl` closes it. `rfl` also closes `4 ≈ 7` directly, without the `show`, and
`Quotient.sound rfl` is the whole proof as a term (W3). Placeholders: none (the concrete relation `mod3`).

| Before `apply Quotient.sound` | After it (R6) | After `show 4 % 3 = 7 % 3` |
|---|---|---|
| `⊢ Tri.mk 4 = Tri.mk 7` | `⊢ 4 ≈ 7` | `⊢ 4 % 3 = 7 % 3` |

---

## Part 4 · `mk_eq_iff`

Statement: `Parity.mk a = Parity.mk b ↔ a % 2 = b % 2`: two classes are equal exactly when the representatives
are related. Split the `↔`; left to right is `Quotient.exact`, right to left is `Quotient.sound`.

**R8 · `⟨fun h => ?_, fun h => ?_⟩`** changes the **goal list**: a proof of `A ↔ B` is a pair of implications,
so one goal becomes two, each with its hypothesis `h`. As a term: `⟨fun h => e₁, fun h => e₂⟩`. Placeholders:
`(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `h : A ⊢ B`, `h : B ⊢ A` |

**R9 · `Quotient.exact`** changes the **context** (used with `have`). The lemma is
`Quotient.mk s a = Quotient.mk s b → a ≈ b`. Since `a ≈ b` unfolds to the relation, `Quotient.exact h` proves a
goal `a % 2 = b % 2` directly. Placeholders: `{α : Type} {s : Setoid α} (a b : α)`.

| Before | After `have h' := Quotient.exact h` |
|---|---|
| `h : Quotient.mk s a = Quotient.mk s b ⊢ G` | `h' : a ≈ b ⊢ G` |

The other direction is R6: `Quotient.sound h` with `h : a % 2 = b % 2`.

**W3 (on `Tri`):** `Tri.mk 2 = Tri.mk 11` is `Quotient.sound rfl` (R6, R7).
**W4 (on `Tri`):** `Tri.mk a = Tri.mk b → a % 3 = b % 3` is `fun h => Quotient.exact h` (R9).

---

## Traps

- `a ≈ b` is the setoid's relation, not some built-in "approximately". In the exercise it means
  `parityRel.r a b`, i.e. `a % 2 = b % 2`. Write the binder as `fun a b (h : a % 2 = b % 2) => …` to see and use
  it in that form (R2).
- `simp [h]` with `h : a ≈ b` fails with "`simp` made no progress": `simp` needs an equation it can read
  syntactically, and `a ≈ b` only becomes one after unfolding. Ascribe the type first (R2).
- `⟨Quotient.exact, Quotient.sound⟩` for the `↔` fails with an "Application type mismatch": without an
  argument, Lean must match `?a ≈ ?b → Quotient.mk ?s ?a = Quotient.mk ?s ?b` against
  `a % 2 = b % 2 → Parity.mk a = Parity.mk b` and cannot find the setoid `?s` through the wrapper. Write
  `fun h => Quotient.sound h` (and likewise for `exact`): then the goal's type is known and Lean unfolds
  `Parity.mk` itself.
- You cannot type `a ≈ b` yourself: `parityRel` is a plain `def`, not an instance, so `have : (3 : Nat) ≈ 7`
  fails with "failed to synthesize `HasEquiv Nat`". `≈` only appears in goals that Lean builds from a
  `Quotient parityRel` (after `apply Quotient.sound`, in the `Quotient.lift` obligation). In your own `have`s
  and binders write the unfolded form `a % 2 = b % 2`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a function `Quotient s → β` | `Quotient.lift f (fun a b (h : r a b) => proof)` | R1, R2 |
| obligation `g u = g v` from `h : u = v` | `simp [h]` | R3 |
| `lift f hf (Quotient.mk s a)` → `f a` | `rfl` / `show` (definitional) | R4 |
| unfold a wrapper `def` | `unfold D` (or let `rfl` do it) | R5 |
| prove `Quotient.mk s a = Quotient.mk s b` | `Quotient.sound e`, `e : a ≈ b` | R6 |
| prove `a ≈ b` for numerals | `rfl` (or `show` the relation first) | R7 |
| split `A ↔ B` | `⟨fun h => …, fun h => …⟩` | R8 |
| use `h : Quotient.mk s a = Quotient.mk s b` | `Quotient.exact h : a ≈ b` | R9 |
| see the state | infoview | |
