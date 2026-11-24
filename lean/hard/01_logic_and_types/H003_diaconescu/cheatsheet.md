# H003 · Diaconescu: choice implies excluded middle: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `have`, `fun`, `⟨_, _⟩`, `.1`/`.2`,
`·` focusing. **New here:** core Lean only (no Mathlib): the two extensionality principles `funext`
and `propext`, proof irrelevance, `subst`, `rcases` on `∨`, `rw … at h`, `Bool.noConfusion`, and
checking which axioms a proof depends on.

The setting. Lean's logic is constructive until you use the axiom `Classical.choice`; excluded
middle `p ∨ ¬p` is then a theorem (`Classical.em`), proved exactly the way this exercise does it.
Here `Classical.choice` is off limits. Instead the theorem receives a *choice operator* as an
argument: `choose P h` returns some `x : α` with `P x` from any proof `h : ∃ x, P x`, and
`choose_spec P h : P (choose P h)` says it does. `choose` is an ordinary function, so equal inputs
give equal outputs; combined with `funext` and `propext` that is enough to decide every `p`.

Axioms. `#print axioms H003.diaconescu` (write it below the theorem; the result appears in the
infoview) lists every axiom the proof uses. It must list only `propext` and `Quot.sound` (the
`AXIOMS:` line of the header; `./check` enforces it). `propext` is used by R5; `Quot.sound` enters
through `funext` (R4), which Lean proves from it.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" or a predicate `P : α → Prop`; `G : Prop` is an arbitrary goal.
- `{α : Type}` is any type (in this exercise it is `Bool`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α` | a hypothesis that is a function. `{α : Type}` is implicit: you write `choose P h`, and Lean finds `α` from `P` |
| `choose P hP` | the element `choose` picks for the predicate `P`, given the proof `hP : ∃ x, P x` |
| `choose_spec : ∀ {α : Type} (P : α → Prop) (h : ∃ x, P x), P (choose P h)` | the picked element satisfies `P`. `choose_spec _ hU` lets Lean fill `P` from the type of `hU` |
| `fun x => x = true ∨ p` | a predicate on `Bool`: "`x` is `true`, or `p` holds" |
| `(fun x => x = true ∨ p) = fun x => x = false ∨ p` | an equation between two predicates (functions `Bool → Prop`) |
| `(A) = (B)` with `A B : Prop` | equality of propositions; `propext` reduces it to `A ↔ B` |
| `true`, `false` vs `True`, `False` | the two values of the type `Bool` vs the true and false propositions (`Prop`) |
| `¬p` | `p → False` |
| `hP hQ : ∃ x, P x` | two proofs of the same proposition; Lean treats them as equal (R2) |
| `this` | the name `have :=` gives a fact when you do not name it (R10) |
| `case inl`, `case inr` | the two goals `rcases … with h \| h` makes: left and right side of `∨` |
| `case inl.inl`, `case inl.inr` | the goals of a second `rcases` inside the `inl` goal |
| `case mp`, `case mpr` | the two directions `constructor` makes from `A ↔ B`: `A → B` (mp) and `B → A` (mpr) |
| `a✝ : x = true ∨ p` | a hypothesis introduced by `intro _`: it exists but has no name you can use |
| `(x = true ∨ p) = (x = false ∨ p)` | after `funext x` (R4): the two predicate bodies at the new `x : Bool` |

---

## Part 1 · `choose_congr` (milestone; prove first, used in Part 2)

Statement: if `P = Q` then `choose P hP = choose Q hQ`, for any proofs `hP`, `hQ`. The two sides
differ in the predicate and in the proof argument.

**R1 · `subst h`** changes the **context**: for `h : P = Q` with `Q` a local variable, it deletes `Q`
and `h` and writes `P` for `Q` in the goal and in every hypothesis. Placeholders:
`{α : Type} (P Q : α → Prop) (a : α)`. `rw [h]` cannot do this: it rewrites only the goal, and here the type
of the proof argument depends on the predicate, so it fails with "motive is not type correct".

| Before | After |
|---|---|
| `h : P = Q, hQ : Q a ⊢ P a` | `hQ : P a ⊢ P a` |

**R2 · `rfl` with proof arguments** **closes** the goal. Any two proofs `h₁ h₂ : A` of a proposition
`A : Prop` are *definitionally* equal (proof irrelevance is built into Lean's type theory; it is not
an axiom), so `f h₁ = f h₂` holds by `rfl`. Placeholders: `{A : Prop} {β : Type} (f : A → β)`.

| Before | After |
|---|---|
| `h₁ h₂ : A ⊢ f h₁ = f h₂` | no goals |

---

## Part 2 · `key` (milestone; prove second, used in Part 3)

Statement: if `p` holds, the two choices agree:
`choose (fun x => x = true ∨ p) hU = choose (fun x => x = false ∨ p) hV`. After `intro hp`, reduce to
an equation of predicates with Part 1, then prove that with extensionality. The states, in
order: `⊢ choose (fun x => x = true ∨ p) hU = choose (fun x => x = false ∨ p) hV`, then (R3)
`⊢ (fun x => x = true ∨ p) = fun x => x = false ∨ p`, then (R4) `x : Bool ⊢ (x = true ∨ p) = (x = false ∨ p)`,
then (R5) `⊢ x = true ∨ p ↔ x = false ∨ p`; `constructor` (E005) splits that into `mp` and `mpr`.

**R3 · `apply hc`** changes the **goal**: Lean matches the conclusion of `hc` against the goal and
leaves the premise as the new goal. Placeholders: `{α β : Type} (f : α → β)`,
`hc : ∀ a b : α, a = b → f a = f b`. With the milestone, `choose_congr` takes `choose` as an explicit
first argument that the goal does not determine, so write `apply choose_congr choose`.

| Before | After |
|---|---|
| `⊢ f a = f b` | `⊢ a = b` |

**R4 · `funext x`** changes the **goal and the context**: two functions are equal when they agree at
every input. The theorem is `funext : (∀ x, f x = g x) → f = g`; term form
`funext fun x => (proof of f x = g x)`. Placeholders: `{α β : Type} (f g : α → β)`. When `f`, `g` are
`fun`-terms the new goal shows their bodies with `x` plugged in (W2).

| Before | After |
|---|---|
| `⊢ f = g` | `x : α ⊢ f x = g x` |

**R5 · `apply propext`** changes the **goal**: two propositions are equal when they are equivalent.
The axiom is `propext : (A ↔ B) → A = B`; term form `propext ⟨fun a => …, fun b => …⟩`.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A = B` | `⊢ A ↔ B` |

**R6 · `.inl` / `.inr`** change the **goal**: to prove `A ∨ B`, prove one side. `.inr hb` is
`Or.inr hb`; the dot finds `Or` from the expected type. `refine .inr ?_` leaves the side as the goal.
Placeholders: `(A B : Prop)`. Both directions of the `↔` in `key` are `fun _ => .inr hp`: each side
is "`…` or `p`", and you have `hp : p`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**W1 (R1, R2)** on a function with a proof argument, `pick : (n : Nat) → n ≠ 0 → Nat`:

```lean-goal
⊢ pick n hn = pick m hm
⊢ pick n hn = pick n hm
```

**W2 (R4, R5)** proves `(fun n : Nat => n < 3 ∧ q) = (fun n => n < 3)` from `hq : q`:

```lean-goal
⊢ (fun n => n < 3 ∧ q) = fun n => n < 3
⊢ (n < 3 ∧ q) = (n < 3)
⊢ n < 3 ∧ q ↔ n < 3
```

---

## Part 3 · `diaconescu`

Statement: from `choose` and `choose_spec`, `p ∨ ¬p` for an arbitrary `p : Prop`. Use the two
predicates `U x := x = true ∨ p` and `V x := x = false ∨ p` on `Bool`; both are inhabited whatever
`p` is.

**R7 · `⟨a, ?_⟩`** changes the **goal**: the anonymous constructor proves `∃ x, P x` from a witness
`a` and a proof of `P a`; `refine ⟨a, ?_⟩` leaves `P a` as the goal. Placeholders:
`{α : Type} (P : α → Prop) (a : α)`. As needed here, nested inside a `have` (TACTIC_STATES, "Adding
facts"): `have hU : ∃ x, x = true ∨ p := ⟨true, .inl rfl⟩` (R6 for the `∨`).

| Before | After |
|---|---|
| `⊢ ∃ x, P x` | `⊢ P a` |

**R8 · `rcases e with h | h`** changes the **goal list**: for `e : B ∨ C` there is one goal with
`h : B` and one with `h : C`. `e` can be any term, such as `choose_spec _ hU`. Placeholders:
`(A B C G : Prop)`, `hs : A → B ∨ C`, `a : A`, and `e` is `hs a`. In the exercise the left case of
`choose_spec _ hU` reads `hut : choose (fun x => x = true ∨ p) hU = true`.

| Before | After |
|---|---|
| `hs : A → B ∨ C ⊢ G` | `h : B ⊢ G`, `h : C ⊢ G` |

**R9 · `intro h` on `¬A`** changes the **goal and the context**: `¬A` is `A → False`. In term
position write `fun h => (proof of False)`, e.g. `.inr fun hp => by …`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R10 · `have := e`** changes the **context**: it adds `this : T` with `T` the type of `e`, here
`have := key choose p hU hV hp`. Placeholders: `(A G : Prop) (f : A → G) (a : A)`.

| Before | After |
|---|---|
| `⊢ G` | `this : G ⊢ G` |

**R11 · `rw [h₁, h₂] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the
goal, left to right with each equation in turn. Placeholders: `{α : Type} (a b c d : α)`,
`h₁ : a = c`, `h₂ : b = d`. In the exercise `h₁, h₂` are `hut, hvf` and `h` is `this`.

| Before | After |
|---|---|
| `h : a = b ⊢ G` | `h : c = d ⊢ G` |

**R12 · `exact Bool.noConfusion h`** **closes** any goal from `h : true = false`: distinct
constructors of an inductive type are never equal. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `h : true = false ⊢ G` | no goals |

**W3 (R9 → R10 → R11 → R12)** proves `¬q` from `hq : q → f 0 = f 1`, `h0 : f 0 = true`,
`h1 : f 1 = false` (`f : Nat → Bool`):

```lean-goal
⊢ ¬q
⊢ False
```

The context meanwhile gains `hq' : q`, then `this : f 0 = f 1`, which `rw [h0, h1] at this` turns
into `this : true = false`.

---

## Traps

- **Classical tactics are off limits.** `Classical.*` (`Classical.em`, `Classical.byContradiction`),
  `by_cases h : p` and `by_contra` on a bare `Prop`, `grind`, `decide`, and some `simp` lemmas use
  `Classical.choice`; `#print axioms` then lists it and `./check` fails. `rcases`, `intro`, `exact`,
  `apply`, `subst`, `rw` and `rfl` never add axioms.
- `rw [h]` with `h : P = Q` fails on `choose P hP = choose Q hQ` ("motive is not type correct"): the
  type of `hP` mentions `P`. Use `subst h` (R1).
- `subst h` needs one side of `h` to be a local variable. In `key` the predicates are `fun`-terms, so
  go through `choose_congr` instead of `subst`.
- `true = false` (in `Bool`) is not `False`. Close it with `Bool.noConfusion` (R12), not `exact h`.
- `choose_congr` takes `choose` explicitly: `apply choose_congr choose`, `key choose p hU hV hp`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| replace a variable by its equal everywhere | `subst h` | R1 |
| `f h₁ = f h₂` for proofs `h₁ h₂` | `rfl` | R2 |
| reduce `f a = f b` to `a = b` with a lemma | `apply hc` / `apply choose_congr choose` | R3 |
| equal functions | `funext x` / `funext fun x => …` | R4 |
| equal propositions | `apply propext` / `propext ⟨…, …⟩` | R5 |
| prove `A ∨ B` | `.inl ha` / `.inr hb` | R6 |
| an `∃` from a witness | `⟨a, ha⟩` / `refine ⟨a, ?_⟩` | R7 |
| case on `A ∨ B` | `rcases e with h \| h` | R8 |
| prove `¬A` | `intro h` / `fun h => …` | R9 |
| unnamed fact | `have := e` (named `this`) | R10 |
| rewrite a hypothesis | `rw [h₁, h₂] at h` | R11 |
| from `true = false` | `Bool.noConfusion h` | R12 |
| check axioms | `#print axioms H003.diaconescu` | |
