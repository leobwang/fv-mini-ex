# E004 · Term-mode proofs: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md); this exercise bans
them (`BANNED: by`), but each entry below says which tactic its term replaces.

**Assumed:** E001 (`theorem`/`example`, `rfl`), E002 (`def`), E003 (`intro`, `exact`, `apply`; a hypothesis
`h : A → B` is a function, and `h a` proves `B` from `a : A`).
**New here:** proofs written as terms, with no `by`: `fun` for `→`, the anonymous constructor `⟨_, _⟩` for `∧`,
pattern-matching `fun ⟨…⟩ =>`, the projections `.1` / `.2` on `∧` and on `↔`; the core names `And.intro`,
`And.left`, `And.right`, `Iff.mp`, `Iff.mpr`. No Mathlib.

## How to read an entry

Each entry is one piece of term syntax. With no tactic block there is no goal list. What plays the role of the
goal is the **expected type**: the type the term at the cursor must have. An entry says what the step changes:

- **goal**: the expected type at the spot you still have to fill (R2 turns one expected `A ∧ B` into two holes);
- **context**: the hypotheses available there (R1, R3, R4 add some);
- **closes**: the term needs nothing more (R5, R6, R7 once applied to all their arguments).

How to see a state yourself: write `_` where a term is missing. Lean reports "don't know how to synthesize
placeholder" (with "for argument `left`" or `right` when the `_` is a component of `⟨_, _⟩`), lists the context
under "context:", then the expected type after the turnstile `⊢`. With several `_`, one error per hole; the later
hole may be reported first, so match each by its line:column position. Every **Before** / **After**
cell below is such a report, taken from the guide's examples with `_` in place of the next term (only the
hypotheses that change are shown; "expects `T`" is the line after the turnstile). Undo the `_` before you move
on: a file with `_` left in it does not compile.

- `A B C G : Prop` are arbitrary propositions (statements).
- A hypothesis such as `k`, `f` or `g` in an entry is only there to finish the example.

## Reading the goals

| You see | It means |
|---|---|
| `A → B` | a function taking a proof of `A` to a proof of `B`; `→` nests to the right: `A → B → C` is `A → (B → C)` |
| `A ∧ B`, `And A B` | `A` and `B`; a proof is a pair `⟨ha, hb⟩`. `./check` output prints the second form |
| `A ∧ B ∧ C` | `A ∧ (B ∧ C)`: `∧` nests to the right too |
| `A ↔ B`, `Iff A B` | `A` if and only if `B`: a pair of implications, `.1 : A → B` and `.2 : B → A` |
| `fun h => e` | the function that sends `h` to `e` (`λ` in other languages); typed `fun`, `=>` |
| `⟨a, b⟩` | the anonymous constructor: here `And.intro a b`; typed `\<` and `\>` |
| `x✝ : A ∧ B` | the pair bound by a pattern `fun ⟨ha, hb⟩ =>`: it exists but has no name you can use |
| `right✝ : B` | a component you named `_` in a pattern: present, but unusable |

---

## Part 1 · `and_swap`

Statement: `P ∧ Q → Q ∧ P`. In words: a function that takes a pair of proofs and returns the same two proofs in
the other order. Entries: R3, then R2. R1 comes first because R3 is R1 with a pattern in place of the name.

**R1 · `fun h => e`** changes the **context**: for an expected `A → B`, `h : A` is added and the body `e` must
have type `B`. It is the term that `intro h` (E003) builds. Placeholders: `(A B : Prop)`.

| Before | After `fun h => _` |
|---|---|
| expects `A → B` | `h : A` · the hole expects `B` |

**R2 · `⟨a, b⟩`** changes the **goal**: an expected `A ∧ B` becomes two holes. It is `And.intro a b`, with
`And.intro : a → b → a ∧ b` (lower-case `a b` are the lemma's own implicit propositions, read off the
arguments). The tactic form is `constructor` or `exact ⟨a, b⟩`. Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After `⟨_, _⟩` |
|---|---|
| `ha : A`, `hb : B` · expects `A ∧ B` | first hole expects `A`; second hole expects `B` |

**R3 · `fun ⟨ha, hb⟩ => e`** changes the **context**: for an expected `A ∧ B → G`, the pair is taken apart as
it is bound, `ha : A` and `hb : B` are added, and the body must have type `G`. Write `_` for a component you do
not need (it then shows as `right✝`). The tactic form is `intro ⟨ha, hb⟩`. Placeholders: `(A B G : Prop)`.

| Before | After `fun ⟨ha, hb⟩ => _` | After `fun ⟨ha, _⟩ => _` |
|---|---|---|
| expects `A ∧ B → G` | `x✝ : A ∧ B`, `ha : A`, `hb : B` · the hole expects `G` | `x✝ : A ∧ B`, `ha : A`, `right✝ : B` · the hole expects `G` |

**W1.** `fun ⟨ha, _, hc⟩ => ⟨hc, ha⟩ : A ∧ B ∧ C → C ∧ A`. Patterns flatten like `∧` nests: `⟨ha, _, hc⟩` is
`⟨ha, ⟨_, hc⟩⟩`.

---

## Part 2 · `curry_and`

Statement: `(P ∧ Q → R) → P → Q → R`. In words: a function that expects a pair can be fed its two components
one at a time. Three premises to bind; the only thing that produces `R` is the first one, and it wants a pair.
Entries: R4, R5 (below), then R2 (Part 1).

**R4 · `fun h1 h2 h3 => e`** changes the **context**: one name per `→`, left to right, all added at once. It is
`intro h1 h2 h3`. Placeholders: `(A B C G : Prop)`.

| Before | After `fun h1 h2 h3 => _` |
|---|---|
| expects `A → B → C → G` | `h1 : A`, `h2 : B`, `h3 : C` · the hole expects `G` |

**R5 · `f a`, `f a b`** **closes** the hole once every premise is supplied: from `f : A → B` and `a : A`, `f a : B`.
Arguments are separated by spaces, no commas or parentheses around them, in the order of `f`'s premises. With
holes, `f _ _` leaves one hole per premise. It is `exact f a` (or `apply f`, then the premises). Placeholders:
`(A B C : Prop) (f : A → B → C)`.

| Before | After `f _ _` |
|---|---|
| `f : A → B → C` · expects `C` | first hole expects `A`; second hole expects `B` |

**W2.** `fun ⟨ha, hc⟩ => ⟨f ha, g hc⟩ : A ∧ C → B ∧ G` with `f : A → B`, `g : C → G`: R3, then R2 whose
components are R5 applications.

---

## Part 3 · `uncurry_and`

Statement: `(P → Q → R) → P ∧ Q → R`. The converse of Part 2: a function that takes two arguments one at a time
can be fed a pair. Bind the function and the pair, then hand the function the pair's two components.
Entries: R4, R5 (Part 2), then R6 twice (below); or R3 (Part 1) then R5.

**R6 · `h.1`, `h.2`** **close** a hole of type `A` (resp. `B`) from `h : A ∧ B`. `h.1` is `And.left h` with
`And.left : a ∧ b → a`; `h.2` is `And.right h`. Use them when the pair has a name (from R1 or R4); R3 is the
alternative that takes it apart at the binder. Chained: `h.2.2` is the third component of `A ∧ B ∧ C` (W4).
Placeholders: `(A B : Prop) (h : A ∧ B)`.

| Before | After `h.1` | After `h.2` (expects `B` instead) |
|---|---|---|
| `h : A ∧ B` · expects `A` | nothing left | nothing left |

**W4.** `⟨h.2.2, h.1⟩ : C ∧ A` from `h : A ∧ B ∧ C`: R2 with R6 as the components.

---

## Part 4 · `and_imp_iff`

Statement: from `h : P ↔ Q` and `hr : Q → R`, prove `P → R ∧ Q`. In words: given `P`, turn it into `Q` through
the `↔`, then build the pair whose second component is that `Q` and whose first is `hr` applied to it.
Entries: R1, R2 (Part 1), then R5 (Part 2) with R8, and R7 (below).

**R7 · `h.1 a`, `h.2 b`** for `h : A ↔ B`: `h.1` is `Iff.mp h : A → B` (left to right), `h.2` is
`Iff.mpr h : B → A` (right to left). Applied as in R5, each **closes** its hole, or with a `_` changes the
**goal** to the premise. Placeholders: `(A B : Prop) (h : A ↔ B)`.

| Before | After `h.1 _` | After `h.2 _` (expects `A` instead) |
|---|---|---|
| `h : A ↔ B` · expects `B` | the hole expects `A` | the hole expects `B` |

**R8 · `f (g a)`** changes the **goal**: the argument of `f` is itself an application, so it needs parentheses.
`f g a` parses as `(f g) a` and passes the function `g` to `f`, a type error ("Application type mismatch").
The same term (`g a`) may appear twice in a proof. Placeholders: `(A B C : Prop) (f : B → C) (g : A → B) (a : A)`.

| Before | After `f (g _)` |
|---|---|
| `f : B → C`, `g : A → B`, `a : A` · expects `C` | the hole expects `A` |

**W3.** `fun hb => ⟨h.2 hb, hb⟩ : B → A ∧ B` from `h : A ↔ B`: R1, R2, then R7 read right to left for the first
component.

---

## Traps

- `by` is banned on purpose, comments excepted: every proof must be a term. The checker matches the word `by`
  anywhere outside comments, so no `by` inside a term either.
- `→` and `∧` both nest to the right. `A → B → C` takes `A` first; `A ∧ B ∧ C` is `A ∧ (B ∧ C)`, so its third
  component is `h.2.2`, not `h.3` (there is no `h.3`).
- Arguments go in the order of the function's premises, whatever order you named the hypotheses in.
- `f g a` is not `f (g a)` (R8).
- `h.1` means different things by type: for `h : A ∧ B` it is a proof of `A`; for `h : A ↔ B` it is a function
  `A → B` that still needs its argument.
- `_` in a pattern hides the component (`right✝`): name it if you need it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `A → B` (tactic: `intro h`) | `fun h => e` | R1 |
| prove `A ∧ B` (tactic: `constructor`) | `⟨ha, hb⟩` | R2 |
| prove `A ∧ B → G`, splitting the pair (tactic: `intro ⟨ha, hb⟩`) | `fun ⟨ha, hb⟩ => e` | R3 |
| prove `A → B → C → G` (tactic: `intro h1 h2 h3`) | `fun h1 h2 h3 => e` | R4 |
| use `f : A → B → C` (tactic: `exact f a b`) | `f a b` | R5 |
| a component of `h : A ∧ B` | `h.1` / `h.2` | R6 |
| use `h : A ↔ B` forwards / backwards | `h.1 a` / `h.2 b` | R7 |
| an argument that is an application | `f (g a)` | R8 |
| see what a spot expects | write `_` there and read the error | |
