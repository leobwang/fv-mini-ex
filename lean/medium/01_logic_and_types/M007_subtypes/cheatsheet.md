# M007 · Subtypes: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `abbrev`, structures and anonymous constructors
`⟨_, _⟩`, `have`, `simp`, `rfl`, `omega`. **New here:** subtypes `{n : Nat // P n}` (a value packed with a
proof about it), their projections `.val` and `.property`, and `Subtype.ext` for equality of such values.
Core Lean only, no Mathlib.

## The objects

- **`EvenNat := {n : Nat // n % 2 = 0}`**: an even natural. A value `a : EvenNat` is a pair `⟨n, h⟩` of a
  number `n` and a proof `h : n % 2 = 0`. `a.val` is the number, `a.property` the proof. It is an `abbrev`, so
  Lean treats `EvenNat` and the subtype as the same type.
- **`half a := a.val / 2`** (given): a plain `Nat`.
- **Holes:** two definitions, `addE a b : EvenNat` (the sum) and `ofHalf k : EvenNat` (the number `2 * k`),
  and four theorems: `(addE a b).val = a.val + b.val`, `(ofHalf k).val = 2 * k`,
  `half (addE a b) = half a + half b`, `ofHalf (half a) = a`.
- The guide teaches on the toy subtype `Pos := {n : Nat // 0 < n}` with `double`, `pred`, `succPos`. They are
  **not** the exercise's objects.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means the goal is closed.
- `P`, `R` are "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. In the subtype entries `P : α → Prop` is the predicate of the subtype.
- Placeholders are written as Lean binders: `{α : Type}` is any type, `(P : α → Prop)` any predicate on it,
  `(x : {a : α // P a})` a value of the subtype.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{ a // P a }` | the subtype: values `a` of the base type with a proof of `P a` (input syntax `{a : α // P a}`) |
| `⟨v, hv⟩` | the subtype value with number `v` and proof `hv : P v` |
| `x.val` | the underlying value of `x` (`Subtype.val x`; also written `x.1`, or `↑x` when Lean inserts it as a coercion) |
| `x.property` | the proof `P x.val` stored in `x` (also `x.2`) |
| `⟨v, hv⟩.val` | a projection of a constructor: computes to `v` (R4, R5) |
| `this : …` | the name `have := e` gives a fact when you do not name it |
| `this✝ : …` | an earlier `this`, shadowed by a newer one (two `have :=` in a row). Still usable by `omega`; name facts (`have ha := …`) to refer to them |
| `n % 2`, `n / 2` | remainder and floor division on `Nat`: `7 % 2 = 1`, `7 / 2 = 3` |

---

## Part 1 · `addE`

Statement: a definition `addE (a b : EvenNat) : EvenNat`, the sum of two even naturals. Give the number
`a.val + b.val` and a proof that it is even (R1). The proof needs the evenness of `a` and `b` (R2) and
arithmetic with `%` (R3).

**R1 · `⟨v, h⟩` (tactic form `refine ⟨v, ?_⟩`)** changes the **goal**: to build a subtype value, give the value
`v`; what is left is the proof obligation `P v`. In a `def` body write `⟨v, by tac⟩`, and the `by` block sees
exactly that obligation. Placeholders: `{α : Type} (P : α → Prop) (v : α) (hv : P v)`.

| Before | After `refine ⟨v, ?_⟩` |
|---|---|
| `⊢ { a // P a }` | `⊢ P v` |

**R2 · `have h := x.property`** changes the **context**: it adds the proof stored inside `x`, stated about
`x.val`. The goal stays the same. Placeholders: `{α : Type} (P : α → Prop) (x : {a : α // P a}) (G : Prop)`.
`have := x.property` (no name) calls it `this`.

| Before | After |
|---|---|
| `⊢ G` | `h : P x.val ⊢ G` |

**R3 · `omega`** **closes** linear arithmetic over `Nat` and `Int`: `+`, truncated `-`, `*` by a numeral, `/` and
`%` by a numeral, with `=`, `≤`, `<`, `≠`, using the hypotheses in the context. It treats `a.val` as an unknown
number. Placeholders: `(n : Nat) (h : n % 3 = 0)`.

| Before | After |
|---|---|
| `h : n % 3 = 0 ⊢ 3 * (n / 3) = n` | `∅` |

In this Lean version (4.32) `omega` also adds `p.property` by itself for each `p.val` of a subtype it meets
(second example of R3), so it would succeed even without R2. Other tactics do not do this, and R2 makes the fact
visible in the infoview: the skeleton uses it.

| Before | After |
|---|---|
| `p : Pos ⊢ p.val ≠ 0` | `∅` |

## Part 2 · `ofHalf`

Statement: a definition `ofHalf (k : Nat) : EvenNat`, the even number `2 * k`. R1 with the value `2 * k`; the
obligation is arithmetic with no hypothesis (R3), like `succPos` in the guide.

## Part 3 · `addE_val`

Statement: `(addE a b).val = a.val + b.val`. Once `addE` is defined, the left side computes to the right side.

**R4 · `rfl`** **closes** an equation whose two sides compute to the same thing. `⟨v, hv⟩.val` computes to `v`,
and `rfl` unfolds definitions, so it also closes `.val` of a `def` whose body is an anonymous constructor.
As a term proof write `:= rfl` (no `by`). Placeholders: `{α : Type} (P : α → Prop) (v : α) (hv : P v)`, and
`(p : Pos)` with the toy `double`.

| Before | After |
|---|---|
| `⊢ ⟨v, hv⟩.val = v` | `∅` |
| `⊢ (double p).val = 2 * p.val` | `∅` |

## Part 4 · `ofHalf_val`

Statement: `(ofHalf k).val = 2 * k`. Same as Part 3: R4.

## Part 5 · `half_addE`

Statement: `half (addE a b) = half a + half b`. Unfold `half` and `addE` so the goal is arithmetic about
`a.val` and `b.val` (R5), then R3 with the evenness facts from R2. Without the evenness facts it is false for
plain numbers: `(1 + 1) / 2 ≠ 1 / 2 + 1 / 2`.

**R5 · `simp only [f]`** changes the **goal**: it replaces the name `f` by its body, and `simp` always reduces a
projection of a constructor, so `⟨v, hv⟩.val` becomes `v` in the same step. Placeholders: `(p : Pos)
(P : Nat → Prop)` with the toy `double`, `pred`; and `{α : Type} (P : α → Prop) (v : α) (hv : P v)
(R : α → Prop)` for the bare projection.

| Before | After |
|---|---|
| `⊢ P (double p).val` | `⊢ P (2 * p.val)` |
| `⊢ P (pred p)` | `⊢ P (p.val - 1)` |
| `⊢ R ⟨v, hv⟩.val` | `⊢ R v` |

**W1** in the guide chains R5 → R3 on `pred (double p) + 1 = 2 * p.val`:

```lean-goal
⊢ pred (double p) + 1 = 2 * p.val
⊢ 2 * p.val - 1 + 1 = 2 * p.val
```

## Part 6 · `ofHalf_half`

Statement: `ofHalf (half a) = a`, an equation between two `EvenNat` values. Reduce it to an equation between
their numbers (R6), then as in Part 5: R2, R5, R3.

**R6 · `apply Subtype.ext`** changes the **goal**: an equation between subtype values becomes an equation
between their `.val`s. The lemma is `Subtype.ext : a1.val = a2.val → a1 = a2`; the proofs inside never need
comparing, because any two proofs of the same `Prop` are equal (*proof irrelevance*). Placeholders:
`{α : Type} (P : α → Prop) (x y : {a : α // P a})`.

| Before | After |
|---|---|
| `⊢ x = y` | `⊢ x.val = y.val` |

**W2** in the guide runs the whole chain R6 → R2 → R5 → R3 on `succPos (pred p) = p`:

```lean-goal
⊢ succPos (pred p) = p
⊢ (succPos (pred p)).val = p.val
⊢ p.val - 1 + 1 = p.val
```

---

## Traps

- `⟨v, h⟩` needs the proof as its second component: `⟨a.val + b.val⟩` alone does not type-check. Write
  `⟨v, by tac⟩` and read the obligation in the infoview by putting the cursor inside the `by`.
- The `by` block inside `⟨v, by …⟩` sees `a` and `b` but not their proofs as hypotheses: `a.property` is a
  term you can use, not a hypothesis that is already there. Bring it in with `have := a.property` (R2).
  (`omega` in Lean 4.32 finds it by itself; `simp`, `exact`, `decide` do not.)
- `omega` does not unfold definitions: `half a` and `addE a b` are opaque to it. Unfold them first (R5).
- `simp only [half]` without `addE` leaves `(addE a b).val`; name every definition that stands between the goal
  and arithmetic.
- An equation `x = y` of subtype values is not arithmetic: `omega` fails on it. Use R6 first.
- `Nat` division rounds down: `n / 2 * 2 = n` only when `n % 2 = 0`, which is why the evenness facts matter.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build a subtype value | `⟨v, by omega⟩` (term) / `refine ⟨v, ?_⟩` (tactic) | R1 |
| the number inside `x` | `x.val` (`x.1`, `↑x`) | |
| the proof inside `x` as a hypothesis | `have h := x.property` (`x.2`) | R2 |
| `Nat` arithmetic with `+`, `-`, `*`, `/ 2`, `% 2` | `omega` | R3 |
| `.val` of a constructor or of a `def` building one | `rfl` (term: `:= rfl`) | R4 |
| unfold definitions, drop `⟨v, h⟩.val` | `simp only [f, g]` | R5 |
| `x = y` for subtype values | `apply Subtype.ext` | R6 |
| see the state | infoview | |
