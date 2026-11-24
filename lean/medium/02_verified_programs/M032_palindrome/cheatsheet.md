# M032 · Palindrome: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `Bool` vs `Prop`, `intro`, `exact`, `rw`,
`simp`, `omega`, lists. **New here:** `==` on lists and the lemma that turns it into `=`; optional
indexing `l[i]?`; the core `List` lemmas about `reverse`, `getElem?` and list extensionality; `conv`
to rewrite one side of an equation; `by_cases`. Core Lean only, no Mathlib.

## How to read an entry

Each entry is one tactic, one term construct, or one lemma used with `rw`/`simp`/`apply`. It says what
changes (**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[BEq α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `l.reverse` | `List.reverse l`: the entries of `l` in the opposite order |
| `a == b` | a `Bool` comparison (type class `BEq`); on `List Nat`, entry by entry |
| `isPal xs = true` | the `Bool` function returned `true`; a theorem about a `Bool` is stated this way |
| `l[i]?` | entry `i` of `l` (from 0) as an `Option`: `some x` if `i < l.length`, else `none` |
| `l.length - 1 - i` | `Nat` subtraction, which stops at 0 (`2 - 5 = 0`); it parses as `(l.length - 1) - i` |
| `∀ (i : Nat), i < n → Q i` | how the infoview prints `∀ i < n, Q i` |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` |
| `case pos`, `case neg` | the two goals of `by_cases`: the condition holds / fails |
| `hi : ¬i < n` | the negated bound; `omega` reads it as `n ≤ i` |
| `\| e` (cursor inside `conv => …`) | `conv` mode: the part `e` of the goal you are focused on; after `lhs` it is the left side only (R7) |

---

## Part 1 · `isPal`

Statement: write `isPal (xs : List Nat) : Bool`, returning `true` exactly for palindromes. Part 2 pins
the meaning down; the natural body is one comparison.

**R1 · `l.reverse`** is a **term**: `List.reverse l`, the list in the opposite order.
`[1, 2, 3].reverse = [3, 2, 1]` holds by `rfl`.

**R2 · `a == b`** is a **term** of type `Bool`. It needs `[BEq α]` (a `Bool`-valued equality test on
`α`); `Nat`, `Bool` and `List Nat` have one. `([1, 2] == [2, 1]) = false` holds by `rfl`. A `Bool` is
not a proposition: to prove something about it you state `… = true` (Part 2).

---

## Part 2 · `isPal_iff`

Statement: `isPal xs = true` holds exactly when `xs[i]? = xs[xs.length - 1 - i]?` for every `i < xs.length`:
the entry `i` from the left equals the entry `i` from the right.

The plan: unfold `isPal` and turn `==` into `=`, so the left side is the equation `xs = xs.reverse`;
then prove each direction with the reverse-indexing lemma R8.

### From `Bool` to `Prop`

**R3 · `simp only [f]`** changes the **goal**: it replaces `f x` by the body of `f`. Placeholders: the
guide's `def isNil (l : List Nat) : Bool := l == []`, `(l : List Nat) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (isNil l = true)` | `⊢ P ((l == []) = true)` |

**R4 · `beq_iff_eq`** changes the **goal**. The lemma is `beq_iff_eq : (a == b) = true ↔ a = b`; `simp only`
(or `rw`) replaces the left side by the right. Placeholders: `{α : Type} [BEq α] [LawfulBEq α] (a b : α)`.
`[LawfulBEq α]` says `==` agrees with `=`; `Nat`, `Bool` and `List Nat` qualify.

| Before | After |
|---|---|
| `⊢ P ((a == b) = true)` | `⊢ P (a = b)` |

R3 and R4 go in one call: `simp only [isNil, beq_iff_eq]` (W1).

### Two directions, bounded quantifiers

**R5 · `constructor`** on an `↔` changes the **goal list**: `A ↔ B` becomes `A → B` (case `mp`) and
`B → A` (case `mpr`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R6 · `intro h i hi`** changes the **goal and the context**: it takes the hypothesis, the index and its
bound off the front of the goal. `∀ i < n, Q i` is `∀ i, i < n → Q i`, so it has two binders. Placeholders:
`(A : Prop) (n : Nat) (Q : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ A → ∀ (i : Nat), i < n → Q i` | `h : A, i : Nat, hi : i < n ⊢ Q i` |

### Rewriting one side only

**R7 · `conv => lhs; rw [h]`** changes the **goal**: it rewrites with `h : a = b` inside the left-hand side
only. `conv` enters a part of the goal, `lhs` picks the second-to-last argument (the left side of `x = y`,
or `x` in `R x y`), and `rw [h]` acts there. Plain `rw [h]` rewrites every `a` in the goal. Placeholders:
`(R : Nat → Nat → Prop) (a b : Nat) (h : a = b)`.

| Before | After `conv => lhs; rw [h]` | After plain `rw [h]` |
|---|---|---|
| `⊢ R a a` | `⊢ R b a` | `⊢ R b b` |

In the `mp` direction your `h` is `xs = xs.reverse`, and `xs` occurs three times in the goal. You want to
replace only the first.

### Indexing a list

**R8 · `List.getElem?_reverse`** changes the **goal**. The lemma is
`List.getElem?_reverse : i < l.length → l.reverse[i]? = l[l.length - 1 - i]?`; pass the bound:
`List.getElem?_reverse hi`. Use it with `rw`, or with `exact` when the goal is exactly this equation.
Placeholders: `{α : Type} (l : List α) (i : Nat) (hi : i < l.length)`.

| Before | After `rw [List.getElem?_reverse hi]` |
|---|---|
| `⊢ P l.reverse[i]?` | `⊢ P l[l.length - 1 - i]?` |

**R9 · `apply List.ext_getElem?`** changes the **goal**. The lemma is
`List.ext_getElem? : (∀ i, l₁[i]? = l₂[i]?) → l₁ = l₂`: lists are equal when they agree at every index,
in range (`some`) and out of range (`none`). Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ l₁ = l₂` | `⊢ ∀ (i : Nat), l₁[i]? = l₂[i]?` |

The new goal quantifies over **all** `i`, with no bound: follow with `intro i`, then split on the bound (R10).

**R10 · `by_cases hi : i < n`** changes the **goal list and the context**: two goals, case `pos` with
`hi : i < n` and case `neg` with `hi : ¬i < n`. Placeholders: `(n i : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hi : i < n ⊢ G`, `hi : ¬i < n ⊢ G` |

**R11 · `rw [h i hi]`** changes the **goal**. A hypothesis `h : ∀ i, i < n → l[i]? = m[i]?` is a function:
`h i hi` is its value at the index `i` and the bound `hi`, the equation `l[i]? = m[i]?`, and `rw` uses it.
Placeholders: `{α : Type} (l m : List α) (n i : Nat) (hi : i < n)`.

| Before | After |
|---|---|
| `⊢ P l[i]?` | `⊢ P m[i]?` |

**R12 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int`, using the hypotheses. It reads
`¬i < n` as `n ≤ i` and treats `l.length` as an unknown number. Example: `hi : ¬i < n` gives `n ≤ i`.

**R13 · `List.getElem?_eq_none`** changes the **goal**. The lemma is
`List.getElem?_eq_none : l.length ≤ i → l[i]? = none`. Write `rw [List.getElem?_eq_none (by omega)]`: `rw`
first finds the first `l[i]?` in the goal, left to right, then `by omega` proves `l.length ≤ i` for that
`l` and `i` (R12). Placeholders: `{α : Type} (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `hi : ¬i < l.length ⊢ P l[i]?` | `⊢ P none` |

**R14 · `List.length_reverse`** changes the **goal**. The lemma is `List.length_reverse : l.reverse.length = l.length`.
`simp` applies it by itself, so `(by simp; omega)` proves `l.reverse.length ≤ i` from `hi : ¬i < l.length`
(W3). Placeholders: `{α : Type} (l : List α)`.

| Before | After |
|---|---|
| `⊢ P l.reverse.length` | `⊢ P l.length` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: unfold and convert in one call.** `simp only [isNil, beq_iff_eq]` applies R3, then R4:

```lean-goal
⊢ P (isNil l = true)
⊢ P (l = [])
```

**W2: lists of equal length that agree below the length are equal.** With `hlen : l.length = m.length`
and `h : ∀ i, i < l.length → l[i]? = m[i]?`: `apply List.ext_getElem?` (R9), `intro i`, then
`by_cases hi : i < l.length` (R10):

```lean-goal
⊢ l = m
⊢ ∀ (i : Nat), l[i]? = m[i]?
⊢ l[i]? = m[i]?
```

In range, `rw [h i hi]` (R11) closes it (`rw` tries `rfl`). Out of range,
`rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]` (R13 twice) turns both sides
into `none`; the second `omega` needs `hlen`.

**W3: a bound on a reversed list.** The side goal is `l.reverse.length ≤ i`; `simp` turns it into
`l.length ≤ i` (R14), then `omega` (R12):

```lean-goal
⊢ l.reverse[i]? = none
```

is closed by `rw [List.getElem?_eq_none (by simp; omega)]`.

---

## Traps

- `rw [h]` with `h : xs = xs.reverse` rewrites **every** `xs`, including the one in `xs.length` and the
  one on the right. Use `conv => lhs; rw [h]` (R7).
- After `apply List.ext_getElem?` the index has **no** bound. The out-of-range case is real: both sides
  must become `none` (R13), and each needs its own `length ≤ i` proof.
- `l.length - 1 - i` is `Nat` subtraction: it stops at 0, so `(n - 1) - i + i = n - 1` fails when
  `i > n - 1`. `omega` handles truncated subtraction; reason about it with `omega`, not by hand.
- `(xs == ys) = true` is not `xs = ys` as text. Convert it with `beq_iff_eq` (R4) before using it as an
  equation.
- `t1 ; t2` runs `t2` on the first goal only. After `constructor` or `by_cases`, focus each goal with `·`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| reverse a list | `l.reverse` | R1 |
| compare two lists, as a `Bool` | `a == b` | R2 |
| unfold a definition | `simp only [f]` | R3 |
| `(a == b) = true` → `a = b` | `simp only [beq_iff_eq]` | R4 |
| split `A ↔ B` | `constructor` | R5 |
| take `h`, `i`, `i < n` off the goal | `intro h i hi` | R6 |
| rewrite the left side only | `conv => lhs; rw [h]` | R7 |
| `l.reverse[i]?` → `l[l.length - 1 - i]?` | `List.getElem?_reverse hi` | R8 |
| list equality → every index | `apply List.ext_getElem?` | R9 |
| split on the bound | `by_cases hi : i < n` | R10 |
| use `h : ∀ i, i < n → …` at `i` | `rw [h i hi]` | R11 |
| linear arithmetic, `¬i < n` → `n ≤ i` | `omega` | R12 |
| out of range → `none` | `rw [List.getElem?_eq_none (by omega)]` | R13 |
| `l.reverse.length` → `l.length` | `simp` (`List.length_reverse`) | R14 |
| see the state | infoview | |
