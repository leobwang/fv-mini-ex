# E086 · Strings and chars: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide`, `unfold`, `rw`, `exact`, and
`List` with `++`. **New here:** core Lean's `String` and `Char`, the bridge `String.toList` from a
string to its list of characters, and `List.countP` (count with a `Bool` test). No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `p : α → Bool` is any `Bool`-valued
  test on `α` (for `α = Char`: `Char.isDigit`, `Char.isUpper`, …).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `"abc"` | a `String` literal. A `String` is UTF-8 bytes, **not** a `List Char` |
| `'a'` | a `Char` literal: one Unicode character |
| `s ++ t` | concatenation (of strings, or of lists) |
| `s.length` | number of characters of `s` (`String.length`), not bytes |
| `s.toList` | the characters of `s` as a `List Char` (`String.toList`) |
| `String.singleton c` | the one-character string made of `c` |
| `c.toNat` | the Unicode code point of `c`, a `Nat` (`'a'.toNat = 97`) |
| `c.isDigit` | `Char.isDigit c : Bool`, `true` exactly for `'0'`…`'9'` |
| `List.countP p l` | how many entries `x` of `l` have `p x = true`; you may write it `l.countP p` |
| `[c]` | the one-element list |
| `if c.isDigit = true then 1 else 0` | how Lean prints `if c.isDigit then 1 else 0`: a `Bool` `b` used as a `Prop` means `b = true` |

---

## Part 1 · `countDigits`

Statement: write `countDigits (s : String) : Nat`, the number of characters of `s` that are digits.
It is one term: turn `s` into a list (R2), count with `Char.isDigit` (R3).

**R2 · `String.toList`** is a function, not a step: `s.toList : List Char` is the list of characters of
`s`. The whole `List` library then applies. On a literal, `decide` evaluates it and **closes** the goal.

| Before | After `decide` |
|---|---|
| `⊢ ("h" ++ "i").toList = ['h', 'i']` | no goals |

**R3 · `List.countP p l`** is a function: `List.countP : (α → Bool) → List α → Nat` counts the entries `x`
of `l` with `p x = true`. Placeholders: `{α : Type} (p : α → Bool) (l : List α)`. A `Char` test such as
`Char.isUpper : Char → Bool` is a valid `p`. On literals, `decide` **closes** the goal.

| Before | After `decide` |
|---|---|
| `⊢ List.countP Char.isUpper "aBcD".toList = 2` | no goals |

## Part 2 · `lit_facts`

Statement: `"hello".length = 5`, `'a'.toNat = 97` and `'7'.isDigit = true`, all three at once.

**R1 · `decide` on literals** **closes** the goal. Every function in it (`String.length`, `Char.toNat`,
`Char.isDigit`, `∧` of decidable equations) computes on literals, so `decide` evaluates the statement
to `true`. No splitting needed.

| Before | After `decide` |
|---|---|
| `⊢ "ab".length = 2 ∧ 'b'.toNat = 98 ∧ 'x'.isDigit = false` | no goals |

## Part 3 · `toList_lit`

Statement: the list of characters of `"abc"` is `['a', 'b', 'c']`. A literal computation: R2 with `decide`.

## Part 4 · `countDigits_lit`

Statement: `countDigits "a1b22" = 3`. A literal computation once Part 1 is written: `decide` unfolds
your `countDigits` and evaluates it (R1, R3). If `decide` fails here, check your definition first.

## Part 5 · `countDigits_singleton`

Statement: for any character `c`, `countDigits (String.singleton c)` is `1` if `c` is a digit, else `0`.
`c` is a variable, so `decide` cannot evaluate this: unfold (R4), go to lists (R5), use the list lemma (R6).

**R4 · `unfold f`** changes the **goal**: the defined name `f` applied to its arguments is replaced by
its body. Placeholders: the guide's own `def twice (s : String) : String := s ++ s`, `(P : String → Prop)`.

| Before | After |
|---|---|
| `⊢ P (twice s)` | `⊢ P (s ++ s)` |

**R5 · `rw [String.toList_singleton]`** changes the **goal**. The lemma is
`String.toList_singleton (c : Char) : (String.singleton c).toList = [c]`. Placeholders: `(c : Char)`,
`(P : List Char → Prop)`.

| Before | After |
|---|---|
| `⊢ P (String.singleton c).toList` | `⊢ P [c]` |

**R6 · `rw [List.countP_singleton]`** changes the **goal**. The lemma is
`List.countP_singleton : List.countP p [a] = if p a = true then 1 else 0`. Placeholders:
`{α : Type} (p : α → Bool) (a : α)`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (List.countP p [a])` | `⊢ P (if p a = true then 1 else 0)` |

## Part 6 · `countDigits_append`

Statement: `countDigits (s ++ t) = countDigits s + countDigits t`. Unfold (R4, all three occurrences at
once), go to lists (R7), split the count (R8).

**R7 · `rw [String.toList_append]`** changes the **goal**. The lemma is
`String.toList_append : (s ++ t).toList = s.toList ++ t.toList` (`s t` implicit). Placeholders:
`(s t : String)`, `(P : List Char → Prop)`.

| Before | After |
|---|---|
| `⊢ P (s ++ t).toList` | `⊢ P (s.toList ++ t.toList)` |

**R8 · `rw [List.countP_append]`** changes the **goal**. The lemma is
`List.countP_append : List.countP p (l₁ ++ l₂) = List.countP p l₁ + List.countP p l₂`. Placeholders:
`{α : Type} (p : α → Bool) (l₁ l₂ : List α)`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (List.countP p (l₁ ++ l₂))` | `⊢ P (List.countP p l₁ + List.countP p l₂)` |

**W1 (not the exercise's object).** R7 followed by another list lemma,
`List.length_append : (l₁ ++ l₂).length = l₁.length + l₂.length`:

```lean-goal
⊢ (s ++ t).toList.length = s.toList.length + t.toList.length
⊢ (s.toList ++ t.toList).length = s.toList.length + t.toList.length
```

The second `rw` makes both sides identical and closes the goal by itself.

## Part 7 · `countDigits_le`

Statement: `countDigits s ≤ s.length`. After R4 the left side is about `s.toList` but the right side is
`s.length`. Rewrite the right side into a list length (R9, right to left), then the list fact (R10).

**R9 · `rw [← String.length_toList]`** changes the **goal**. The lemma is
`String.length_toList : s.toList.length = s.length`; `←` uses it right to left, turning `s.length` into
`s.toList.length`. Placeholders: `(s : String)`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P s.length` | `⊢ P s.toList.length` |

**R10 · `exact List.countP_le_length`** **closes** the goal. The lemma is
`List.countP_le_length : List.countP p l ≤ l.length` (`p l` implicit, found from the goal).
Placeholders: `{α : Type} (p : α → Bool) (l : List α)`.

| Before | After |
|---|---|
| `⊢ List.countP p l ≤ l.length` | no goals |

---

## Traps

- A `String` is not a `List Char`: list lemmas do not apply to `s` itself. Go through `s.toList` (R5, R7, R9).
- `decide` only evaluates closed terms. With a variable `s` or `c` in the goal it fails; use R4 + `rw`.
- `simp` makes no progress on `List.countP Char.isDigit s.toList ≤ s.length`: it does not rewrite
  `s.length` into `s.toList.length`. Use R9 by hand.
- R9 goes right to left: the goal contains `s.length`, not `s.toList.length`, so plain
  `rw [String.length_toList]` finds nothing to rewrite.
- `rw` tries `rfl` after rewriting. When both sides become the same text the goal is already closed, and a
  further tactic fails with "no goals".
- `if c.isDigit then …` is shown as `if c.isDigit = true then …`: the same term, printed with the
  `Bool`-to-`Prop` coercion spelled out.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a literal fact about strings / chars | `decide` | R1 |
| characters of a string as a list | `s.toList` | R2 |
| count entries passing a `Bool` test | `l.countP p` | R3 |
| replace your definition by its body | `unfold countDigits` | R4 |
| `(String.singleton c).toList → [c]` | `rw [String.toList_singleton]` | R5 |
| `countP p [a] → if p a = true then 1 else 0` | `rw [List.countP_singleton]` | R6 |
| `(s ++ t).toList → s.toList ++ t.toList` | `rw [String.toList_append]` | R7 |
| `countP p (l₁ ++ l₂) → countP p l₁ + countP p l₂` | `rw [List.countP_append]` | R8 |
| `s.length → s.toList.length` | `rw [← String.length_toList]` | R9 |
| `countP p l ≤ l.length` | `exact List.countP_le_length` | R10 |
| see the state | infoview | |
