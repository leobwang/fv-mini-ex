# E009 · Rewriting: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E008: `theorem`/`example`, tactic mode `by`, `exact` (E003), `rfl` (E001), the
connectives `∧ ∨ ¬`.
**New here:** rewriting. An equation `e : l = r` is a tool for changing a goal: `rw [e]` finds `l` in the goal
and replaces it by `r`. The equation can be a hypothesis (`h : a = b`) or a library lemma
(`Nat.add_zero`, `Nat.add_comm`, `List.length_append`). Variants: right to left (`rw [← e]`), several in a
row (`rw [e₁, e₂]`), and on a hypothesis instead of the goal (`rw [e] at k`). No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : Nat → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `P : α → α → Prop` has two holes.
- `{α : Type}` is any type (`Nat`, `Bool`, `List Nat`, …). A hypothesis `k` only finishes the example.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## How `rw` works

`rw [e]` with `e : l = r`:

1. If `e` has arguments left open (`Nat.add_comm : ∀ n m, n + m = m + n` with none given), `rw` scans the
   goal for the **first** term of the shape `l` and fixes the arguments from it.
2. It replaces **every** occurrence of that one instantiated `l` by `r`. Other instances of the shape (a
   different sum) are left alone.
3. It tries `rfl` with only *reducible* definitions unfolded. If the goal is now `t = t` it is closed.

It fails with `Did not find an occurrence of the pattern` when `l` does not appear literally: `rw` matches
syntax (up to instances), not meaning. `a + 0` and `a` are different text.

## Reading the goals

| You see | It means |
|---|---|
| `h : a = b` | a hypothesis that `a` equals `b`; `rw [h]` turns `a` into `b` |
| `← h` | `h` used right to left (`\l` or `\leftarrow`, or write `<-`) |
| `xs ++ ys` | list `xs` followed by list `ys` (append) |
| `xs.length` | `List.length xs`, the number of elements |
| `[7]`, `[x]` | the one-element list; `[7].length` computes to `1` |
| `P (as ++ bs).length` | `P` applied to `(as ++ bs).length`: Lean prints no extra parentheses |
| `b + c + a` | `(b + c) + a`: `+` groups to the left, so `a + (b + c)` keeps its parentheses |
| `f a` | the function `f` applied to `a` |
| `f : Nat → Nat` | `f` is a function from `Nat` to `Nat` |
| `h₁`, `h'` | ordinary hypothesis names (`h\1` types `h₁`); the subscript and the prime mean nothing |

---

## Part 1 · `rw_chain`

Statement: from `h1 : a = b + 1` and `h2 : b = c`, prove `a = c + 1` (all `Nat`). Rewrite `a` away with
`h1`, then `b` with `h2`, in one `rw` list (R1, R2); `rw` closes the result itself (R3).

**R1 · `rw [h]`** changes the **goal**: with `h : a = b`, every `a` becomes `b`. Placeholders:
`{α : Type} (a b : α) (P : α → Prop) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ P a` | `h : a = b ⊢ P b` |

**R2 · `rw [h₁, h₂]`** changes the **goal**: the same as `rw [h₁]` then `rw [h₂]`; `h₂` acts on the goal `h₁`
produced. Placeholders: `{α : Type} (a b c d : α) (P : α → α → Prop) (h₁ : a = b) (h₂ : c = d)`.

| Before | After |
|---|---|
| `h₁ : a = b, h₂ : c = d ⊢ P a c` | `⊢ P b d` |

**R3 · `rw` closes `t = t`** changes the **goal list**: after its last rewrite `rw` tries `rfl`, and when both
sides are identical the goal is gone. Writing `rfl` or `exact …` after that is an error (`no goals`).
Placeholders: `{α β : Type} (f : α → β) (a b : α) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ f a = f b` | no goals |

**W1** (R2, R3): `x = y * 2` and `z = y` give `x = z * 2`. After `h₁` the goal is `y * 2 = z * 2`; `h₂`
turns `z` into `y`, and `rw` closes `y * 2 = y * 2`.

| Step | State |
|---|---|
| start | `h₁ : x = y * 2, h₂ : z = y ⊢ x = z * 2` |
| `rw [h₁, h₂]` | no goals |

## Part 2 · `rw_back`

Statement: from `h : f a = b` and `h' : f a + 1 = 5`, prove `b + 1 = 5`. The goal has `b`, the hypothesis
`h'` has `f a`. `rw [h]` would look for `f a` in the goal and fail; use `h` right to left so `b` becomes
`f a` (R4), and the goal is now exactly `h'`.

**R4 · `rw [← h]`** changes the **goal**: with `h : a = b`, every `b` becomes `a`. Placeholders:
`{α : Type} (a b : α) (P : α → Prop) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ P b` | `h : a = b ⊢ P a` |

(The other route, `rw [h] at h'` (R5), turns `h'` into `b + 1 = 5`.)

## Part 3 · `rw_at`

Statement: from `h1 : a + 0 = b` and `h2 : b = c`, prove `a = c`. `h1` cannot rewrite `a` in the goal: its
left side is `a + 0`, which does not appear. Clean `h1` first with `Nat.add_zero` at the hypothesis
(R5, R6), then it is `a = b` and Part 1's pattern finishes (R2, R3).

**R5 · `rw [h] at k`** changes the **context**: hypothesis `k` is rewritten, the goal is untouched.
Placeholders: `{α : Type} (a b : α) (P : α → Prop) (h : a = b) (k : P a)`.

| Before | After |
|---|---|
| `k : P a ⊢ P b` | `k : P b ⊢ P b` |

**R6 · `Nat.add_zero`** changes whatever it is applied to (here the **context**, with `at k`). The lemma is
`Nat.add_zero : ∀ (n : Nat), n + 0 = n`; `rw` picks `n` from the first `_ + 0` it finds. Placeholders:
`(n : Nat) (P : Nat → Prop) (k : P (n + 0))`.

| Before | After `rw [Nat.add_zero] at k` |
|---|---|
| `k : P (n + 0) ⊢ P n` | `k : P n ⊢ P n` |

**W2** (R5, R6 with a list): `rw [Nat.add_zero, h] at k` with `h : n = m` rewrites `k` twice.

| Step | State |
|---|---|
| start | `h : n = m, k : P (n + 0) ⊢ P m` |
| `rw [Nat.add_zero, h] at k` | `h : n = m, k : P m ⊢ P m` |

## Part 4 · `rw_lemmas`

Statement: from `h : xs = ys ++ [7]`, prove `xs.length = 1 + ys.length`. Replace `xs` (R1), split the length
of the append (R7), and commute the sum so it reads `[7].length + ys.length` (R8). `rw` cannot close that, as
`[7].length` must be computed; `rfl` can (R10).

**R7 · `List.length_append`** changes the **goal**. The lemma is
`List.length_append : (as ++ bs).length = as.length + bs.length` for any `{α : Type} (as bs : List α)` (its
arguments are implicit: `rw` finds them). Placeholders: `{α : Type} (as bs : List α) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs).length` | `⊢ P (as.length + bs.length)` |

**R8 · `Nat.add_comm` (no arguments)** changes the **goal**. The lemma is
`Nat.add_comm : ∀ (n m : Nat), n + m = m + n`. With no arguments `rw` takes the first sum it meets and flips
every copy of that sum only. Placeholders: `(a b c d : Nat) (P : Nat → Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a + b) (c + d)` | `⊢ P (b + a) (c + d)` |

**R9 · `Nat.add_comm c d` (explicit arguments)** changes the **goal**: only `c + d` is flipped.
Placeholders as in R8.

| Before | After |
|---|---|
| `⊢ P (a + b) (c + d)` | `⊢ P (a + b) (d + c)` |

**R10 · `rfl`** **closes** an equation whose sides become equal once definitions are computed. `rw`'s own
`rfl` (R3) unfolds only *reducible* definitions, and `List.length` is not one, so after the rewrites a goal
such as `[7].length + n = 1 + n` stays open; the `rfl` tactic computes `[x].length` to `1` and closes it.
Placeholders: `{α : Type} (x : α) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ [x].length + n = 1 + n` | no goals |

**W3** (R7, R10): `rw [List.length_append]` leaves `[x].length` uncomputed.

| Step | State |
|---|---|
| start | `⊢ (as ++ [x]).length = as.length + 1` |
| `rw [List.length_append]` | `⊢ as.length + [x].length = as.length + 1` |
| `rfl` | no goals |

**W4** (R8 vs R9): in `a + (b + c)`, the whole left side is itself a sum `a + s` and is met before `b + c`, so
the bare lemma flips the outer sum:

| Step | State |
|---|---|
| start | `⊢ a + (b + c) = a + (c + b)` |
| `rw [Nat.add_comm]` | `⊢ b + c + a = a + (c + b)` (not what you wanted) |
| `rw [Nat.add_comm b c]` (instead) | no goals |

---

## Traps

- `rw [h]` with `h : l = r` needs `l` literally in the goal: `Did not find an occurrence of the pattern`
  means it is not there (often you need `← h`, or `at` a hypothesis).
- `rw` rewrites **every** occurrence of the instantiated `l`, not just one. To hit one sum among several,
  give the lemma its arguments (`Nat.add_comm c d`, R9).
- After a `rw` that closed the goal (R3), an extra `rfl` or `exact` fails with `no goals`. After one that did
  not (R10), you need it. Look at the infoview.
- `rw` only rewrites with equations (`=`) and iffs (`↔`), not with implications.
- `simp`, `simp_all`, `grind` and `omega` are banned here: every step is a `rw`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| replace `a` by `b` using `h : a = b` | `rw [h]` | R1 |
| several rewrites in a row | `rw [h₁, h₂]` | R2 |
| finish when both sides match | nothing: `rw` closes `t = t` | R3 |
| replace `b` by `a` using `h : a = b` | `rw [← h]` | R4 |
| rewrite a hypothesis `k` | `rw [h] at k` | R5 |
| `n + 0 → n` | `rw [Nat.add_zero]` | R6 |
| `(as ++ bs).length → as.length + bs.length` | `rw [List.length_append]` | R7 |
| `n + m → m + n`, first sum met | `rw [Nat.add_comm]` | R8 |
| flip one chosen sum | `rw [Nat.add_comm c d]` | R9 |
| close after computing `[x].length` | `rfl` | R10 |
| see the state | infoview | |
