# M033 · Prefix sums: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rfl`, `simp`, `exact`, `have`, `rw`, `omega`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `match` and structural recursion (E002), induction
on `Nat` and on lists (E014, E015), `cases` on `Option` (E016, E032), `simp` (E010), `omega` (E011),
`List.map` (E024). E059 (indexing lists) helps but is not needed.
**New here:** a recursion that builds a list from the recursive result with `List.map`; indexing
`l[i]?`; `List.take` and `List.sum`; `induction … generalizing i` followed by `cases i`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, `P : Option α → Prop`, …). The step changes only
  what sits inside `P (…)`.
- Placeholders are written as Lean binders: `{α β : Type}` are any types, `(l t : List α)` lists,
  `(f : α → β)` a function, `(i n : Nat)` indices and bounds. In the exercise `α` is `Int`.
- The guide's function, not the exercise's: `marks l = [0, 1, …, l.length]`, defined by
  `| [] => [0] | _ :: t => 0 :: (marks t).map (· + 1)`. So `marks [7, 7, 7] = [0, 1, 2, 3]`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `List.map f l` | `l.map f`: `f` applied to every entry of `l` |
| `fun x => c + x` | the section `(c + ·)` as Lean prints it; `fun x_1 => x + x_1` when the name `x` is already taken |
| `l[i]?` | the entry of `l` at index `i` (from 0) as an `Option`: `some a` if `i < l.length`, else `none` |
| `Option.map f o` | `f` applied inside `some`: `Option.map f (some a) = some (f a)`, `Option.map f none = none` |
| `List.take i l` | the first `i` entries of `l` (all of `l` if `i ≥ l.length`) |
| `l.sum` | `List.sum l`, the sum of the entries; `[].sum = 0` |
| `[].length` | the length of the empty list, `0`; `simp` turns it into `0` |
| `(x :: t).length` | `t.length + 1` after `simp` (R5) |
| `i + 1` | the index after `cases i` in the `succ` case (Lean 4 prints `Nat.succ i` as `i + 1`) |
| `case cons.succ` | the goal for a non-empty list and a positive index |

---

## Part 1 · `prefixSums`

Statement: write the body of `prefixSums : List Int → List Int` so that entry `i` is the sum of the
first `i` entries of the input: `prefixSums [1, 2, 3] = [0, 1, 3, 6]`, one entry more than the
input. Recursion: the prefix sums of `x :: xs` are `0` followed by the prefix sums of `xs`, each
plus `x`.

**R1 · `match l with | [] => … | x :: t => … (f t) …`** **closes** a test goal once the function is
defined. One arm per list constructor, the recursive call on the tail `t`, so Lean accepts it by
structural recursion with no `termination_by`, and the function computes: `rfl` tests it. An unused
pattern variable is written `_`. Placeholders: `(l : List Nat)`, `t : List Nat` bound by the pattern.

| Before | After |
|---|---|
| `⊢ marks [7, 7, 7] = [0, 1, 2, 3]` | closed by `rfl` |

**R2 · `List.map f l` with the section `(c + ·)`** **closes** a test goal. `(c + ·)` is notation for
`fun x => c + x`; `List.map` applies it to every entry. Placeholders: `(c : Int) (l : List Int)`.

| Before | After |
|---|---|
| `⊢ List.map (fun x => 10 + x) [1, 2, 3] = [11, 12, 13]` | closed by `rfl` |

---

## Part 2 · `prefixSums_length`

Statement: `(prefixSums xs).length = xs.length + 1`. Induction on `xs`; the `nil` case computes, the
`cons` case unfolds one step and uses the IH.

**R3 · `induction l with | nil => … | cons x t ih => …`** changes the **goal list**: one goal per list
constructor; `cons` names the head `x`, the tail `t` and the IH `ih` about `t`. Placeholders:
`{α : Type} (l : List α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `⊢ P l` | `⊢ P []`, `ih : P t ⊢ P (x :: t)` |

In the exercise the `nil` goal `(prefixSums []).length = [].length + 1` holds by computation: `rfl`.

**R4 · `simp only [f]`** changes the **goal**: naming a function defined by `match` gives `simp` one
equation per arm, so `f (x :: t)` is replaced by the `cons` arm's right-hand side. `simp [f, ih]`
does this and keeps going with R5, R6 and the IH. Placeholders: `(x : Nat) (t : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (marks (x :: t))` | `⊢ P (0 :: List.map (fun x => x + 1) (marks t))` |

**R5 · `List.length_cons`** changes the **goal**. The lemma is `(a :: as).length = as.length + 1`.
Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).length` | `⊢ P (l.length + 1)` |

**R6 · `List.length_map`** changes the **goal**. The lemma is `(List.map f as).length = as.length`:
`map` keeps the length. Placeholders: `{α β : Type} (f : α → β) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map f l).length` | `⊢ P l.length` |

**W1 · `marks` has one more entry.** `(marks l).length = l.length + 1` by R3, then `rfl` for `nil`
and `simp [marks, ih]` (R4, R5, R6, the IH) for `cons`.

| Before | After |
|---|---|
| `⊢ (marks l).length = l.length + 1` | closed |

---

## Part 3 · `prefixSums_get`

Statement: for `i ≤ xs.length`, `(prefixSums xs)[i]? = some (xs.take i).sum`: entry `i` exists and
is the sum of the first `i` inputs. The step from `xs` to `x :: xs` moves the index from `i + 1` to
`i`, so the IH must hold for every index (R7), and the index splits into `0` and `i + 1` (R10).

**R7 · `induction l generalizing i with …`** changes the **context**. `i`, and every hypothesis that
mentions it (here `h : i ≤ l.length`), is taken into the induction: each case gets its own `i` and
`h`, and the IH holds for all indices, `ih : ∀ (i : Nat), i ≤ t.length → P t i`. Without
`generalizing i`, `ih` would be about the single starting `i`, useless at index `i + 1`.
Placeholders: `{α : Type} (l : List α) (i : Nat) (h : i ≤ l.length) (P : List α → Nat → Prop)`.

| Before | After |
|---|---|
| `h : i ≤ l.length ⊢ P l i` | `h : i ≤ [].length ⊢ P [] i`, `h : i ≤ (x :: t).length ⊢ P (x :: t) i` (with `ih` as above) |

**R8 · `simp at h`** (empty list) changes the **context**: `[].length` is `0` (`List.length_nil`) and
`(i ≤ 0) = (i = 0)` (`Nat.le_zero_eq`). Placeholders: `{α : Type} (i : Nat)`.

| Before | After |
|---|---|
| `h : i ≤ [].length ⊢ P i` | `h : i = 0 ⊢ P i` |

**R9 · `subst h`** changes the **context and the goal**: with `h : i = 0`, the variable `i` is replaced
by `0` everywhere, and `i` and `h` leave the context. Placeholders: `(i : Nat) (h : i = 0)`.

| Before | After |
|---|---|
| `h : i = 0 ⊢ P i` | `⊢ P 0` |

In the exercise, after R8 and R9 the `nil` goal is `(prefixSums [])[0]? = some (List.take 0 []).sum`,
which computes: `rfl`.

**R10 · `cases i with | zero => … | succ i => …`** changes the **goal list**: index `0` and index
`i + 1`. Hypotheses about `i` are rewritten in each goal. Placeholders: `(n i : Nat) (h : i ≤ n)`.

| Before | After |
|---|---|
| `h : i ≤ n ⊢ P i` | `h : 0 ≤ n ⊢ P 0`, `h : i + 1 ≤ n ⊢ P (i + 1)` |

**R11 · `rfl` at index 0** **closes** the `zero` case. Both sides compute: `(a :: l)[0]?` is `some a`
(`List.getElem?_cons_zero`), `List.take 0 t` is `[]` (`List.take_zero`), `[].sum` is `0`
(`List.sum_nil`). Placeholders: `(l t : List Int)`.

| Before | After |
|---|---|
| `⊢ (0 :: l)[0]? = some (List.take 0 t).sum` | closed |

**R12 · `simp at h`** (non-empty list) changes the **context**: R5 turns `(x :: l).length` into
`l.length + 1`, then `+ 1` cancels (`Nat.add_le_add_iff_right`). `omega` cannot do this step itself:
it treats `(x :: l).length` as an unknown number. Placeholders: `{α : Type} (x : α) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `h : i + 1 ≤ (x :: l).length ⊢ P` | `h : i ≤ l.length ⊢ P` |

**R13 · `List.getElem?_cons_succ`** changes the **goal**. The lemma is `(a :: l)[i + 1]? = l[i]?`:
drop the head, lower the index. Placeholders: `{α : Type} (a : α) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a :: l)[i + 1]?` | `⊢ P l[i]?` |

**R14 · `List.getElem?_map`** changes the **goal**. The lemma is
`(List.map f l)[i]? = Option.map f l[i]?`: index first, then apply `f`. It is a `simp` lemma, so
`simp` applies it by itself; naming it in `simp […]` documents the step. Placeholders: `{α β : Type} (f : α → β) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.map f l)[i]?` | `⊢ P (Option.map f l[i]?)` |

**R15 · `ih i (by omega)`** changes the **context** (with `have hi := …`). After R7 the IH is a
function `ih : ∀ (i : Nat), i ≤ n → Q i`: give it the index and a proof of the bound; `(by omega)`
finds that proof in the context. The same term goes straight into `simp [ih i (by omega)]` or
`rw [ih i (by omega)]` as a rewrite rule. Placeholders: `(n i : Nat) (Q : Nat → Prop) (h : i ≤ n)`.

| Before | After |
|---|---|
| `h : i ≤ n ⊢ P` | `hi : Q i ⊢ P` |

**R16 · `Option.map_some`** changes the **goal**. The lemma is `Option.map f (some a) = some (f a)`.
Placeholders: `{α β : Type} (f : α → β) (a : α)`.

| Before | After |
|---|---|
| `⊢ P (Option.map f (some a))` | `⊢ P (some (f a))` |

**R17 · `List.take_succ_cons`** changes the **goal**. The lemma is
`List.take (i + 1) (a :: as) = a :: List.take i as`. Placeholders: `{α : Type} (a : α) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.take (i + 1) (a :: l))` | `⊢ P (a :: List.take i l)` |

**R18 · `List.sum_cons`** changes the **goal**. The lemma is `(a :: l).sum = a + l.sum`. Placeholders:
`{α : Type} [Add α] [Zero α] (a : α) (l : List α)`: `α` has `+` and `0`, as `Nat` and `Int` do.

| Before | After |
|---|---|
| `⊢ P (a :: l).sum` | `⊢ P (a + l.sum)` |

**W2 · one index step of `marks`, rewrite by rewrite.** With `ih : (marks t)[i]? = some i`: R4, R13,
R14, `rw [ih]`, R16 (the last `rw` closes the goal by `rfl`).

```lean-goal
⊢ (marks (x :: t))[i + 1]? = some (i + 1)
⊢ (0 :: List.map (fun x => x + 1) (marks t))[i + 1]? = some (i + 1)
⊢ (List.map (fun x => x + 1) (marks t))[i]? = some (i + 1)
⊢ Option.map (fun x => x + 1) (marks t)[i]? = some (i + 1)
⊢ Option.map (fun x => x + 1) (some i) = some (i + 1)
```

In the exercise the same chain, `rw [ih i (by omega)]` in place of `rw [ih]`, then R17, R18 on the
right-hand side, makes both sides `some (x + (List.take i xs).sum)`; one
`simp [prefixSums, List.getElem?_map, ih i (by omega)]` does all of it. If you run `simp [prefixSums]`
without the IH, it unfolds both sides, cancels the common `x +` under `some`, and stops at exactly
the IH at `i`: the goal `(prefixSums xs)[i]? = some (List.take i xs).sum`. Then
`exact ih i (by omega)` (R15) finishes.

**W3 · a sum over a `take` of a `cons`.** R17 then R18, twice (the literal `2` matches `i + 1`):

```lean-goal
⊢ (List.take 2 (a :: b :: l)).sum = a + b
⊢ (a :: List.take 1 (b :: l)).sum = a + b
⊢ a + (List.take 1 (b :: l)).sum = a + b
⊢ a + (b :: List.take 0 l).sum = a + b
⊢ a + (b + (List.take 0 l).sum) = a + b
```

`simp` then clears `List.take 0 l` (`[]`), `[].sum` (`0`) and `b + 0`.

---

## Traps

- Without `generalizing i`, the IH is about the one fixed `i`; the `cons` step needs it at a
  different index and gets stuck. Write `induction xs generalizing i with`.
- `h : i ≤ xs.length` mentions `i`, so `generalizing i` takes it along: in each case `h` is about that
  case's list, and the IH asks for the bound as an argument (`ih i (by omega)`, R15).
- `omega` does not know `(x :: xs).length = xs.length + 1`. Run `simp at h` first (R12), then
  `by omega` can prove `i ≤ xs.length`.
- `simp` rewrites with the IH only if you hand it the instance: `simp [ih]` cannot use
  `ih : ∀ (i : Nat), i ≤ xs.length → …` unless it can prove the bound itself; pass `ih i (by omega)`.
- In the `nil` case, `subst h` needs `h : i = 0` with the variable on one side; `simp at h` gives
  exactly that (R8).
- The definition's arm for `x :: xs` must recurse on `xs` and shift by `x`; shifting by anything that
  is not the head (or forgetting the leading `0`) breaks the length theorem or the index theorem.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define a list from the recursive result | `match xs with \| [] => … \| x :: xs => … (f xs).map (x + ·)` | R1, R2 |
| test the definition | `example : f [1, 2, 3] = [0, 1, 3, 6] := by rfl` | R1 |
| induct on a list | `induction xs with \| nil => … \| cons x xs ih => …` | R3 |
| unfold `f (x :: t)` | `simp only [f]` / `simp [f, …]` | R4 |
| `(a :: l).length`, `(l.map f).length` | `simp` (`List.length_cons`, `List.length_map`) | R5, R6 |
| IH for every index | `induction xs generalizing i with …` | R7 |
| `i ≤ [].length` → `i = 0` | `simp at h` | R8 |
| replace `i` by `0` | `subst h` | R9 |
| split the index | `cases i with \| zero => … \| succ i => …` | R10 |
| index `0` of a `cons` | `rfl` | R11 |
| `i + 1 ≤ (x :: l).length` → `i ≤ l.length` | `simp at h` | R12 |
| `(a :: l)[i + 1]?` → `l[i]?` | `List.getElem?_cons_succ` | R13 |
| `(l.map f)[i]?` → `Option.map f l[i]?` | `List.getElem?_map` | R14 |
| use the IH at index `i` | `ih i (by omega)` | R15 |
| `Option.map f (some a)` → `some (f a)` | `Option.map_some` | R16 |
| `take (i + 1) (a :: l)` → `a :: take i l` | `List.take_succ_cons` | R17 |
| `(a :: l).sum` → `a + l.sum` | `List.sum_cons` | R18 |
| see the state | infoview | |
