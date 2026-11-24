# E059 · Indexing lists: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` and `decide` (E001), `rw` (E009),
`simp` (E010), `omega` (E011), `List` and `List.map`, `Option` (`some`, `none`). **New here:** core Lean's
indexing notation `xs[i]` (the `GetElem` class) with its three variants `xs[i]'p`, `xs[i]?`, `xs[i]!`; the
dependent `if h : c then … else …` (`dite`) and its lemmas `dif_pos`, `dif_neg`; the list lemmas
`List.getElem?_eq_getElem` and `List.getElem_map`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : Option α → Prop`, …). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type (`Nat` in the exercise). `[Decidable c]` says Lean can compute whether `c`
  holds, which `if` needs; `i < l.length` on `Nat` is decidable.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `l[i]` | `GetElem.getElem l i h`: entry `i` of `l`; the proof `h` is hidden in the display |
| `l[i]?` | `GetElem?.getElem? l i : Option α` |
| `(l.map (· * 2))[i]'(by simpa using h)` | entry `i` of the mapped list, with the bound proved by `simpa using h` (R10, R11) |
| `List.map (fun x => x * 2) l` | `l.map (· * 2)`: `(· * 2)` is shorthand for `fun x => x * 2` |
| `(List.map f xs)[n]` | entry `n` of `xs.map f` (as `P (List.map f xs)[n]`, the argument of `P`) |
| `if h : c then t h else e h` | `dite c t e`, a dependent `if`: `h : c` in the `then` branch, `h : ¬c` in the `else` branch |
| `¬0 < xs.length` | `¬(0 < xs.length)`: `¬` is printed without a space and binds looser than `<` |
| `inst✝ : Decidable c` | the unnamed instance argument `[Decidable c]` |
| `case refine_1`, `case refine_2` | the goals `refine` created, one per `?_` |

### The four ways to index a list

`xs[i]` needs a proof of `i < xs.length`: Lean will not let you read past the end. The variants differ in
who supplies that proof, or what happens without one. Lists are indexed from `0`.

| Form | Type | Bound proof | Out of range |
|---|---|---|---|
| `xs[i]` | `α` | found automatically (`get_elem_tactic`) from hypotheses such as `h : i < xs.length`, or by evaluation on a literal list | does not type-check |
| `xs[i]'p` | `α` | `p : i < xs.length`, given by you | does not type-check |
| `xs[i]?` | `Option α` | none needed | `none` (in range: `some xs[i]`) |
| `xs[i]!` | `α` | none needed | `default` (`0` for `Nat`), and a panic message at run time |

`[10, 20, 30][1]? = some 20`, `[10, 20, 30][7]? = none`, `[10, 20, 30][7]! = 0`.

---

## Part 1 · `safeGet` (a definition)

Statement: `safeGet (l : List Nat) (i : Nat) : Nat` returns entry `i` of `l`, or `0` when `i ≥ l.length`. You
write the body. Test `i < l.length` with a dependent `if` and use the name it gives you to index. The guide's
`headOr xs d` (entry `0`, or `d` for an empty list) has the same shape.

**R1 · `if h : c then … else …`** changes the **goal list and the context**. In a definition you write it as a
term; in tactic mode, `refine if h : c then ?_ else ?_` shows what each branch sees: two goals, the first with
`h : c`, the second with `h : ¬c`. The name `h` exists only inside the branches. Placeholders:
`{α : Type} (xs : List α) (d : α)`.

| Before | After |
|---|---|
| `⊢ α` | `h : 0 < xs.length ⊢ α`, `h : ¬0 < xs.length ⊢ α` |

**R2 · `xs[n]`** **closes** a goal `⊢ α` when the bound is in the context: `exact xs[n]` with
`h : n < xs.length`. `get_elem_tactic` finds `h` by itself. Placeholders: `{α : Type} (xs : List α) (n : Nat)
(h : n < xs.length)`.

| Before | After |
|---|---|
| `h : n < xs.length ⊢ α` | no goals |

## Part 2 · `lit_get`

Statement: `[10, 20, 30][1] = 20`. On a literal list the bound `1 < 3` is proved automatically, and the lookup
computes.

**R3 · `rfl`** **closes** a literal lookup: Lean evaluates `[a, b, c][k]` to the `k`-th entry.

| Before | After |
|---|---|
| `⊢ [5, 6, 7][2] = 7` | no goals |

## Part 3 · `lit_get?`

Statement: `[10, 20, 30][5]? = none`. Index `5` is out of range, so `?` gives `none` (no bound proof needed).

**R4 · `xs[k]?` with `rfl`** **closes** the goal: `xs[k]?` evaluates to `some xs[k]` in range and to `none`
out of range.

| Before | After |
|---|---|
| `⊢ [5, 6, 7][2]? = some 7 ∧ [5, 6, 7][9]? = none` | no goals |

## Part 4 · `safeGet_lt`

Statement: for `h : i < l.length`, `safeGet l i = l[i]`. Unfold `safeGet` and take the `then` branch.

**R5 · `unfold f`** changes the **goal**: `f x y` is replaced by `f`'s body with `x, y` substituted.
Placeholders: `headOr {α : Type} (xs : List α) (d : α) : α := if h : 0 < xs.length then xs[0] else d`,
`(P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (headOr xs d)` | `⊢ P (if h : 0 < xs.length then xs[0] else d)` |

**R6 · `rw [dif_pos hc]`** changes the **goal**: the `if` becomes its `then` branch. The lemma is
`dif_pos {c : Prop} [Decidable c] (hc : c) : (if h : c then t h else e h) = t hc`. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (t : c → α) (e : ¬c → α) (hc : c)`. `rw` then tries `rfl`, which closes
a goal such as `l[i] = l[i]` by itself.

| Before | After |
|---|---|
| `⊢ P (if h : c then t h else e h)` | `⊢ P (t hc)` |

**W1.** `unfold headOr` then `rw [dif_pos h]` proves `headOr xs d = xs[0]` from `h : 0 < xs.length`:

```lean-goal
⊢ headOr xs d = xs[0]
⊢ (if h : 0 < xs.length then xs[0] else d) = xs[0]
```

## Part 5 · `safeGet_ge`

Statement: for `h : l.length ≤ i`, `safeGet l i = 0`. Unfold, then take the `else` branch. Its lemma needs
`¬ i < l.length`, which is not `h` itself: prove it on the spot.

**R7 · `rw [dif_neg hnc]`** changes the **goal**: the `if` becomes its `else` branch. The lemma is
`dif_neg {c : Prop} [Decidable c] (hnc : ¬c) : (if h : c then t h else e h) = e hnc`. Placeholders: as R6,
with `(hnc : ¬c)`.

| Before | After |
|---|---|
| `⊢ P (if h : c then t h else e h)` | `⊢ P (e hnc)` |

**R8 · `omega`** **closes** `¬ n < m` given `m ≤ n` (it handles `¬` of a linear fact). Write it as the
argument, `dif_neg (by omega)`: Lean reads the needed `¬c` off the `if` in the goal, then `omega` proves it.
Placeholders: `(n m : Nat) (h : m ≤ n)`.

| Before | After |
|---|---|
| `h : m ≤ n ⊢ ¬n < m` | no goals |

**W2.** `unfold headOr` then `rw [dif_neg (by omega)]` with `h : xs.length = 0`:

```lean-goal
⊢ headOr xs d = d
⊢ (if h : 0 < xs.length then xs[0] else d) = d
```

## Part 6 · `get?_eq_some`

Statement: for `h : i < l.length`, `l[i]? = some (safeGet l i)`. First replace `safeGet l i` by `l[i]` with
the theorem `safeGet_lt` you proved in Part 4 (an earlier theorem is a rewrite rule like any hypothesis:
`rw [safeGet_lt l i h]`). What is left relates `?` to plain indexing.

**R9 · `List.getElem?_eq_getElem`** changes the **goal**. The lemma is
`List.getElem?_eq_getElem {l : List α} {i : Nat} (h : i < l.length) : l[i]? = some l[i]`. Use it with
`rw [List.getElem?_eq_getElem hn]`, or close `⊢ xs[n]? = some xs[n]` with `exact List.getElem?_eq_getElem hn`.
Placeholders: `{α : Type} (xs : List α) (n : Nat) (hn : n < xs.length) (P : Option α → Prop)`.

| Before | After |
|---|---|
| `⊢ P xs[n]?` | `⊢ P (some xs[n])` |

**W3.** `rw [headOr_pos xs d h]` (the theorem of W1), then R9:

```lean-goal
⊢ xs[0]? = some (headOr xs d)
⊢ xs[0]? = some xs[0]
```

## Part 7 · `get_map_double`

Statement: for `h : i < l.length`, `(l.map (· * 2))[i]'(by simpa using h) = l[i] * 2`. Entry `i` of the
doubled list is twice entry `i`. The `'(by simpa using h)` is the bound for the mapped list: `h` talks about
`l.length`, not `(l.map (· * 2)).length`, so `get_elem_tactic` alone does not find it (R10, R11). You only read
that part; the proof is R12.

**R10 · `xs[n]'p`** gives the bound proof yourself; with `'?_` it changes the **goal list**: the bound becomes
the goal. Placeholders: `{α β : Type} (f : α → β) (xs : List α) (n : Nat) (hn : n < xs.length)`.

| Before | After |
|---|---|
| `⊢ β` | `⊢ n < (List.map f xs).length` |

**R11 · `simpa using hn`** **closes** the bound goal. `simp` rewrites with
`List.length_map (f : α → β) : (List.map f as).length = as.length`, and the result is `hn`.

| Before | After |
|---|---|
| `hn : n < xs.length ⊢ n < (List.map f xs).length` | no goals |

**R12 · `List.getElem_map`** changes the **goal**. The lemma is
`List.getElem_map (f : α → β) {l : List α} {i : Nat} {h : i < (List.map f l).length} : (List.map f l)[i] = f l[i]`.
The bound proof is implicit, so any proof matches (all proofs of a `Prop` are equal). With `rw`, the result
`(fun x => x * 2) l[i]` is β-reduced and `rfl` closes the goal; as a term, `List.getElem_map _` closes it
directly (W4). Placeholders: `{α β : Type} (f : α → β) (xs : List α) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.map f xs)[n]` | `⊢ P (f xs[n])` |

---

## Traps

- `xs[i]` with no bound in sight fails with "failed to prove index is valid". Put `h : i < xs.length` in
  the context (a dependent `if`, R1), or pass it with `xs[i]'h`.
- A plain `if c then … else …` (no `h :`) does not give the branches a name for the fact: `l[i]` in the `then`
  branch then has no bound. Write `if h : i < l.length then … else …`.
- A dependent `if` is `dite`; a plain one is `ite`. Their lemmas differ: `dif_pos`/`dif_neg` for `if h : …`,
  `if_pos`/`if_neg` for plain `if`. The wrong one makes `rw` fail with "Did not find an occurrence of the pattern".
- `dif_neg` needs `¬ i < l.length`, not `l.length ≤ i`. They are equivalent on `Nat`, but `rw` needs the exact
  form: produce it with `(by omega)`.
- `rw [dif_pos h]` before `unfold safeGet` fails: the `if` is not visible until the body is.
- `xs[i]!` is not `xs[i]?`: `!` returns `default` (and panics when the program runs), `?` returns an `Option`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| branch on a fact and keep its proof | `if h : c then … else …` | R1 |
| index with the bound in context | `xs[i]` | R2 |
| a literal lookup `[a, b, c][k]` or `[…][k]?` | `rfl` | R3, R4 |
| expose a definition's body | `unfold f` | R5 |
| take the `then` branch | `rw [dif_pos hc]` | R6 |
| take the `else` branch | `rw [dif_neg (by omega)]` | R7, R8 |
| `xs[i]?` → `some xs[i]` | `rw [List.getElem?_eq_getElem h]` / `exact …` | R9 |
| give the bound yourself | `xs[i]'h`, `xs[i]'(by simpa using h)` | R10, R11 |
| entry of a mapped list | `List.getElem_map _` / `rw [List.getElem_map]` | R12 |
| reuse an earlier theorem | `rw [thm args]` | TACTIC_STATES |
| see the state | infoview | |
