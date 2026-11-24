# M022 · Linear search: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`intro`, `exact`, `rw`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, `Option`, `def` by pattern matching,
`if … then … else`, `induction`, `cases`, `simp`, `intro`, `exact`, `omega`. M001 (induction with
`generalizing`) helps but is not needed. **New here:** core Lean only (no Mathlib): a recursive
function that returns an `Option` and shifts the recursive answer with `Option.map`; list lookup
`xs[i]?`; taking apart a hypothesis `h : search k xs = …` with `simp … at h`, `split at h`, `subst`;
splitting on a recursive call with `cases hs : …`; and the core lemmas `List.getElem?_cons_zero`,
`List.getElem?_cons_succ`, `Option.map_none`, `Option.map_some`, `Option.map_eq_none_iff`,
`List.mem_cons`, `List.not_mem_nil`, `not_or`.

## The objects

- **`search k xs : Option Nat`** (you write it): `some i` where `i` is the index (from 0) of the first
  `k` in `xs`, or `none` if `k` does not occur. Recursion: on `[]` the answer is `none`; on `x :: xs`,
  a hit `x = k` gives `some 0`, a miss gives the tail's answer shifted by one, `(search k xs).map (· + 1)`.
- **Holes:** the body of `search`, and two theorems:
  `search_some`: `search k xs = some i → xs[i]? = some k ∧ ∀ j < i, xs[j]? ≠ some k` (correct and first);
  `search_none`: `search k xs = none → k ∉ xs`.
- Both theorems take a hypothesis `h` about `search` and the proof consists of unfolding `h` one step
  (`simp only [search] at h`) and splitting its `if` (`split at h`). In `search_some` the index `i` changes
  from call to call (`i` at the top, `i'` in the tail), so the induction must generalize `i`.
- The guide teaches on its own functions, **not** the exercise's: `len` (R1), `isZero` (R2) and
  `stepsDown k n` (R3), the number of steps `n, n - 1, …` takes to reach `k`, which recurses with the same
  `if … then some 0 else (…).map (· + 1)` shape.

## How to read an entry

Each entry is one tactic, one lemma used with `rw`/`simp`, or one term construct. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means the goal is closed.
- `P` is "the rest of your goal" (`P : Option α → Prop`, `P : Nat → Prop`, …). The step changes only the
  part inside `P (…)`. `G` is an arbitrary goal (`G : Prop`), used when a step acts on a hypothesis.
- Placeholders are written as Lean binders: `{α : Type}` is any element type; `(a b : Nat)`,
  `(l : List α)`, `(o : Option Nat)`, `(f : Nat → Nat)`, `(c : Prop) [Decidable c]` (a proposition with an
  algorithm deciding it, such as `x = k` on `Nat`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Option Nat`, `some i`, `none` | an optional number: present (`some i`) or absent (`none`) |
| `xs[i]?` | entry `i` of `xs` (from 0) as an `Option`: `some` if `i < xs.length`, else `none` |
| `[][i]?`, `(x :: xs)[0]?`, `(x :: xs)[i + 1]?` | lookup in the empty list (always `none`), the head (`some x`, R10), the tail (`xs[i]?`, R17) |
| `Option.map f o`, `o.map f` | `f` applied inside `some`: `some a ↦ some (f a)`, `none ↦ none` |
| `fun x => x + 1` | what `(· + 1)` prints as |
| `¬k ∈ xs` | `k ∉ xs` (`∉` is notation for `¬(· ∈ ·)` and prints unfolded) |
| `∀ (j : Nat), j < i → …` | what `∀ j < i, …` prints as |
| `h✝ : x = k` / `h✝ : ¬x = k` | the `if` condition after `split at h`; inaccessible, `simp_all` still uses it |
| `ih : ∀ (i : Nat), search k xs = some i → …` | the IH after `generalizing i`: for every index |
| `case cons.isFalse.some.succ` | list `x :: xs`, the `else` branch, the tail call returned `some i'`, `j = j' + 1` |

---

## Part 1 · `search`

Statement: the body of `def search (k : Nat) (xs : List Nat) : Option Nat`. The two theorems pin it down:
the result must be the first index of `k`, or `none`.

**R1 · `match xs with | [] => … | x :: xs => …`** is a **term**: a function defined by cases on the list.
The recursive call on the tail `xs` is accepted because it is structurally smaller. Each arm becomes one
equation `simp only [f]` can use (R6). Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `len [a, b]` | `2` (by `rfl`) |

**R2 · `if a = b then u else v`** is a **term**: a branch on `a = b`. `a = b` is a `Prop`, and the `if` is
allowed because equality on `Nat` is decidable. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `isZero 0`, `isZero 3` | `true`, `false` (by `rfl`) |

**R3 · `Option.map f o`** is a **term**: it applies `f` inside `some` and leaves `none` alone. `(· + 1)` is
`fun x => x + 1`, so `(search k xs).map (· + 1)` adds one to the tail's index, if there is one.
Placeholders: `(f : Nat → Nat) (a : Nat)`.

| Before | After |
|---|---|
| `Option.map f (some a)` | `some (f a)` |
| `Option.map f none` | `none` |
| `(some a).map (· + 1)` | `some (a + 1)` |

## Part 2 · `search_some`

Statement: if `search k xs = some i` then `xs[i]? = some k` (correct) and `xs[j]? ≠ some k` for every
`j < i` (first). Induct on `xs` generalizing `i`; in `cons` unfold `h` and split its `if`.

**R4 · `induction xs generalizing i with | nil => ?_ | cons x xs ih => ?_`** changes the **goal list and the
context**. `generalizing i` removes `i` (and `h`, which mentions it) from the context before inducting, so
the IH is `ih : ∀ (i : Nat), P xs i` (in the exercise: `ih : ∀ (i : Nat), search k xs = some i → …`), usable
at the tail's index `i'`. Placeholders: `{α : Type} (P : List α → Nat → Prop) (xs : List α) (i : Nat)`.

| Before | After (case `nil`) | After (case `cons`, plus `ih`) |
|---|---|---|
| `xs : List α, i : Nat ⊢ P xs i` | `i : Nat ⊢ P [] i` | `x : α, xs : List α, i : Nat ⊢ P (x :: xs) i` |

**R5 · `simp at h`** with `h : none = some a` (or `some a = none`) **closes** the goal: distinct constructors
are never equal, so `h` becomes `False`. Case `nil`: `simp [search] at h` unfolds `search k []` to `none`
and does this. Placeholders: `(a : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `h : none = some a ⊢ G` | `∅` |
| `h : some a = none ⊢ G` | `∅` |

**R6 · `simp only [f] at h`** changes the **context**: `h` is unfolded by one equation of `f`. It fires
only when the argument is literally a constructor (`x :: xs`, `n + 1`). In the exercise:
`simp only [search] at h`. Placeholders: `(k n : Nat) (o : Option Nat) (G : Prop)`.

| Before | After |
|---|---|
| `h : stepsDown k (n + 1) = o ⊢ G` | `h : (if n + 1 = k then some 0 else Option.map (fun x => x + 1) (stepsDown k n)) = o ⊢ G` |

**R7 · `split at h`** changes the **goal list and the context**: an `if` in `h` gives two goals, named
`isTrue` and `isFalse`, each with the condition as an inaccessible hypothesis `h✝` (`rename_i hc` names it
`hc`; `simp_all` uses it unnamed). Placeholders:
`(c : Prop) [Decidable c] (u v o : Option Nat) (G : Prop)`.

| Before | After (`isTrue`) | After (`isFalse`) |
|---|---|---|
| `h : (if c then u else v) = o ⊢ G` | `h✝ : c, h : u = o ⊢ G` | `h✝ : ¬c, h : v = o ⊢ G` |

**R8 · `simp at h`** with `h : some a = some b` changes the **context**: `h` becomes `a = b`
(`Option.some.injEq`: `some` is injective). In the hit case `h : some 0 = some i` becomes `h : 0 = i`.
Placeholders: `(a b : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `h : some a = some b ⊢ G` | `h : a = b ⊢ G` |

**R9 · `subst h`** with `h : a = i` and `i` a local variable changes the **context and the goal**: `i`
disappears and every `i` becomes `a`. Placeholders: `(a i : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : a = i ⊢ P i` | `⊢ P a` |

**R10 · `List.getElem?_cons_zero`** changes the **goal**. Statement: `(a :: l)[0]? = some a`. `simp` applies
it by itself. Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: l)[0]?` | `⊢ P (some a)` |

**R11 · `simp_all`** **closes** the goal by simplifying all hypotheses and the goal with each other. In the hit
case it rewrites with `h✝ : x = k`, applies R10, and knows `j < 0` is `False`. It also closes the `j = 0`
case later, `(x :: xs)[0]? ≠ some k` with `h✝ : ¬x = k`. Placeholders: `(x k : Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `hc : x = k ⊢ (x :: l)[0]? = some k ∧ ∀ (j : Nat), j < 0 → (x :: l)[j]? ≠ some k` | `∅` |

**R12 · `cases hs : e with | none => ?_ | some a => ?_`** changes the **goal list and the context**: one goal
per value of `e`, with `hs` recording which. It replaces `e` in the **goal** only; a hypothesis that mentions
`e` (your `h : Option.map … (search k xs) = some i`) keeps it, so rewrite it with `hs` next (R13, R14). In the
exercise `e` is `search k xs`. Placeholders: `(o : Option Nat) (P : Option Nat → Prop)`.

| Before | After (`none`) | After (`some`) |
|---|---|---|
| `⊢ P o` | `hs : o = none ⊢ P none` | `a : Nat, hs : o = some a ⊢ P (some a)` |

**R13 · `Option.map_none`** with `simp [hs] at h` **closes** the goal. Statement: `Option.map f none = none`.
`simp` rewrites `o` to `none` in `h` (by `hs`), applies this lemma, and is left with `none = some b` (R5).
Placeholders: `(f : Nat → Nat) (o : Option Nat) (b : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `hs : o = none, h : Option.map f o = some b ⊢ G` | `∅` |

**R14 · `Option.map_some`** with `simp [hs] at h` changes the **context**. Statement:
`Option.map f (some a) = some (f a)`; then R8 strips the `some`s. In the exercise `h` becomes `i' + 1 = i`,
and `subst h` (R9) puts `i' + 1` everywhere. Placeholders: `(f : Nat → Nat) (o : Option Nat) (a b : Nat)`.

| Before | After |
|---|---|
| `hs : o = some a, h : Option.map f o = some b ⊢ G` | `h : f a = b ⊢ G` |

**R15 · `obtain ⟨h1, h2⟩ := ih a hs`** changes the **context**: `ih a hs` is the IH at the index `a`, fed
the fact `hs`; the pattern splits the resulting `∧`. In the exercise: `ih i' hs`. Placeholders:
`(Q A B : Nat → Prop) (a : Nat) (hs : Q a) (ih : ∀ i, Q i → A i ∧ B i)`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : A a, h2 : B a ⊢ G` |

**R16 · `refine ⟨by tac, ?_⟩`** changes the **goal**: `tac` proves the left conjunct on the spot, the right
one stays as the next goal. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ B` |

**R17 · `List.getElem?_cons_succ`** changes the **goal**. Statement: `(a :: l)[i + 1]? = l[i]?`: dropping the
head lowers the index by one. `simp` applies it by itself. Placeholders: `{α : Type} (a : α) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a :: l)[i + 1]?` | `⊢ P l[i]?` |

**R18 · `simpa using e`** **closes** the goal: it simplifies both the goal and the type of `e` (here R17
fires on the goal) and closes the goal when they agree. In the exercise: `simpa using h1` for the first
conjunct, and `simpa using h2 j (by omega)` in the `succ` case. Placeholders: `{α : Type} (a b : α) (l : List α) (i : Nat)`.

| Before | After |
|---|---|
| `h1 : l[i]? = some b ⊢ (a :: l)[i + 1]? = some b` | `∅` |

**R19 · `cases j with | zero => ?_ | succ j => ?_`** changes the **goal list**: `j = 0` (closed by R11 in the
exercise) and `j = j' + 1` (shifted down by R17, then the IH). Use it after `intro j hj`. Placeholders:
`(P : Nat → Prop) (j : Nat)`.

| Before | After (`zero`) | After (`succ`) |
|---|---|---|
| `j : Nat ⊢ P j` | `⊢ P 0` | `j : Nat ⊢ P (j + 1)` |

**R20 · `e (by omega)`** is a **term**: an argument whose proof is a linear-arithmetic fact, proved in place.
`h2 j` needs `j < a`; `omega` gets it from `hj : j + 1 < a + 1`. Placeholders:
`(Q : Nat → Prop) (a j : Nat) (h2 : ∀ j, j < a → Q j)`.

| Before | After |
|---|---|
| `hj : j + 1 < a + 1 ⊢ Q j` | `∅` |

## Part 3 · `search_none`

Statement: if `search k xs = none` then `k ∉ xs`. Plain `induction xs` (no index to generalize); in `cons`
unfold `h`, split its `if`. The `isTrue` branch has `h : some 0 = none` (R5). In `isFalse`, `simp at h`
turns `Option.map … (search k xs) = none` into `search k xs = none` (R22), which is what `ih` needs.

**R21 · `List.not_mem_nil`** **closes** the goal. Statement: `a ∉ []`; plain `simp` uses it (case `nil`).
Placeholders: `(k : Nat)`.

| Before | After |
|---|---|
| `⊢ ¬k ∈ []` | `∅` |

**R22 · `Option.map_eq_none_iff`** changes the **context** (via `simp at h`). Statement:
`Option.map f o = none ↔ o = none`. Placeholders: `(f : Nat → Nat) (o : Option Nat) (G : Prop)`.

| Before | After |
|---|---|
| `h : Option.map f o = none ⊢ G` | `h : o = none ⊢ G` |

**R23 · `List.mem_cons`** changes the **goal**. Statement: `a ∈ b :: l ↔ a = b ∨ a ∈ l`. Placeholders:
`{α : Type} (a b : α) (l : List α) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P ¬a ∈ b :: l` | `⊢ P ¬(a = b ∨ a ∈ l)` |

**R24 · `not_or`** changes the **goal**. Statement: `¬(p ∨ q) ↔ ¬p ∧ ¬q`. `simp only [List.mem_cons, not_or]`
does R23 and R24 at once; in the exercise the goal becomes `¬k = x ∧ ¬k ∈ xs`. Placeholders: `(p q : Prop)`.

| Before | After |
|---|---|
| `⊢ P ¬(p ∨ q)` | `⊢ P (¬p ∧ ¬q)` |

**R25 · `exact ⟨fun hp => …, hq⟩`** **closes** `¬p ∧ q`. `¬p` is `p → False`, so its proof is a function:
given `hp : p`, derive `False`. In the exercise the left part is `fun hk => by simp_all` (with `hk : k = x`
and `h✝ : ¬x = k`, R11) and the right part is `ih h`. Placeholders: `(p q : Prop) (hnp : p → False) (hq : q)`.

| Before | After |
|---|---|
| `⊢ ¬p ∧ q` | `∅` |

### Worked combinations (on `stepsDown`, not the exercise's function)

**W1** (`stepsDown_some : stepsDown k n = some i → n = k + i`) runs Part 2's pattern: R4 on `n`
generalizing `i`; in each case R6, R7; hit branch R8 then `omega`; miss branch R12, then R13 / R14, R9, the IH
at `a`, and `omega`.

**W2** (`stepsDown_none : stepsDown k n = none → n < k`) runs Part 3's pattern: R6, R7, R5 in the hit branch,
R22 and the IH in the miss branch.

---

## Traps

- Plain `induction xs` in `search_some` (no `generalizing i`) gives `ih` about the original `i` only; the tail
  call returns some `i'` with `i = i' + 1`, and `ih` cannot be applied at `i'` (R4).
- `cases hs : search k xs` rewrites the **goal**, not `h`. `h` still mentions `search k xs`: follow with
  `simp [hs] at h` (R13, R14).
- `cases search k xs` without `hs :` loses the link between the cases and `search k xs`; `ih i' ?` then has
  nothing to be fed.
- `simp only [search] at h` fires only on `search k (x :: xs)` or `search k []`, never on an unknown list;
  that is why it comes after `induction`.
- After `subst h` with `h : i' + 1 = i`, the goal speaks of `(x :: xs)[i' + 1]?` and `j < i' + 1`; split `j`
  (R19) so that R10 / R17 can fire on a literal `0` or `j + 1`.
- `k ∉ xs` prints as `¬k ∈ xs`; `simp only [List.mem_cons]` still finds it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| recursive `def` on a list | `match xs with \| [] => … \| x :: xs => …` | R1 |
| branch on `x = k` | `if x = k then … else …` | R2 |
| shift an optional index | `(e).map (· + 1)` | R3 |
| IH for every index | `induction xs generalizing i with \| nil => … \| cons x xs ih => …` | R4 |
| `h : none = some _` / `some _ = none` | `simp at h` (closes) | R5 |
| unfold `search` in `h` | `simp only [search] at h` | R6 |
| split the `if` in `h` | `split at h` | R7 |
| `some a = some b` → `a = b` | `simp at h` | R8 |
| eliminate `i` using `h : a = i` | `subst h` | R9 |
| `(a :: l)[0]?`, `(a :: l)[i + 1]?` | applied by `simp` | R10, R17 |
| finish from the hypotheses | `simp_all` | R11 |
| split on the recursive call | `cases hs : search k xs with \| none => … \| some i' => …` | R12 |
| `Option.map f e` with `hs : e = …` in `h` | `simp [hs] at h` | R13, R14 |
| use the IH at `i'` | `obtain ⟨h1, h2⟩ := ih i' hs` | R15 |
| prove the first conjunct inline | `refine ⟨by simpa using h1, ?_⟩` | R16, R18 |
| `∀ j < i' + 1, …` | `intro j hj; cases j with \| zero => … \| succ j => …` | R19 |
| `j < i'` from `j + 1 < i' + 1` | `h2 j (by omega)` | R20 |
| `k ∉ []` | `simp` | R21 |
| `Option.map f e = none` → `e = none` | `simp at h` | R22 |
| `k ∉ x :: xs` → `¬k = x ∧ k ∉ xs` | `simp only [List.mem_cons, not_or]` | R23, R24 |
| prove `¬p ∧ q` | `exact ⟨fun hp => …, hq⟩` | R25 |
| see the state | infoview | |
