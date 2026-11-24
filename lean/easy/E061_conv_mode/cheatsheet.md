# E061 · conv mode: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact`, `rfl`, `rw [h]`, lambdas
`fun x => …`, and `List.map`. **New here:** `conv` mode, a sub-language of tactics that move a *focus*
through the goal (`lhs`, `rhs`, `arg i`, `intro x`) and rewrite only the focused subterm; its variants
`conv at h` and `conv in pat`; the core lemmas `Nat.zero_add` and `List.map_id'`. No Mathlib.

Why conv: `rw [Nat.zero_add]` on `(fun x => f (0 + x)) = f` fails with
`Did not find an occurrence of the pattern 0 + ?n`. The `0 + x` mentions the bound variable `x`, and
`rw` cannot instantiate `?n` with a variable bound inside the term. `conv … intro x` turns `x` into a local,
and then `rw` works. `funext`, `ext` and `simp` would bypass this and are banned.

## How to read an entry

Each entry is one tactic, one conv tactic, or one lemma. It says what changes (**goal**, **context**,
**goal list**, or the conv **focus**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `Γ | e` is a **conv goal**, the state inside a `conv` block: `e` is the focused subterm. You see it in the
  infoview when the cursor is inside the block. Conv cells below are copied from the infoview.
- `P` is "the rest of a statement" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `{α β : Type}` are any types; the entries work for `Nat` or anything else.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `\| fun x => g (0 + x)` | a conv goal: you are focused on that term (inside a `conv` block) |
| `x : Nat` appears above `\|` | `intro x` (conv) turned the bound `x` into a local |
| `P fun x => g x a` | `P (fun x => g x a)`: Lean drops the parentheses around a `fun` argument |
| `∀ (x : α), g x a = g x b` | Lean prints the binder type `(x : α)` of a `∀` |
| `fun x => f x` vs `f` | equal by **eta**. When a `conv` block ends, Lean writes `fun x => f x` as `f` |
| `0 + ?n` (in an error) | `?n` is a *metavariable*: a hole `rw` tries to fill with a subterm of the goal |
| `List.map t xs` | the list `xs` with `t` applied to each element; explicit arguments `t`, `xs` |

---

## Part 1 · `under_binder`

Statement: `(fun x => f (0 + x)) = f`. Enter conv (R1), focus the left side (R2), step under the binder
(R3), rewrite `0 + x` (R4). When the block ends, Lean eta-reduces `fun x => f x` to `f`; the goal `f = f`
is closed by the `rfl` tried at the end (R5).

**R1 · `conv => tacs`** changes the **goal**: inside the block the goal `⊢ G` becomes the conv goal `| G`,
the conv tactics `tacs` move the focus or rewrite the focused term, and at the end `G` is replaced by the
result. Inside conv, `rw [e]` rewrites the focus. Placeholders:
`{α : Type} (a b : α) (P : α → Prop) (e : a = b)`.

| Before | Inside, after `rw [e]` | After the block |
|---|---|---|
| `⊢ P a` | `\| P b` | `⊢ P b` |

**R2 · `lhs` / `rhs`** (conv) change the **focus**: `| a = b` becomes `| a` (`rhs`: `| b`). Moving the focus
alone changes nothing, so the block below ends with the goal as it was. Placeholders: `{α : Type} (a b : α)`.

| Before | Inside, after `lhs` | After the block |
|---|---|---|
| `⊢ a = b` | `\| a` | `⊢ a = b` |

**R3 · `intro x`** (conv) changes the **focus and the context**: on `| fun x => t x` it adds a local `x : α`
and focuses the body `| t x`. Now the body is an ordinary term that `rw` can rewrite. When the block ends,
Lean rebuilds the `fun` and eta-reduces `fun x => t x` to `t`. Placeholders:
`{α β : Type} (t u : α → β) (h : t = u)`.

| Before | Inside, after `lhs` | Inside, after `intro x` | After the block |
|---|---|---|---|
| `⊢ (fun x => t x) = u` | `\| fun x => t x` | `x : α \| t x` | `⊢ t = u` |

**R4 · `Nat.zero_add`** changes the **goal**. The lemma is `Nat.zero_add (n : Nat) : 0 + n = n` (core Lean).
`0 + n` does not compute to `n`, because `+` on `Nat` recurses on its second argument, so you need the lemma.
`rw [Nat.zero_add]` works the same on a conv focus: in the exercise, `x : Nat | f (0 + x)` becomes
`x : Nat | f x`. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (0 + n)` | `⊢ P n` |

**R5 · end of a `conv` block** changes the **goal list**: Lean rebuilds the goal from the focus (eta-reducing
`fun x => t x` to `t`), then tries `rfl` on it and closes it if it can. That `rfl` runs at reducible
transparency (`with_reducible rfl`): it does not unfold ordinary definitions, so `List.map (fun x => x) xs = xs`
stays open (Part 2). Placeholders: `{α β : Type} (a b : α) (e : a = b) (t : α → β)`.

| Before | Inside, after the last conv step | After the block |
|---|---|---|
| `⊢ a = b` | `\| b = b` (after `rw [e]`) | no goals |
| `⊢ (fun x => t x) = t` | `x : α \| t x` (after `lhs; intro x`) | no goals (it was `t = t`) |

**W1 (on `g (x * 1)`, lemma `Nat.mul_one (n : Nat) : n * 1 = n`):** R1, R2, R3, `rw [Nat.mul_one]`, R5.

| Before | `lhs` | `intro x` | `rw [Nat.mul_one]` | After the block |
|---|---|---|---|---|
| `⊢ (fun x => g (x * 1)) = g` | `\| fun x => g (x * 1)` | `x : Nat \| g (x * 1)` | `x : Nat \| g x` | no goals |

---

## Part 2 · `map_under`

Statement: `List.map (fun x => 0 + x) xs = xs`. The binder is inside `List.map`'s first argument: focus the
left side (R2), then the function (R6), step under it (R3), rewrite (R4). The block ends at
`List.map (fun x => x) xs = xs`, which `rfl` cannot close for a variable list; finish with R7.

**R6 · `arg i`** (conv) changes the **focus**: on `| F a₁ … aₙ` it focuses the i-th *explicit* argument
`| aᵢ`, counted from 1. `List.map t xs` has explicit arguments `t` (`arg 1`) and `xs` (`arg 2`); its type
arguments are implicit and skipped (`arg @i` counts those too). Placeholders:
`{α β : Type} (t : α → β) (xs : List α) (ys : List β)`.

| Before | Inside, after `lhs` | Inside, after `arg 1` | After the block |
|---|---|---|---|
| `⊢ List.map t xs = ys` | `\| List.map t xs` | `\| t` | `⊢ List.map t xs = ys` |

**R7 · `List.map_id'`** **closes** the goal. The lemma is
`List.map_id' {α : Type u} (l : List α) : List.map (fun a => a) l = l` (core Lean): mapping the identity
changes nothing. `exact List.map_id' l` proves it for your list. (`List.map_id` is the same fact stated with
`id`.) Placeholders: `{α : Type} (l : List α)`.

| Before | After `exact List.map_id' l` |
|---|---|
| `⊢ List.map (fun a => a) l = l` | no goals |

---

## Part 3 · `at_h`

Statement: from `h : (fun x => f (0 + x)) = g`, prove `f = g`. Rewrite inside `h` instead of the goal (R8),
with the same path as Part 1 (R2, R3, R4). When the block ends, `fun x => f x` is eta-reduced, so
`h : f = g`, which is the goal: `exact h`.

**R8 · `conv at h => tacs`** changes the **context**: the conv goal starts as `| (type of h)` and `h` is
replaced by the result. The goal is unchanged, and no `rfl` is tried at the end. Placeholders:
`{α : Type} (a b : α) (P : α → Prop) (e : a = b)`.

| Before | Inside, after `rw [e]` | After the block |
|---|---|---|
| `h : P a ⊢ P b` | `\| P b` | `h : P b ⊢ P b` |

**W2 (two levels down in a hypothesis):** `conv at h => rhs; arg 2; rw [Nat.mul_one]` (R8, R2, R6).

| Before | `rhs` | `arg 2` | `rw [Nat.mul_one]` | After the block |
|---|---|---|---|---|
| `h : a = b * (c * 1) ⊢ a = b * c` | `\| b * (c * 1)` | `\| c * 1` | `\| c` | `h : a = b * c ⊢ a = b * c` |

---

## Part 4 · `pattern_bind`

Statement: `(fun x => f (0 + x) + 1) = fun x => f x + 1`. Instead of walking there, jump to the subterm by
pattern (R9) with `0 + _`, rewrite it (R4). The block ends at `(fun x => f x + 1) = fun x => f x + 1`,
which `rfl` closes (R5).

**R9 · `conv in pat => tacs`** changes the **goal**: the focus jumps to the first subterm matching `pat`,
even under a binder. `_` in `pat` matches anything, the bound variable included, and that variable becomes a
local. Placeholders:
`{α β : Type} (g : α → α → β) (a b : α) (e : ∀ x, g x a = g x b) (P : (α → β) → Prop)`.

| Before | Inside, at the start | Inside, after `rw [e]` | After the block |
|---|---|---|---|
| `⊢ P fun x => g x a` | `x : α \| g x a` | `x : α \| g x b` | `⊢ P fun x => g x b` |

**W3 (related, not conv):** `rw (occs := [k]) [e]` rewrites only the k-th match of `e`'s left side. On
`a + b + (a + b) = b + a + (a + b)`, `rw (occs := [1]) [Nat.add_comm a b]` turns only the first `a + b` into
`b + a`, and the final `rfl` closes the goal.

---

## Traps

- `rw` cannot rewrite a subterm that mentions a bound variable (`Did not find an occurrence of the pattern`).
  Neither can conv's `rw` while the focus is still `| fun x => …`: `intro x` first (R3), or use `conv in`.
- A `conv` block ends with `rfl` (R5). If that closes the goal, any tactic after the block fails with
  `No goals to be solved`. In Part 1 and Part 4 nothing follows the block.
- `arg i` counts **explicit** arguments from 1. Use `arg @i` to count implicit ones too.
- `conv_lhs => …` and `nth_rw` are Mathlib only. In core write `conv => lhs; …` and `rw (occs := [k]) […]`.
- `conv at h` does not try `rfl`, so the goal stays open: finish with `exact h`. The infoview shows `h : f = g`,
  not `h : (fun x => f x) = g`, because the block eta-reduces the result.
- The `rfl` at the end of a block does not unfold definitions: `List.map (fun x => x) xs = xs` needs R7.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| rewrite part of the goal | `conv => …; rw [e]` | R1 |
| focus a side of `a = b` | `lhs` / `rhs` | R2 |
| step under `fun x =>` | `intro x` (in conv) | R3 |
| `0 + n → n` | `rw [Nat.zero_add]` | R4 |
| leave conv | block ends, `rfl` tried | R5 |
| focus the i-th explicit argument | `arg i` | R6 |
| `List.map (fun a => a) l = l` | `exact List.map_id' l` | R7 |
| rewrite inside a hypothesis | `conv at h => …` | R8 |
| jump to a subterm by pattern | `conv in 0 + _ => …` | R9 |
| only the k-th match | `rw (occs := [k]) [e]` | W3 |
| see the state | infoview, cursor inside the block | |
