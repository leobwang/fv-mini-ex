# M021 · Partition is a permutation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, pairs `α × β`, `Bool`,
`rfl`, `exact`, `apply`, `refine`, `simp`, `rw`, `omega`, `induction` on `List`, `<;>`, `·` bullets.
**New here:** core Lean only (no Mathlib): `cases h : b` on a Boolean with the case fact named,
evaluating a `def` whose clause has a `let` and an `if`, the core list lemmas `List.filter_cons` and
`List.cons_append`, the `Bool`/`if` clean-up lemmas, rewriting a hypothesis and the goal together
(`at ih ⊢`), and the permutation relation `List.Perm` with `refl`, `trans`, `cons` and `perm_middle`.

The problem in one paragraph. `partition p xs : List Nat × List Nat` walks `xs` once and puts each `x`
into the first list if `p x = true`, into the second otherwise. Part 1 (`partition_eq`) shows the result
is the pair of the two filters, `(xs.filter p, xs.filter (fun x => !p x))`. Part 2 (`partition_perm`)
shows that the two lists glued together are a rearrangement of `xs`. Part 2 starts by rewriting with
Part 1, so it is a statement about two filters only.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`, `P : List α → Prop`). The step changes only
  the part inside `P (…)`. A hypothesis `h` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  ∅ means the goal is closed.
- The guide's own object: `tally q l : Nat × Nat`, the pair (number of elements with `q`, number
  without), computed in one pass with `let r := tally q xs` and an `if`, the same shape as `partition`.

## Reading the goals

| You see | It means |
|---|---|
| `List Nat × List Nat` | the type of pairs of lists; `(a, b)` is a pair |
| `r.1`, `r.2` / `.fst`, `.snd` | the first / second component of a pair; Lean prints `.1` as `.fst` |
| `List.filter p xs` | the elements `y` of `xs` with `p y = true`, in order (`xs.filter p` is the same) |
| `fun x => !p x` | the predicate "not `p`"; `!b` is Boolean negation `Bool.not b`. Its `x` is a bound variable, not your `x` |
| `(!p ·)` | how the skeleton and hints abbreviate `fun x => !p x`; `·` marks the argument |
| `if p x = true then a else e` | an `if` on a `Bool`: the condition `p x` is shown as the proposition `p x = true` |
| `false = true`, `True`, `False` | after `simp only [h]`: a false Boolean test (`false = true`, cleaned by R7), the propositions true / false |
| `a :: as ++ bs` | `(a :: as) ++ bs`: `::` binds tighter than `++` (precedence 67 vs 65), so the head sticks to `as` first |
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a rearrangement of `l₁` (same elements, same multiplicities). Hints write `l₁ ~ l₂` |
| `case cons.false`, `case cons.true` | goal tags: the `cons` arm of `induction`, then the `false` / `true` value from `cases h : p x` |

---

## Part 1 · `partition_eq`

Statement: `partition p xs = (xs.filter p, xs.filter (fun x => !p x))`: an equation of pairs of lists.
Induct on `xs`; the `nil` case computes. In the `cons x xs` case split on the Boolean `p x`, naming the
fact `h`, and evaluate both sides one step: `partition p (x :: xs)` by its second clause and `ih`, each
`filter` by `List.filter_cons`; then `h` decides every `if`.

### Induction and the base case

**R1 · `induction l with | nil => … | cons x xs ih => …`** changes the **goal list**: the `[]` case and
the `x :: xs` case, where `ih` is the statement for `xs`. In the exercise, `ih` is
`partition p xs = (List.filter p xs, List.filter (fun x => !p x) xs)`. Write each arm on its own line,
starting with `|`. Placeholders: `(P : List Nat → Prop) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P l` | `⊢ P []`, `x : Nat, xs : List Nat, ih : P xs ⊢ P (x :: xs)` |

**R2 · `rfl`** **closes** an equation whose two sides compute to the same value. `partition p []`,
`List.filter p []` and `tally q []` all evaluate by their `[]` clauses, so the `nil` case is `rfl`.
Placeholders: `(q : Nat → Bool)`.

| Before | After |
|---|---|
| `⊢ (tally q [], List.filter q []) = ((0, 0), [])` | ∅ |

### Splitting on `p x`

**R3 · `cases h : q x`** changes the **goal list and the context**: one goal per value of the `Bool`
`q x`, with `h : q x = false` in the first and `h : q x = true` in the second (`false` is `Bool`'s first
constructor). Every *visible* `q x` in the goal is replaced by the value. In the exercise `p x` is hidden
inside `partition` and `filter`, so the goal looks unchanged and only `h` is new; `h` is what later
decides the `if`s. Placeholders: `(q : Nat → Bool) (x : Nat) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (q x)` | `h : q x = false ⊢ P false`, `h : q x = true ⊢ P true` |

### Evaluating one step

**R4 · `simp only [f]`** changes the **goal**: it unfolds the clause of `f` whose pattern matches
(`x :: xs`), and substitutes the `let`: `r` is replaced by `tally q xs`, so `r.1` becomes
`(tally q xs).fst`. A call on a variable list (`tally q xs`) is not unfolded. In the exercise, after
`simp only [partition]` the left side is an `if p x = true then (x :: (partition p xs).fst, …) else …`,
and `ih` then rewrites `partition p xs`. Placeholders: `(q : Nat → Bool) (x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (tally q (x :: xs))` | `⊢ P (if q x = true then ((tally q xs).fst + 1, (tally q xs).snd) else ((tally q xs).fst, (tally q xs).snd + 1))` |

**R5 · `List.filter_cons`** changes the **goal**. The lemma is
`List.filter_cons : filter q (x :: xs) = if q x = true then x :: filter q xs else filter q xs`. In the
exercise it applies to both filters; for the second, `q` is `fun x => !p x`, so its condition is
`(!p x) = true`. Placeholders: `{α : Type} (q : α → Bool) (x : α) (xs : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.filter q (x :: xs))` | `⊢ P (if q x = true then x :: List.filter q xs else List.filter q xs)` |

**R6 · `simp only [h]`** (`h : b = true` or `h : b = false`) changes the **goal**: every `b` becomes its
value. With `h : q x = true`, the condition becomes `true = true`, which `simp` turns into `True` on the
spot. With `h : q x = false`, it becomes `false = true` and stays until R7. Placeholders:
`{α : Type} (q : Nat → Bool) (x : Nat) (a e : α) (hq : q x = false)`.

| Before | After |
|---|---|
| `hq : q x = false ⊢ P (if q x = true then a else e)` | `⊢ P (if false = true then a else e)` |

**R7 · `Bool.false_eq_true`** changes the **goal**. The lemma is `(false = true) = False`: it turns the
failed Boolean test into the proposition `False`. Placeholders: `{α : Type} (a e : α)`.

| Before | After |
|---|---|
| `⊢ P (if false = true then a else e)` | `⊢ P (if False then a else e)` |

**R8 · `if_true`, `if_false`** change the **goal**: `(if True then a else e) = a` and
`(if False then a else e) = e` pick the branch. Placeholders: `{α : Type} (a e : α)`.

| Before | After |
|---|---|
| `⊢ P (if True then a else e) ∧ P (if False then a else e)` | `⊢ P a ∧ P e` |

**R9 · `Bool.not_true`, `Bool.not_false`** change the **goal**: `(!true) = false`, `(!false) = true`.
After R6 the second filter's condition is `(!true) = true` or `(!false) = true`; R9 makes it
`false = true` (then R7) or `true = true` (which `simp` turns into `True`). Placeholders:
`(P : Bool → Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (!true) !false` | `⊢ P false true` |

**R10 · pair projections** change the **goal**: `(a, b).fst` becomes `a` and `(a, b).snd` becomes `b`.
Every `simp` / `simp only […]` call does this by itself, even `simp only []`. You meet them after
`rw [ih]` in Part 1 and after `rw [partition_eq]` in Part 2. Placeholders: `{α β : Type} (a : α) (b : β)`.

| Before | After |
|---|---|
| `⊢ P (a, b).fst (a, b).snd` | `⊢ P a b` |

R4–R10 combine into one call: a plain `simp [f, ih, lemma, h]`, given the definition to unfold, the
induction hypothesis, the list lemma and the case fact, unfolds, rewrites with `ih`, evaluates the `if`s
and closes the resulting `(a, b) = (a, b)` itself. `cases h : b <;> simp […]` runs it on both Boolean
cases. W1 shows the pattern on `tally`.

**W1.** `(tally q l).1 + (tally q l).2 = l.length`: `induction l` (R1), `nil` by `rfl` (R2), and in the
`cons` arm `cases h : q x <;> simp [tally, h] <;> omega` (R3, R4, R6–R10; `omega` uses `ih`).

```lean-goal
⊢ (tally q l).fst + (tally q l).snd = l.length
```

---

## Part 2 · `partition_perm`

Statement: `((partition p xs).1 ++ (partition p xs).2).Perm xs`. First `rw [partition_eq]` (R11), so
the goal is about the two filters. Then induct on `xs` (R1). `nil` closes by R12. In the `cons` case,
`cases h : p x` (R3) and in each branch `simp only [List.filter_cons, h] at ih ⊢` (R13 with R5, R6, R10),
then clean the `if`s (R7–R9). What is left:

- `p x = false`: `x` went to the second list, so it sits in the **middle**:
  `(List.filter p xs ++ x :: List.filter (fun x => !p x) xs).Perm (x :: xs)`. Move it to the front
  (R15), then use `ih` under the head `x` (R17), glued by R16.
- `p x = true`: `x` went to the first list. R14 pulls it out of `++`, giving
  `(x :: (List.filter p xs ++ List.filter (fun x => !p x) xs)).Perm (x :: xs)`: `ih` under the head (R17).

### Using Part 1

**R11 · `rw [lem]`** (`lem : ∀ l, f l = g l`) changes the **goal**: `rw` instantiates `lem` with the
first match `f l` and rewrites every copy of that instance. `rw [partition_eq]` replaces both
`partition p xs`, leaving `(… , …).fst ++ (… , …).snd` (R10 cleans it). Do it **before** `induction`, so
`ih` is about filters too. Placeholders: `(f g : List Nat → Nat × Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (f l) (f l)` | `⊢ P (g l) (g l)` |

### Permutations

**R12 · `exact .refl _`** **closes** `l.Perm l`. The lemma is `List.Perm.refl l : l.Perm l`; `.refl` is
read as `List.Perm.refl` from the goal's head. `exact` also accepts the goal when both sides only
*compute* to the same list: `List.filter q []`, `[] ++ []` and `(a, b).fst` all compute. Placeholders:
`(q r : Nat → Bool)`.

| Before | After |
|---|---|
| `⊢ (List.filter q [] ++ List.filter r []).Perm []` | ∅ |

**R13 · `simp only [l₁, h] at ih ⊢`** changes the **context and the goal**: the same rewriting in the
hypothesis `ih` and in the goal (`⊢` names the goal). It fails only when it changes neither. In the
exercise `ih` has no `x :: xs` for R5 to act on, but R10 still cleans its `.fst`/`.snd`.
Placeholders: `{α : Type} (q : α → Bool) (x : α) (xs : List α) (hq : q x = true)`.

| Before | After |
|---|---|
| `ih : P (List.filter q (x :: xs)) ⊢ Q (List.filter q (x :: xs))` | `ih : P (x :: List.filter q xs) ⊢ Q (x :: List.filter q xs)` |

**R14 · `List.cons_append`** changes the **goal**. The lemma is `a :: as ++ bs = a :: (as ++ bs)`: the
head moves out of the append. Placeholders: `{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R15 · `List.perm_middle`** **closes** a goal of its shape. The lemma is
`List.perm_middle : (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))`: an element in the middle can move to the
front. Its arguments `{a l₁ l₂}` are all implicit, read off the goal (or off the next step in a chain).
Placeholders: `{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂))` | ∅ |

**R16 · `List.Perm.trans`** changes the **goal**: the lemma is
`l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`. `refine h.trans ?_` uses `h` for the first step and leaves the
rest of the chain. As a term, `h.trans h'`. Placeholders: `{α : Type} (l₁ l₂ l₃ : List α)`.

| Before | After |
|---|---|
| `h : l₁.Perm l₂ ⊢ l₁.Perm l₃` | `h : l₁.Perm l₂ ⊢ l₂.Perm l₃` |

**R17 · `List.Perm.cons`** changes the **goal**: the lemma is `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)`,
so applying it drops a common head. As a term, `h.cons a` for `h : l₁.Perm l₂`. Placeholders:
`{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (a :: l₁).Perm (a :: l₂)` | `⊢ l₁.Perm l₂` |

### Worked combinations (W2, W3, on objects that are not the exercise's)

**W2.** Two middle elements to the front: `refine List.perm_middle.trans ?_` (R15 inside R16), then
`exact List.perm_middle.cons a` (R15 under R17).

```lean-goal
⊢ (l₁ ++ a :: b :: l₂).Perm (a :: b :: (l₁ ++ l₂))
⊢ (a :: (l₁ ++ b :: l₂)).Perm (a :: b :: (l₁ ++ l₂))
```

**W3.** A chain with an induction hypothesis `ih : (l₁ ++ l₂).Perm l`: move `a` to the front (R15),
then `ih` under the head `a` (R17), glued by R16: `exact List.perm_middle.trans (ih.cons a)`.

```lean-goal
⊢ (l₁ ++ a :: l₂).Perm (a :: l)
```

---

## Traps

- `cases p x` without `h :` throws the fact away: the goal never mentions `p x` literally, so nothing
  is replaced and `simp` cannot decide `if p x = true`. Write `cases h : p x` (R3).
- `rw [partition_eq]` goes **before** `induction`. Otherwise `ih` and the goal are about `partition`,
  and you have to unfold it and rewrite with Part 1 inside every case.
- `simp only [h]` with `h : p x = false` leaves `if false = true then …`: add `Bool.false_eq_true` and
  `if_false` (R7, R8). For the negated filter add `Bool.not_false` / `Bool.not_true` (R9).
- In the `false` case `x` lands in the middle of the append, not at the front: `List.Perm.cons` alone
  does not apply; go through `List.perm_middle` first (R15, R16).
- `(fun x => !p x)` prints a bound variable named `x`. It is not the `x` of your `cons` case.
- `List.filter_append_perm` is BANNED: it is Part 2 after `rw [partition_eq]` in one line.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on the list | `induction xs with \| nil => … \| cons x xs ih => …` | R1 |
| the `[]` case of an equation | `rfl` | R2 |
| split on a `Bool`, keep the fact | `cases h : p x` | R3 |
| unfold one clause of `partition` | `simp only [partition]` | R4 |
| one step of `filter` | `List.filter_cons` | R5 |
| decide the `if` with `h` | `simp only [h]` | R6 |
| `false = true` → `False` | `Bool.false_eq_true` | R7 |
| pick the branch | `if_true`, `if_false` | R8 |
| `!true`, `!false` | `Bool.not_true`, `Bool.not_false` | R9 |
| `(a, b).fst` → `a` | any `simp` | R10 |
| all of R4–R10 at once, both cases | `cases h : b <;> simp [def, ih, lemmas, h]` (W1) | R3–R10 |
| use Part 1 | `rw [partition_eq]` | R11 |
| `l.Perm l` (also up to computation) | `exact .refl _` | R12 |
| rewrite `ih` and the goal together | `simp only [lemmas] at ih` followed by ⊢ (R13) | R13 |
| `a :: as ++ bs` → `a :: (as ++ bs)` | `List.cons_append` | R14 |
| move a middle element to the front | `List.perm_middle` | R15 |
| chain two permutations | `h.trans h'` | R16 |
| add the same head | `h.cons a` | R17 |
| see the state | infoview | |
