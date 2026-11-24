# M017 · Quicksort terminates: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching, `List`, `rw`, `simp`, `have`,
`·`. **New here:** well-founded recursion (`termination_by` / `decreasing_by`), functional induction
(`fun_induction`), `List.filter` with `decide`, permutations (`List.Perm`), and the closers `omega` and
`grind`. Everything is core Lean: no Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop → Prop` when the changed part is itself a
  proposition). The step changes only the part inside `P (…)`, wherever it sits in a larger goal.
- `G` is an arbitrary goal that the step leaves alone (used when only the context changes).
- `{α : Type}` is any element type: `Nat` in this exercise.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[]` | the empty list |
| `a :: l` | the list with head `a` and tail `l` |
| `x ∈ l` | `x` is an element of the list `l` (`List.Mem`, a `Prop`) |
| `s ++ t` | `s` followed by `t` (append) |
| `l.length` | the length of `l`, a `Nat` |
| `List.filter p l`, `l.filter p` | the elements `a` of `l` with `p a = true`, in order; `p : α → Bool` |
| `(· < p)` | `fun x => x < p` (the `·` is the argument) |
| `decide A` | the `Bool` that is `true` iff the proposition `A` holds (needs `A` decidable, as `x < p` on `Nat` is) |
| `fun x => decide (x < p)` | how `(· < p)` prints once used as a `Bool` test: `filter` needs `α → Bool`, so Lean inserts `decide` |
| `!b` | `Bool` negation of `b : Bool` |
| `p a = true` | the `Bool` test `p a` passed, as a proposition |
| `¬x < p` | `¬(x < p)` |
| `A ∧ B ∨ C ↔ D` | `((A ∧ B) ∨ C) ↔ D`: `∧` binds tighter than `∨`, `↔` loosest |
| `l₁.Perm l₂` | `List.Perm l₁ l₂` (notation `l₁ ~ l₂`): `l₁` is a reordering of `l₂` |
| `x✝`, `ih1✝` | inaccessible names made by a tactic; you cannot type them until you name them (R6) |
| `case case2` | the goal for the second equation of the function (R6) |
| `this` | the name `have := e` gives a fact when you give none (R2) |

---

## Part 1 · `qsort` (`decreasing_by`)

Statement: `qsort` recurses on `lows p xs` and `highs p xs`, which are not sub-terms of `p :: xs`, so Lean
cannot see that it terminates. `termination_by xs => xs.length` (frozen) says the length decreases; your
`decreasing_by` proves it, once per recursive call. Given helpers: `lows_le p xs : (lows p xs).length ≤
xs.length` and `highs_le` (proved with R3).

**R1 · `termination_by m` + `decreasing_by`** changes the **goal list**: `m` is a `Nat` measure of the
arguments (`xs.length` for `qsort`, `l.length` for the guide's `sieve`). For each recursive call `f a` inside
the equation for input `i`, you get a goal `m(a) < m(i)` with the pattern variables in context.
Several calls give several goals: handle each with `·` (or `all_goals`).
In the guide, `sieve (x :: xs)` calls `sieve (rest x xs)`.

| Before | After |
|---|---|
| `def sieve` … `termination_by l.length` `decreasing_by` | `x : Nat, xs : List Nat ⊢ (rest x xs).length < (x :: xs).length` |

**R2 · `have := e`** changes the **context**: it adds the fact `e` under the name `this`. The goal stays.
Placeholders: `(T G : Prop) (t : T)`.

| Before | After |
|---|---|
| `⊢ G` | `this : T ⊢ G` |

**R3 · `List.length_filter_le`** changes the **context** (with `have :=`). The lemma is
`List.length_filter_le (p : α → Bool) (l : List α) : (l.filter p).length ≤ l.length`: filtering never makes
a list longer. The given helpers `lows_le`, `highs_le` are this lemma. Placeholders:
`{α : Type} (p : α → Bool) (l : List α)`.

| Before | After |
|---|---|
| `⊢ G` | `this : (List.filter p l).length ≤ l.length ⊢ G` |

**R4 · `simp only [List.length_cons]`** changes the **goal**. The lemma is
`List.length_cons : (a :: l).length = l.length + 1`. Placeholders: `{α : Type} (a : α) (l : List α)`.
`rw [List.length_cons]` works too, but rewrites only the first instance it finds (with all its copies).

| Before | After |
|---|---|
| `⊢ P (a :: l).length` | `⊢ P (l.length + 1)` |

**R5 · `omega`** **closes** a goal of linear arithmetic (`+`, `-`, `*` by numerals, `<`, `≤`, `=`) over `Nat`
and `Int`, using the hypotheses in context. Any other term, such as `(l.filter p).length`, is an opaque
number: two terms count as the same number only if they are written the same way. Placeholders:
`(a b : Nat)`.

| Before | After |
|---|---|
| `h : a ≤ b ⊢ a < b + 1` | no goals |

**W1: the `decreasing_by` goal of `sieve`, replayed.** R2 with `rest_le x xs`, then R4, then R5:

```lean-goal
⊢ (rest x xs).length < (x :: xs).length
⊢ (rest x xs).length < xs.length + 1
```

---

## Part 2 · `mem_qsort`

Statement: `x ∈ qsort xs ↔ x ∈ xs`: sorting keeps exactly the same elements.

**R6 · `fun_induction f l`** changes the **goal list**: induction that follows the equations of `f`, one goal
per equation (`case1`, `case2`, …), with one induction hypothesis per recursive call, and `f` already
unfolded in each goal. Use it when `f` is not structurally recursive (plain `induction l` gives you an IH
about the tail, which `qsort` never calls). Name the new variables with
`fun_induction f l with | case1 => … | case2 a b ih1 ih2 => …`, in the order they are listed in the
context; only the `✝` names are named (in `mem_qsort`, `x` is already named, so case2 is
`case2 p xs ih1 ih2`). Placeholders: `(l : List Nat) (Q : List Nat → Nat → Prop)`, and the guide's
`zig : List Nat → Nat` with equations `[]`, `[x]`, `x :: y :: xs` (two recursive calls in the last).

| Before | After `fun_induction zig l` |
|---|---|
| `⊢ Q l (zig l)` | `⊢ Q [] 0`, `x✝ : Nat ⊢ Q [x✝] x✝`, `⊢ Q (x✝ :: y✝ :: xs✝) (x✝ + zig (y✝ :: xs✝) + zig xs✝)` |

After naming the variables of `case3` as `x y xs ih1 ih2`:

| Before | After |
|---|---|
| `⊢ Q (x✝ :: y✝ :: xs✝) (x✝ + zig (y✝ :: xs✝) + zig xs✝)` | `ih1 : Q (y :: xs) (zig (y :: xs)), ih2 : Q xs (zig xs) ⊢ Q (x :: y :: xs) (x + zig (y :: xs) + zig xs)` |

The infoview labels the first IH `ih2✝`, but the first name you give goes to it: in context order,
`ih1` is the IH of the first recursive call.

**R7 · `rw [List.mem_append]`** changes the **goal**. The lemma is
`List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. Placeholders: `{α : Type} (a : α) (s t : List α)`.

| Before | After |
|---|---|
| `⊢ P (a ∈ s ++ t)` | `⊢ P (a ∈ s ∨ a ∈ t)` |

**R8 · `rw [List.mem_cons]`** changes the **goal**. The lemma is `List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`.
Placeholders: `{α : Type} (a b : α) (l : List α)`. `rw` rewrites the first match only (and its copies), so
the right-hand side `x ∈ p :: xs` of `mem_qsort` stays as it is.

| Before | After |
|---|---|
| `⊢ P (a ∈ b :: l)` | `⊢ P (a = b ∨ a ∈ l)` |

**R9 · `rw [h]` with `h : A ↔ B`** changes the **goal**: an `↔` rewrites like an `=`, replacing `A` by `B`.
This is how the IHs of `mem_qsort` (which are `↔`) are used. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `h : A ↔ B ⊢ P A` | `⊢ P B` |

**R10 · `unfold d`** changes the **goal**: the defined name `d` is replaced by its body. `simp only [d]`
does the same and can be combined with other lemmas. Placeholders: the guide's
`def small (xs : List Nat) : List Nat := xs.filter (· < 3)`. Note the `decide` that appears.

| Before | After |
|---|---|
| `⊢ P (small xs)` | `⊢ P (List.filter (fun x => decide (x < 3)) xs)` |

**R11 · `List.mem_filter`** changes the **goal**. The lemma is
`List.mem_filter : a ∈ l.filter p ↔ a ∈ l ∧ p a = true`. Placeholders:
`{α : Type} (p : α → Bool) (a : α) (l : List α)`. `rw` fixes `p` and `l` at the first match, so in
`mem_qsort` (two different filters) it takes two `rw`s; `simp only [List.mem_filter]` does both at once.

| Before | After |
|---|---|
| `⊢ P (a ∈ List.filter p l)` | `⊢ P (a ∈ l ∧ p a = true)` |

**R12 · `simp only [decide_eq_true_eq]`** changes the **goal**: the `Bool` test turns back into the
proposition. The lemma is `decide_eq_true_eq : (decide A = true) = A`. Placeholders:
`(A : Prop) [Decidable A]` (a decidability proof for `A`; `x < p` on `Nat` has one). After R11 on
`filter (· < p)` you have `decide (x < p) = true`; this makes it `x < p`.

| Before | After |
|---|---|
| `⊢ P (decide A = true)` | `⊢ P A` |

**R13 · `grind`** **closes** goals that follow by propositional logic (with case splits such as `B ∨ ¬B`),
equalities, simple list facts (it knows `List.mem_cons`) and linear arithmetic. Placeholders:
`(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∨ C ∨ A ∧ ¬B ↔ C ∨ A` | no goals |

**W3: membership in a split at 5.** R7, then R11 with R12 in one `simp only`, then R13:

```lean-goal
⊢ x ∈ List.filter (fun x => decide (x < 5)) xs ++ List.filter (fun y => decide ¬y < 5) xs ↔ x ∈ xs
⊢ x ∈ List.filter (fun x => decide (x < 5)) xs ∨ x ∈ List.filter (fun y => decide ¬y < 5) xs ↔ x ∈ xs
⊢ x ∈ xs ∧ x < 5 ∨ x ∈ xs ∧ ¬x < 5 ↔ x ∈ xs
```

---

## Part 3 · `qsort_length`

Statement: `(qsort xs).length = xs.length`. Same induction as Part 2 (R6); `case1` is `[].length =
[].length` (`rfl`). In `case2` the IHs are equations, used with plain `rw [ih1, ih2]`.

**R14 · `rw [List.length_append]`** changes the **goal**. The lemma is
`List.length_append : (s ++ t).length = s.length + t.length`. Placeholders: `{α : Type} (s t : List α)`.

| Before | After |
|---|---|
| `⊢ P (s ++ t).length` | `⊢ P (s.length + t.length)` |

**R15 · `List.filter_append_perm`** changes the **context** (with `have :=`). The lemma is
`List.filter_append_perm (p : α → Bool) (l : List α) : (l.filter p ++ l.filter (fun x => !p x)).Perm l`:
the elements that pass `p` followed by those that fail it are a reordering of `l`. Placeholders:
`{α : Type} (p : α → Bool) (l : List α)`. For `p` write `(fun x => decide (x < p))` to match `lows`.

| Before | After |
|---|---|
| `⊢ G` | `this : (List.filter p l ++ List.filter (fun x => !p x) l).Perm l ⊢ G` |

**R16 · `List.Perm.length_eq`** changes the **context**. The lemma is
`List.Perm.length_eq : l₁.Perm l₂ → l₁.length = l₂.length`. Dot notation: for `hp : l₁.Perm l₂`,
`hp.length_eq` is `List.Perm.length_eq hp`, so `(List.filter_append_perm _ _).length_eq` chains R15 and R16.
Placeholders: `{α : Type} (l₁ l₂ : List α) (hp : l₁.Perm l₂)`.

| Before | After |
|---|---|
| `hp : l₁.Perm l₂ ⊢ G` | `this : l₁.length = l₂.length ⊢ G` |

**R17 · `rw [lemma] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal.
Placeholders: `{α : Type} (s t : List α) (n : Nat)`.

| Before | After |
|---|---|
| `h : (s ++ t).length = n ⊢ s.length + t.length = n` | `h : s.length + t.length = n ⊢ s.length + t.length = n` |

**R18 · `simp only [decide_not]`** changes the **goal**. The lemma is `decide_not : decide ¬A = !decide A`.
Placeholders: `(p : Nat → Prop) [DecidablePred p] (l : List Nat)` (`DecidablePred p`: every `p x` is
decidable). It matters because `highs` unfolds to `decide ¬x < p` while R15 produces `!decide (x < p)`, and
`omega` (R5) treats differently written lengths as different numbers. The rewrite happens under
`fun x =>`, where `rw` cannot reach: use `simp only`.

| Before | After |
|---|---|
| `⊢ P (List.filter (fun x => decide ¬p x) l)` | `⊢ P (List.filter (fun x => !decide (p x)) l)` |

**W4: the two halves of a split at 5 add up.** `have := (List.filter_append_perm (· < 5) xs).length_eq`
(R15 → R16), `rw [List.length_append] at this` (R17: `this` becomes "first length + second length =
`xs.length`", with `!decide (x < 5)` in the second), then R18 on the goal and R5:

```lean-goal
⊢ (List.filter (fun x => decide (x < 5)) xs).length + (List.filter (fun y => decide ¬y < 5) xs).length = xs.length
⊢ (List.filter (fun x => decide (x < 5)) xs).length + (List.filter (fun y => !decide (y < 5)) xs).length = xs.length
```

---

## Traps

- Rewrite with the IHs **before** unfolding `lows`/`highs`. The IHs mention `qsort (lows p xs)`; once
  `lows` is unfolded that text is gone and `rw [ih1]` fails.
- `fun_induction … with | case2 p xs ih1 ih2`: `ih1` is the IH for the first recursive call
  (`lows`), even though the infoview labels it `ih2✝` before you name it.
- `decreasing_by` has **two** goals. A single tactic block runs on the first only; use `·` per goal or
  `all_goals`.
- `omega` matches opaque terms by how they are written: `decide ¬x < p` and `!decide (x < p)` are two
  different unknowns to it (R18). It also needs the facts in context: `have` them first.
- `rw [List.length_cons]` rewrites one instance (`(p :: qsort …).length`), not every `(_ :: _).length`;
  repeat it for `(p :: xs).length`, or use `simp only [List.length_cons]`.
- `rw` cannot rewrite under a binder (`fun x => …`); use `simp only [lemma]` there.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove a recursive call shrinks | `decreasing_by` then `·` per call | R1 |
| add a known bound | `have := lows_le p xs` | R2, R3 |
| `(a :: l).length → l.length + 1` | `simp only [List.length_cons]` | R4 |
| linear `Nat` arithmetic from context | `omega` | R5 |
| induction along `qsort` | `fun_induction qsort xs with \| case1 => … \| case2 p xs ih1 ih2 => …` | R6 |
| `∈ s ++ t`, `∈ b :: l` | `rw [List.mem_append, List.mem_cons]` | R7, R8 |
| use an `↔` IH | `rw [ih1, ih2]` | R9 |
| unfold a definition | `unfold lows highs` / `simp only [lows, highs]` | R10 |
| `∈ l.filter p` → `∈ l ∧ …` | `simp only [List.mem_filter, decide_eq_true_eq]` | R11, R12 |
| finish the logic | `grind` | R13 |
| `(s ++ t).length` | `rw [List.length_append]` | R14 |
| the two filter lengths add up | `have := (List.filter_append_perm (fun x => decide (x < p)) xs).length_eq` | R15, R16 |
| rewrite a hypothesis | `rw [List.length_append] at this` | R17 |
| `decide ¬A → !decide A` | `simp only [decide_not]` | R18 |
| see the state | infoview | |
