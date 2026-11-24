# M037 · Rose trees: nested inductives: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, pattern-matching `def`s, `List`, `rw`,
`simp only`, `have`, `exact`. **New here:** nested inductive types (the recursive occurrence sits
inside `List`), recursive theorems in place of `induction`, well-founded unfolding with `simp only`,
and the core `List` lemmas about `map`, `reverse`, `flatten`, `length` and `sum`. No Mathlib.

The guide's examples run on its own tree `Bush α` (`Bush.br (a : α) (kids : List (Bush α))`), with
`Bush.count` (number of nodes) and `Bush.map f` (apply `f : α → β` to every label), never on `Rose`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma statement, lists the placeholders with their types,
then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : β → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders: `{α β γ : Type}` are any types, `u : α → β`, `v : β → γ`,
  `w : α → γ` are functions, `l : List α` is a list, `L : List (List α)` a list of lists.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Rose.node x cs` | the node with label `x : Nat` and children `cs : List Rose` |
| `.node x cs` (in a pattern or a `def`) | `Rose.node x cs`: a leading `.` means "the constructor `node` of the type Lean expects here" |
| `(Rose.node x cs).size` | `Rose.size (Rose.node x cs)`: dot notation, `t.f` is `T.f t` for `t : T` |
| `List.map f l` | `l.map f`: apply `f` to every element of `l` (Lean prints the `List.map f l` form) |
| `l.sum` | `List.sum l`: the sum of a list of numbers, `[].sum = 0` |
| `L.flatten` | `List.flatten L`: concatenate a list of lists, `[[1], [2, 3]].flatten = [1, 2, 3]` |
| `l.reverse` | `List.reverse l`: the list backwards |
| `x :: l` | the list with head `x` and tail `l` (`List.cons x l`) |
| `g ∘ f` | function composition, `(g ∘ f) a = g (f a)` (`Function.comp`) |
| `id` | the identity function, `id a = a` |
| `∀ (c : Rose), c ∈ cs → P c` | how Lean prints `∀ c ∈ cs, P c`: for every child `c` of the list `cs` |
| `sizeOf t` | a `Nat` measure Lean defines automatically for every inductive; a child's `sizeOf` is smaller than its parent's. Termination checks compare it |
| `match t with \| .br a kids => ?_` | `?_` is a hole: the tactics after the `match` line prove it |
| `t : Rose` still in the context after `match` | harmless: `match` adds `x`, `cs` and leaves `t` unused |

---

## Part 1 · `length_flatten`

Statement: `t.flatten.length = t.size`. The pre-order list of labels has one entry per node.

### Recursion on a nested inductive

**R1 · `match t with | .br a kids => ?_`** changes the **context and the goal**: the constructor's
fields `a`, `kids` enter the context and `t` is replaced by `.br a kids` in the goal. `induction t`
is rejected for a nested inductive ("does not support the type … because it is a nested inductive
type"); `match` is case analysis, and one constructor gives one goal. In the exercise write
`match t with` and then `| .node x cs =>` followed by the tactics of that case.
`cases t with | node x cs => …` (the alternative the `induction` error suggests) works the same way
here, and R2 can follow it.
Placeholders: `{α : Type} (P : Bush α → Prop) (t : Bush α)`.

| Before | After |
|---|---|
| `t : Bush α ⊢ P t` | `a : α, kids : List (Bush α) ⊢ P (Bush.br a kids)` |

**R2 · `have ih : ∀ k ∈ kids, P k := fun k _ => thm … k`** changes the **context**: it adds the
induction hypothesis. The theorem `thm` calls itself on each child `k`; the `_` is the proof of
`k ∈ kids`, and Lean uses it to show termination (`sizeOf k < sizeOf (.br a kids)`). This is
well-founded recursion, so `ih : ∀ k, P k` (no `∈ kids`) fails with "fail to show termination". The
guide's `bush_all` packages this as the induction principle for `Bush`.
Placeholders: `{α : Type} (P : Bush α → Prop) (a : α) (kids : List (Bush α))`.

| Before | After |
|---|---|
| `a : α, kids : List (Bush α) ⊢ P (Bush.br a kids)` | context gains `ih : ∀ (k : Bush α), k ∈ kids → P k`; goal unchanged `⊢ P (Bush.br a kids)` |

**R3 · `simp only [Bush.count]`** changes the **goal**: a definition applied to a constructor is
replaced by its clause. Definitions by recursion through `List.map` are compiled by well-founded
recursion, so `rfl` does not unfold them; `simp only [d]` (or `rw [d]`) uses the equation lemma.
In the exercise: `simp only [Rose.flatten, Rose.size]`, `simp only [Rose.mirror, …]`.
Placeholders: `{α : Type} (a : α) (kids : List (Bush α)) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Bush.br a kids).count` | `⊢ P (1 + (List.map Bush.count kids).sum)` |

### Lengths and maps

**R4 · `List.length_cons`** changes the **goal**. Statement: `(a :: as).length = as.length + 1`
(the `+ 1` is on the right). Placeholders: `{α : Type} (a : α) (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as).length` | `⊢ P (as.length + 1)` |

**R5 · `List.length_flatten`** changes the **goal**. Statement:
`L.flatten.length = (L.map List.length).sum`. Placeholders: `{α : Type} (L : List (List α))`.

| Before | After |
|---|---|
| `⊢ P L.flatten.length` | `⊢ P (List.map List.length L).sum` |

**R6 · `List.map_map`** changes the **goal**: two maps fuse into one map of the composition.
Statement: `List.map v (List.map u l) = List.map (v ∘ u) l`.
Placeholders: `{α β γ : Type} (u : α → β) (v : β → γ) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map v (List.map u l))` | `⊢ P (List.map (v ∘ u) l)` |

**R7 · `rw [List.map_congr_left (f := F) (g := G) hFG]`** changes the **goal**: it replaces one map by
another when the two functions agree on every element of the list. Statement:
`List.map_congr_left : (∀ a ∈ l, f a = g a) → List.map f l = List.map g l` (`f g` implicit). This is
where `ih` is used. Always name `f` and `g`: from `ih` alone Lean infers `f := fun a => v (u a)`, which
is not literally the `v ∘ u` that R6 left in the goal, and `rw` reports "did not find an occurrence of
the pattern". The hypothesis may be stated pointwise (`v (u a) = w a`): `(v ∘ u) a` unfolds to it.
Placeholders: `{α β γ : Type} (u : α → β) (v : β → γ) (w : α → γ) (l : List α)`,
`hvu : ∀ a ∈ l, v (u a) = w a`.

| Before | After |
|---|---|
| `⊢ P (List.map (v ∘ u) l)` | `⊢ P (List.map w l)` |

**R8 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `-`, numerals,
`≤`, `<`, `=`). Any other subterm, such as `(List.map u l).sum`, is treated as an unknown number.
Use it for `s + 1 = 1 + s`, which R4 leaves and `rw` cannot close.

### Worked combination (W2, on `Bush`)

`bush_count_map : (t.map f).count = t.count` chains R1, R2, R3, R6, R7. After R1, R2 and
`simp only [Bush.map, Bush.count]`, then after `rw [List.map_map]`:

```lean-goal
⊢ 1 + (List.map Bush.count (List.map (Bush.map f) kids)).sum = 1 + (List.map Bush.count kids).sum
⊢ 1 + (List.map (Bush.count ∘ Bush.map f) kids).sum = 1 + (List.map Bush.count kids).sum
```

`rw [List.map_congr_left (f := Bush.count ∘ Bush.map f) (g := Bush.count) ih]` makes both sides equal
and `rw` closes it by `rfl`.

---

## Part 2 · `size_mirror`

Statement: `t.mirror.size = t.size`. Mirroring reverses every list of children, which does not
change the count. Same frame as Part 1 (R1, R2, R3, then R6, R7); new are the two `reverse` lemmas.

**R9 · `List.map_reverse`** changes the **goal**: a map moves inside a `reverse`. Statement:
`List.map u l.reverse = (List.map u l).reverse`. Placeholders: `{α β : Type} (u : α → β) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map u l.reverse)` | `⊢ P (List.map u l).reverse` |

**R10 · `List.sum_reverse`** changes the **goal**. Statement: `l.reverse.sum = l.sum`. It holds for
any element type whose `+` is associative and commutative with unit `0` (type classes
`Std.Associative`, `Std.Commutative`, `Std.LawfulLeftIdentity`); `Nat` qualifies.
Placeholders: `(l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P l.reverse.sum` | `⊢ P l.sum` |

Order matters: R9 first moves `List.map Rose.size` inside the `reverse` so that R10 sees a
`(…).reverse.sum`; then R6 fuses the two maps. `simp only [...]` with all of them applies them in
whatever order works.

---

## Part 3 · `mirror_mirror`

Statement: `t.mirror.mirror = t`. Unfolding `Rose.mirror` twice (R3) gives two `reverse`s around two
maps. R9 moves the outer map inside, R11 cancels the reverses, R6 fuses the maps, R7 with `g := id`
uses `ih`, and R12 removes the `map id`.

**R11 · `List.reverse_reverse`** changes the **goal**. Statement: `l.reverse.reverse = l`.
Placeholders: `{α : Type} (l : List α)`.

| Before | After |
|---|---|
| `⊢ P l.reverse.reverse` | `⊢ P l` |

**R12 · `List.map_id`** changes the **goal**. Statement: `List.map id l = l`.
Placeholders: `{α : Type} (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map id l)` | `⊢ P l` |

### Worked combination (W1, on `Bush`)

`bush_map_id : t.map id = t`: after R1, R2 and `simp only [Bush.map]`, then R7 with
`(f := Bush.map id) (g := id)`, then R12:

```lean-goal
⊢ Bush.br (id a) (List.map (Bush.map id) kids) = Bush.br a kids
⊢ Bush.br (id a) (List.map id kids) = Bush.br a kids
⊢ Bush.br (id a) kids = Bush.br a kids
```

The last goal needs a plain `rfl` (`id a` unfolds to `a`). In the exercise there is no `id a` left:
the label `x` is not touched by `Rose.mirror`, so the `rw` of R12 closes the goal itself.

---

## Traps

- `induction t` fails on a nested inductive. Use `match` plus a recursive call (R1, R2).
- The recursive call must come with the membership proof: `fun c _ => thm c` for
  `∀ c ∈ cs, …`. Without `∈ cs` Lean cannot show termination. The `∈ cs` also tells Lean that
  `c : Rose`; `∀ c, c.size = …` fails earlier with "Invalid field notation: Type of c is not known".
- `rfl` does not unfold `Rose.size`, `Rose.flatten`, `Rose.mirror` (well-founded recursion). Unfold
  them with `simp only [Rose.size, …]` (R3).
- `rw [List.map_congr_left ih]` without `(f := …) (g := …)` fails: the inferred `f` is a `fun`, not
  the `g ∘ f` in the goal (R7). Copy `f` from the goal, e.g. `List.length ∘ Rose.flatten`.
- R7 rewrites only after R6 has fused the maps; before that the goal has `List.map g (List.map f cs)`,
  not `List.map (g ∘ f) cs`.
- `List.length_cons` puts `+ 1` on the right, `Rose.size` puts `1 +` on the left: finish with `omega`
  (R8), not `rfl`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| case on a nested inductive | `match t with \| .node x cs => …` | R1 |
| induction hypothesis | `have ih : ∀ c ∈ cs, P c := fun c _ => thm c` | R2 |
| unfold a recursive `def` | `simp only [Rose.size, Rose.flatten, Rose.mirror]` | R3 |
| `(a :: as).length` | `List.length_cons` → `as.length + 1` | R4 |
| `L.flatten.length` | `List.length_flatten` → `(L.map List.length).sum` | R5 |
| `(l.map f).map g` | `List.map_map` → `l.map (g ∘ f)` | R6 |
| use `ih` under a map | `rw [List.map_congr_left (f := F) (g := G) ih]` | R7 |
| `s + 1 = 1 + s` over `Nat` | `omega` | R8 |
| map of a reverse | `List.map_reverse` → `(l.map f).reverse` | R9 |
| `l.reverse.sum` | `List.sum_reverse` → `l.sum` | R10 |
| `l.reverse.reverse` | `List.reverse_reverse` → `l` | R11 |
| `l.map id` | `List.map_id` → `l` | R12 |
| see the state | infoview | |
