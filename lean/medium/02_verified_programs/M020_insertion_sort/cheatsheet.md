# M020 · Insertion sort: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, `inductive`, `intro`,
`exact`, `apply`, `refine`, `have`, `simp`, `omega`, `induction` on `Nat` and `List`, anonymous
constructors, `·` bullets. **New here:** core Lean only (no Mathlib): induction on the *derivation* of
an inductive predicate (`induction h` for `h : Sorted l`), constructors written as `.cons`, `by_cases`
on a comparison, evaluating an `if` with `simp only [h, if_true]`, rewriting a hypothesis with
`simp … at ih`, and the permutation relation `List.Perm` with its lemmas `refl`, `cons`, `trans`,
`swap`.

The problem in one paragraph. `Sorted l` is an inductive predicate with three constructors: `[]` is
sorted, `[x]` is sorted, and `x :: y :: rest` is sorted when `x ≤ y` and `y :: rest` is sorted.
`ins x l` inserts `x` before the first element `y` with `x ≤ y`; `isort` inserts the head into the
sorted tail. You prove that `isort xs` is sorted and is a permutation of `xs`. Both go through one
MILESTONE each about a single `ins` step, which you state and prove yourself first:
`ins_sorted : Sorted l → Sorted (ins x l)` and `ins_perm : (ins x l).Perm (x :: l)`.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`/`refine`/`simp`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : List Nat → Prop`, `P : Prop`). The step changes only
  the part inside `P (…)`. A hypothesis `h` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  `∅` means the goal is closed.
- The guide's own objects: `Alt l` (neighbours of `l` differ; constructors `nil`, `single x`,
  `cons : x ≠ y → Alt (y :: rest) → Alt (x :: y :: rest)`, the same shape as `Sorted`), `dropBig b l`
  (keep the elements `≤ b`; an `if` in the `::` clause, like `ins`), `pushBack x l` (append `x` at the
  end).

## Reading the goals

| You see | It means |
|---|---|
| `Sorted l` | the exercise's own inductive predicate `M020.Sorted`, not a library one |
| `.nil`, `.single x`, `.cons hxy hs` | `Sorted.nil`, `Sorted.single x`, `Sorted.cons hxy hs`: Lean reads `Sorted` off the goal (R2, R3) |
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a rearrangement of `l₁` (same elements, same multiplicities). The hints write it `l₁ ~ l₂` |
| `[y, x]` | the list `y :: x :: []` |
| `if x ≤ y then a else e` | an unevaluated `if`: `simp` evaluates it once it knows `x ≤ y` or `¬x ≤ y` (R6, R7) |
| `ins x (z :: rest)` vs `ins x rest` | the first can be unfolded (R5), the second cannot: `rest` is a variable |
| `x ≠ y` | `¬(x = y)` |
| `case nil`, `case single`, `case cons` | goal tags made by `induction h`, one per constructor of the predicate |
| `case pos`, `case neg` | goal tags made by `by_cases`: the condition holds / fails |
| `x✝`, `y✝` | inaccessible names: variables you did not name in an `induction` arm (use `@cons x y rest …`) |
| `l : List Nat` still in the context after `induction h` | the old index of `h : Sorted l`; it is unused in every case (the goal mentions the constructor's list instead). Ignore it |
| `Sorted (isort (x :: xs))`, `(ins x []).Perm [x]` | calls that `induction` does not unfold. They *compute* (`isort (x :: xs)` is `ins x (isort xs)`, `ins x []` is `[x]`), so `exact` accepts a term for the computed form (R11, R15); `simp only [isort]` shows it |
| `fun x => x + 1` | how `(· + 1)` is printed |

---

## Part 1 · `isort_sorted`

Statement: `Sorted (isort xs)`. Prove the MILESTONE `ins_sorted (x : Nat) {l : List Nat} (h : Sorted l) :
Sorted (ins x l)` first, by induction on the derivation `h`. Then `isort_sorted` is an induction on
`xs` that uses it in the `cons` case.

### Taking a derivation apart and building one

**R1 · `induction h with | nil => … | single x => … | @cons x y rest hxy hs ih => …`** changes the
**goal list**: one goal per constructor of the predicate, with the list replaced by that constructor's
list. `cons` has implicit arguments `{x y rest}`; `@cons` lets you name them, in order, followed by the
premises `hxy`, `hs` and the induction hypothesis `ih` for the premise `hs`. In `ins_sorted`, `ih` is
`Sorted (ins x (y :: rest))`: `x` stays fixed, the list shrinks. Placeholders:
`(P : List Nat → Prop) (l : List Nat) (h : Alt l)`.

| Before | After |
|---|---|
| `h : Alt l ⊢ P l` | `⊢ P []`, `x : Nat ⊢ P [x]`, `hxy : x ≠ y, hs : Alt (y :: rest), ih : P (y :: rest) ⊢ P (x :: y :: rest)` |

**R2 · `exact .single x`** **closes** `Alt [x]` (in the exercise `Sorted [x]`). `.single` is short for
`Alt.single`; Lean reads the namespace from the goal's head. `exact .nil` closes `Alt []` the same way.
Placeholders: `(x : Nat)`.

| Before | After |
|---|---|
| `⊢ Alt [x]` | ∅ |

**R3 · `refine .cons ?_ ?_`** changes the **goal list**: one goal per premise of the constructor. The
implicit `{x y rest}` are read off the goal. Usually you write the premises directly:
`exact .cons hxy hs`, or `exact .cons (by omega) ih`. Placeholders: `(x y : Nat) (rest : List Nat)`.

| Before | After |
|---|---|
| `⊢ Alt (x :: y :: rest)` | `⊢ x ≠ y`, `⊢ Alt (y :: rest)` |

### Case splits and evaluating `ins`

**R4 · `by_cases hxy : x ≤ y`** changes the **goal list and the context**: two goals, one with
`hxy : x ≤ y`, one with `hxy : ¬x ≤ y`. Placeholders: `(x y : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `hxy : x ≤ y ⊢ P`, `hxy : ¬x ≤ y ⊢ P` |

**R5 · `simp only [f]`** changes the **goal**: it unfolds a clause of the pattern-matching `def f`
wherever its list argument is visibly `[]` or `_ :: _`. A call on a variable list (`dropBig b ys`,
`ins x rest`) stays. Placeholders: `(b y : Nat) (ys : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (dropBig b (y :: ys))` | `⊢ P (if y ≤ b then y :: dropBig b ys else dropBig b ys)` |

**R6 · `simp only [hc, if_true]`** (`hc : c`) changes the **goal**: `simp` rewrites `c` to `True` using
`hc`, and `if_true : (if True then a else e) = a` picks the `then` branch. Placeholders:
`(s t : List Nat) (hyb : y ≤ b)`.

| Before | After |
|---|---|
| `⊢ P (if y ≤ b then s else t)` | `⊢ P s` |

**R7 · `simp only [hc, if_false]`** (`hc : ¬c`) changes the **goal**: `c` becomes `False`, and
`if_false : (if False then a else e) = e` picks the `else` branch. Placeholders: as R6 with
`(hyb : ¬y ≤ b)`.

| Before | After |
|---|---|
| `⊢ P (if y ≤ b then s else t)` | `⊢ P t` |

R5–R7 combine into one call, `simp only [ins, hxy, if_true]` or `simp only [ins, hxy, if_false]`. In
the `single y` case with `¬x ≤ y`, that call unfolds `ins` twice and leaves `Sorted [y, x]`.

**R8 · `simp only [f, hc, if_true] at ih`** changes the **context**: the same rewriting, applied to the
hypothesis `ih` instead of the goal (`at ih ⊢` does both). You need it in the `cons y z rest` case with
`¬x ≤ y`: the goal is then `Sorted (y :: ins x (z :: rest))` and `ih : Sorted (ins x (z :: rest))`. After
a second `by_cases hxz : x ≤ z`, rewrite `ih` with `hxz` (`simp only [ins, hxz, if_true] at ih`) and the
goal with both `hxy` and `hxz` (`simp only [ins, hxy, hxz, if_true, if_false]`), so that `ih` is literally
the second premise of `.cons`. With `hxz` alone the goal keeps its outer `if x ≤ y then … else …`.
Placeholders: `(hyb : y ≤ b) (ih : P (dropBig b (y :: ys)))`.

| Before | After |
|---|---|
| `ih : P (dropBig b (y :: ys)) ⊢ False` | `ih : P (y :: dropBig b ys) ⊢ False` |

**R9 · `omega`** **closes** linear `Nat` arithmetic from the hypotheses, including negated
comparisons: from `¬x ≤ y` it proves `y ≤ x`. Use it as a constructor premise: `.cons (by omega) ih`.
Placeholders: `(x y : Nat) (h : ¬x ≤ y)`.

| Before | After |
|---|---|
| `h : ¬x ≤ y ⊢ y ≤ x` | ∅ |

### Structural induction and using the milestone

**R10 · `induction l with | nil => … | cons y ys ih => …`** changes the **goal list**: the `[]` case and
the `y :: ys` case, with `ih` the statement for `ys`. For `isort_sorted` (`induction xs`), the goals are
shown as `Sorted (isort [])` and `Sorted (isort (x :: xs))`; they compute to `Sorted []` and
`Sorted (ins x (isort xs))`, and `exact` sees through that computation. Placeholders:
`(P : List Nat → Prop) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P l` | `⊢ P []`, `y : Nat, ys : List Nat, ih : P ys ⊢ P (y :: ys)` |

**R15 · `exact lem x ih`** **closes** the goal with a lemma you proved, its implicit arguments inferred.
For `lem : ∀ (x : Nat) {l : List Nat}, Q l → Q (f x l)`, the `{l}` is read off `ih : Q l`. In the
exercise: `exact ins_sorted x ih`, even though the goal is displayed as `Sorted (isort (x :: xs))`: it
computes to `Sorted (ins x (isort xs))`. Placeholders: `(Q : List Nat → Prop) (f : Nat → List Nat → List Nat)`.

| Before | After |
|---|---|
| `ih : Q l ⊢ Q (f x l)` | ∅ |

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1.** `Alt l → Alt (l.map (· + 1))`: `induction h` (R1), `.nil` and `.single (x + 1)` (R2), and in
the `cons` arm `simp only [List.map] at ih ⊢` (R5, R8) then `exact .cons (by omega) ih` (R3, R9).

```lean-goal
⊢ Alt (List.map (fun x => x + 1) l)
```

**W2.** `(dropBig b l).length ≤ l.length`: `induction l` (R10); in the `cons` arm `by_cases hyb : y ≤ b`
(R4), then in each branch `simp only [dropBig, hyb, if_true, List.length_cons]` (R5, R6; `if_false` and
R7 in the other branch; `List.length_cons : (a :: l).length = l.length + 1`) and `omega` (R9).

---

## Part 2 · `isort_perm`

Statement: `(isort xs).Perm xs`. Prove the MILESTONE `ins_perm (x : Nat) (l : List Nat) :
(ins x l).Perm (x :: l)` first, by `induction l` (R10) and `by_cases` on `x ≤ y` (R4) in the `cons`
case. Then `isort_perm` is an induction on `xs` that chains `ins_perm` with the IH.

**R11 · `exact .refl _`** **closes** `l.Perm l`. The lemma is `List.Perm.refl l : l.Perm l`; `exact`
also accepts the goal when both sides only *compute* to the same list, such as `(pushBack x []).Perm [x]`
or, after `simp only [ins, hxy, if_true]`, `(x :: y :: ys).Perm (x :: y :: ys)`. Placeholders:
`(x : Nat)`.

| Before | After |
|---|---|
| `⊢ (pushBack x []).Perm [x]` | ∅ |

**R12 · `List.Perm.cons`** changes the **goal**: the lemma is `l₁.Perm l₂ → (a :: l₁).Perm (a :: l₂)`,
so applying it drops a common head. As a term, `h.cons a` for `h : l₁.Perm l₂`. Placeholders:
`{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (a :: l₁).Perm (a :: l₂)` | `⊢ l₁.Perm l₂` |

**R13 · `List.Perm.trans`** changes the **goal**: the lemma is `l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`.
`refine h.trans ?_` uses `h` for the first step and leaves the rest of the chain. As a term,
`h.trans h'`. Placeholders: `{α : Type} (l₁ l₂ l₃ : List α)`.

| Before | After |
|---|---|
| `h : l₁.Perm l₂ ⊢ l₁.Perm l₃` | `h : l₁.Perm l₂ ⊢ l₂.Perm l₃` |

**R14 · `List.Perm.swap`** **closes** a swap of the first two elements. The lemma is
`List.Perm.swap x y l : (y :: x :: l).Perm (x :: y :: l)`: the arguments `x y` appear *swapped* on the
left side. Placeholders: `{α : Type} (x y : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ (y :: x :: l).Perm (x :: y :: l)` | ∅ |

In `ins_perm`'s `¬x ≤ y` branch the goal is `(y :: ins x ys).Perm (x :: y :: ys)`: one chain
`y :: ins x ys ~ y :: x :: ys ~ x :: y :: ys`, the first step by R12 on `ih`, the second by R14, glued by
R13. In `isort_perm`'s `cons` case the chain is `ins x (isort xs) ~ x :: isort xs ~ x :: xs`: the
milestone `ins_perm x (isort xs)` (R15), then R12 on `ih`, glued by R13.

**W3.** `(pushBack x l).Perm (x :: l)`: `induction l` (R10); `nil` by R11; `cons` by
`simp only [pushBack]` (R5) and `exact (ih.cons y).trans (List.Perm.swap x y ys)` (R12, R13, R14).

```lean-goal
⊢ (pushBack x l).Perm (x :: l)
```

---

## Traps

- Prove `ins_sorted` by induction on the derivation `h : Sorted l` (R1), not on the list `l`: list
  induction gives an IH that needs `Sorted ys`, and getting that from `Sorted (y :: ys)` takes extra work.
- Name the implicit arguments of `cons` with `@cons y z rest hyz hs ih`. Without `@`, they appear as
  `y✝`, `rest✝`, which you cannot mention.
- In the `cons y z rest` case with `¬x ≤ y`, the goal contains `ins x (z :: rest)`, which only
  evaluates once you split on `x ≤ z` too. Rewrite `ih` with the same `hxz` (R8) so it matches the
  goal's tail literally, and rewrite the goal with `hxy` *and* `hxz`: with `hxz` alone it keeps the
  outer `if x ≤ y`.
- `List.Perm.swap x y l` proves `(y :: x :: l).Perm (x :: y :: l)`, not the other way round (R14).
- `simp only [ins, …]` reports an unused-argument warning when `ins` has nothing left to unfold, e.g. on
  `ih` that is already unfolded. Drop the name then.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| cases of a derivation `h : Sorted l` | `induction h with \| nil => … \| single y => … \| @cons y z rest hyz hs ih => …` | R1 |
| prove `Sorted []`, `Sorted [x]` | `exact .nil`, `exact .single x` | R2 |
| prove `Sorted (x :: y :: rest)` | `exact .cons hxy hs` | R3 |
| split on a comparison | `by_cases hxy : x ≤ y` | R4 |
| unfold `ins` and pick the branch | `simp only [ins, hxy, if_true]` / `simp only [ins, hxy, if_false]` | R5–R7 |
| the same in a hypothesis | `simp only [ins, hxz, if_true] at ih` | R8 |
| `y ≤ x` from `¬x ≤ y` | `by omega` | R9 |
| induction on a list | `induction xs with \| nil => … \| cons x xs ih => …` | R10 |
| `l.Perm l` | `exact .refl _` | R11 |
| add the same head | `h.cons a` | R12 |
| chain two permutations | `h.trans h'` | R13 |
| swap the first two | `List.Perm.swap x y l` | R14 |
| use a milestone | `exact ins_sorted x ih` | R15 |
| see the state | infoview | |
