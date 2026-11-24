# M019 · BST insert: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive` types, pattern-matching definitions,
`if … then … else`, `∧ ∨ ↔`, `simp`, `rw`, `exact`, `induction` on `Nat`/`List`, `grind` (E028),
`def … : Prop` and `unfold` (E030). **New here:** proving facts about a recursive program on a
user-defined tree: induction on the tree, unfolding one recursive call and splitting its `if`s,
recursive functions into `Prop` (`mem`, `All`) that unfold to `∨`/`∧`, **inductive predicates**
(`BST`, explained in Part 2), induction on a proof of one, and a helper lemma (milestone) proved
first. Core Lean only (no Mathlib).

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop → Prop` when the changing part is itself
  a proposition). The step changes only the part inside `P (…)`. `G : Prop` is a goal the step leaves
  alone (the step works on the context). `Q : BT → Prop` is an arbitrary property of trees.
- The guide's own objects (not the exercise's): `BT` with constructors `BT.tip`, `BT.bin l a r`;
  `has y t` (label `y` occurs in `t`), `every p t` (all labels satisfy `p`), `mirror`, `prune x t`
  (drop nodes below `x`), and the inductive predicate `Heap t` (max-heap).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `l.node k r` | `Tree.node l k r` (dot notation: `l` is the first explicit argument, of type `Tree`) |
| `Tree.leaf`, `(insert x l).node k r` | the empty tree; the node with left subtree `insert x l` |
| `l.bin a r`, `BT.tip` | the same for the guide's tree `BT` |
| `mem y t` | `y` is a key of `t`: a `Prop` computed by recursion on `t` (`False` at a leaf, `mem y l ∨ y = k ∨ mem y r` at a node) |
| `All p t` | every key of `t` satisfies `p`: `True` at a leaf, `All p l ∧ p k ∧ All p r` at a node |
| `fun x => x < k`, `fun x => k < x` | the predicates written `(· < k)`, `(k < ·)` in the source: "is less than `k`", "is greater than `k`". The `x` here is a bound variable, not the `x : Nat` in the context |
| `(y = x ∨ mem y l) ∨ y = k ∨ mem y r` | `∨` nests to the right (`A ∨ B ∨ C` is `A ∨ (B ∨ C)`), so parentheses show a left disjunct that is itself an `∨`; `grind` (R6) regroups them |
| `BST t` | `t` is a search tree: a proof built only from the constructors `BST.leaf`, `BST.node` |
| `if x < k then u else v` | the body of `insert` after unfolding one call (R3); `split` it (R4) |
| `h✝`, `h✝¹` | inaccessible hypotheses made by `split` (`h✝¹` is the older one, after two `split`s): you cannot type their names; `assumption`, `‹x < k›` and `grind` still use them |
| `ihl : All p l → All p (insert x l)` | an induction hypothesis that is an implication, because `ht : All p t` was carried into the induction (R1) |
| `case node`, `case node.isTrue` | goal tags: the `node` arm of `induction`, then the `then` branch of a `split` (`isFalse` is the `else` branch) |
| `inst✝ : Decidable c` | the instance that lets `if c then … else …` be computed; ignore it |

---

## Part 1 · `mem_insert`

Statement: `y` is a key of `insert x t` exactly when `y = x` or `y` was already a key of `t`.

**R1 · `induction t with | tip => ?_ | bin l a r ihl ihr => ?_`** changes the **goal list** and the
**context**: one goal per constructor of the tree type; the `bin` goal gets the subtrees `l a r` and
one induction hypothesis per subtree. Placeholders: `(P : BT → Prop) (t : BT)`. In the exercise the
constructors are `leaf` and `node l k r`.

| Before | After |
|---|---|
| `⊢ P t` | `⊢ P BT.tip`, `l : BT, a : Nat, r : BT, ihl : P l, ihr : P r ⊢ P (l.bin a r)` |

A hypothesis about `t` that is in the context (`ht : Q t`, with `Q : BT → Prop`) moves into the
induction: each goal gets its own copy of `ht`, and the hypotheses become implications.

| Before | After |
|---|---|
| `ht : Q t ⊢ P t` | `ht : Q BT.tip ⊢ P BT.tip`, `ihl : Q l → P l, ihr : Q r → P r, ht : Q (l.bin a r) ⊢ P (l.bin a r)` |

**R2 · `simp only [f]`** changes the **goal**: a recursive function applied to a constructor is replaced
by that constructor's arm. A call on anything else (`has y (prune x l)`, `mem y (insert x l)`) stays,
because Lean cannot tell which arm applies. Placeholders: `(y a : Nat) (l r : BT) (P : Prop → Prop)`.
In the leaf case `simp [insert, mem]` (plain `simp`, which also knows `False ∨ A ↔ A`) closes the goal.

| Before | After |
|---|---|
| `⊢ P (has y (l.bin a r))` | `⊢ P (y = a ∨ has y l ∨ has y r)` |

**R3 · `unfold f`** changes the **goal**: one call `f x (bin l a r)` becomes the body of the matching arm,
`if` included. The recursive calls inside the body stay folded. Placeholders: `(x a : Nat) (l r : BT)
(P : BT → Prop)`. In the exercise: `unfold insert` turns `insert x (l.node k r)` into the two nested `if`s.

| Before | After |
|---|---|
| `⊢ P (prune x (l.bin a r))` | `⊢ P (if a < x then prune x r else (prune x l).bin a r)` |

**R4 · `split`** changes the **goal list** and the **context**: the first `if c then u else v` in the goal
gives two goals, one per branch, each with the branch condition as an inaccessible hypothesis `h✝`.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (u v : α) (P : α → Prop)`; `[Decidable c]` holds for
`x < k` on `Nat`. A nested `else if` is split by a second `split` in the `isFalse` goal.

| Before | After |
|---|---|
| `⊢ P (if c then u else v)` | `h✝ : c ⊢ P u`, `h✝ : ¬c ⊢ P v` |

**R5 · `simp only [ih]`** with `ih : A ↔ B` changes the **goal**: every occurrence of the proposition `A`
becomes `B` (an `↔` rewrites like `=`). This is how the induction hypothesis
`ihl : mem y (insert x l) ↔ y = x ∨ mem y l` is used. Combine it with R2: `simp only [mem, ihl]`.
Placeholders: `(A B : Prop) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P A` | `⊢ P B` |

**R6 · `grind`** **closes** the goal by propositional reasoning (`∨ ∧ ¬ ↔`, reordering and
regrouping disjunctions), equalities and linear arithmetic over `Nat`, using all hypotheses (the `h✝`
from `split` included). Subterms such as `mem y l` are opaque propositions to it. Example:
from `h1 : ¬a < b` and `h2 : ¬b < a` it derives `a = b`, which the goal below needs.
`omega` cannot do this: it handles only arithmetic, not `∨` of arbitrary propositions.

```lean-goal
⊢ A ∨ y = b ∨ B ↔ y = a ∨ B ∨ A ∨ y = b
```

**W1** (`has y (mirror t) ↔ has y t`) chains R1, then `simp only [mirror, has, ihl, ihr]` (R2 + R5),
then R6.

---

## Part 2 · `insert_bst`

Statement: if `t` is a BST, so is `insert x t`.

**Inductive predicate.** `inductive BST : Tree → Prop` defines `BST t` by rules instead of by
recursion: its constructors are the only ways to build a proof. `BST.leaf : BST Tree.leaf`, and
`BST.node : All (· < k) l → All (k < ·) r → BST l → BST r → BST (l.node k r)` (with `l k r` implicit,
in `{…}`). So you *prove* `BST (…)` by applying a constructor (R10), and you *use* `h : BST t` by
induction on `h` (R9): one goal per constructor, with the constructor's arguments in the context. The
guide's `Heap` is defined the same way.

The `node` constructor of `BST` needs
`All (· < k) l` and `All (k < ·) r`, so the new left subtree `insert x l` must still have all keys
`< k`. That is a separate fact about `All`, the **milestone**:

```
theorem all_insert (p : Nat → Prop) (x : Nat) (t : Tree) (ht : All p t) (hx : p x) :
    All p (insert x t)
```

State it (outside the spec regions, before `insert_bst`) and prove it first, by R1 (with `ht`
carried), R7, R3, R4, R8. W2 is the same pattern for `prune` and `every`.

**R7 · `obtain ⟨ha, hl, hr⟩ := h`** changes the **context**: `h : every p (bin l a r)` is replaced by its
three parts. `every p (bin l a r)` unfolds to `p a ∧ every p l ∧ every p r`, and `obtain` sees through the
definition by itself. Placeholders: `(p : Nat → Prop) (a : Nat) (l r : BT) (G : Prop)`. In the exercise
`All p (l.node k r)` gives `All p l`, `p k`, `All p r`, in that order.

| Before | After |
|---|---|
| `h : every p (l.bin a r) ⊢ G` | `ha : p a, hl : every p l, hr : every p r ⊢ G` |

**R8 · `exact ⟨ha, hl, hr⟩`** **closes** `every p (bin l a r)` from proofs of the three parts; the anonymous
constructor also sees through the definition (`⟨_, _, _⟩` is `⟨_, ⟨_, _⟩⟩`). In the exercise the new
left part is the induction hypothesis applied: `ihl hl`.

```lean-goal
⊢ every p (l.bin a r)
```

**R9 · `induction h with | tip => ?_ | @bin l a r hl hr bl br ihl ihr => ?_`** changes the **goal list**:
induction on a proof `h : Heap t`, one goal per constructor of the inductive predicate. `@bin` lets you
name the constructor's implicit arguments `{l a r}`; then come its explicit arguments `hl hr bl br`, then one
induction hypothesis per recursive argument (`bl : Heap l` gives `ihl : Q l`). Placeholders:
`(Q : BT → Prop) (t : BT) (h : Heap t)`. In the exercise: `@node l k r hl hr bl br ihl ihr`, with
`ihl : BST (insert x l)`.

| Before | After |
|---|---|
| `h : Heap t ⊢ Q t` | `⊢ Q BT.tip`, `hl : every (fun x => x ≤ a) l, bl : Heap l, ihl : Q l ⊢ Q (l.bin a r)` |

**R10 · `exact .bin h₁ h₂ h₃ h₄`** **closes** `Heap (bin l a r)` with the constructor: `.bin` is
`Heap.bin`, read off the expected type. `trivial` proves `every p BT.tip` because it unfolds to `True`.
In the exercise: `.node …` for `BST`, and `trivial` for `All p Tree.leaf`.

```lean-goal
⊢ Heap (BT.tip.bin a BT.tip)
```

`exact` compares types up to computation, so a function applied to a constructor needs no unfolding
first: the same term closes the goal below, because `mirror (BT.tip.bin a BT.tip)` computes to
`BT.tip.bin a BT.tip`. In the exercise the `leaf` goal `BST (insert x Tree.leaf)` is of this kind:
`insert x Tree.leaf` computes to `Tree.leaf.node x Tree.leaf`.

```lean-goal
⊢ Heap (mirror (BT.tip.bin a BT.tip))
```

**R11 · `(by assumption)`** **closes** a goal that is one of the hypotheses, compared up to unfolding:
`h : x < k` proves `(fun y => y < k) x`. Write it where a term is expected; it finds `h✝` from `split` too.
`‹x < k›` does the same for a stated type.

```lean-goal
⊢ (fun y => y < k) x
```

**R12 · `lem _ s hs`** is a **term**: `_` stands for an explicit argument Lean can infer, here `p` from
`hs : every (fun x => x < k) s`. Placeholders: `(f : BT → BT) (k : Nat) (s : BT)`,
`lem : ∀ (p : Nat → Prop) (s : BT), every p s → every p (f s)`. In the exercise the milestone is used as
`all_insert _ x l hl (by assumption)`: `p := (· < k)` from `hl`, and `(by assumption)` is R11 on `x < k`.

```lean-goal
⊢ every (fun x => x < k) (f s)
```

**W2** (`every_prune`) is a milestone of the same shape as `all_insert`; **W3** (`prune` keeps `Heap`)
uses it the way `insert_bst` uses `all_insert`: R9, R3, R4, then R10 with R12 in the `else` branch.

---

## Traps

- `induction h` on `h : BST t` is not `induction t`: the `node` goal then already has `hl hr bl br` (the
  invariant's pieces) and `ihl : BST (insert x l)`. Without `@`, the implicit `l k r` get inaccessible
  names `l✝ k✝ r✝`.
- `simp only [mem]` unfolds `mem y (l.node k r)` but not `mem y (insert x l)`: rewrite that one with the
  induction hypothesis (R5), which must be in the same `simp only [mem, ihl]` call.
- `split` splits only the outermost `if`; the `else if` needs a second `split` in the `isFalse` goal.
- `omega` fails on goals with `∨` of propositions like `mem y l`; use `grind` (R6).
- The milestone needs `hx : p x` as a hypothesis: `insert` adds `x` itself, so `All p` survives only if
  `p x`. In `insert_bst`, `p x` is `x < k`, the `h✝` from the first `split`.
- `t1 ; t2` runs `t2` on the first goal only; use `·` to work on each goal after `split`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a tree | `induction t with \| leaf => … \| node l k r ihl ihr => …` | R1 |
| a function on a constructor → its arm | `simp only [mem]` / `simp [insert, mem]` | R2 |
| one call of a recursive function → its body | `unfold insert` | R3 |
| split an `if` in the goal | `split` | R4 |
| use an `↔` induction hypothesis | `simp only [mem, ihl]` | R5 |
| reorder `∨`, use `¬x < k`, `¬k < x` | `grind` | R6 |
| `All p (l.node k r)` → three facts | `obtain ⟨hl, hk, hr⟩ := ht` | R7 |
| prove `All p (l.node k r)` | `exact ⟨_, _, _⟩` | R8 |
| induction on `h : BST t` | `induction h with \| leaf => … \| @node l k r hl hr bl br ihl ihr => …` | R9 |
| build `BST (…)` | `exact .node _ _ _ _`, `trivial` for `All p Tree.leaf` | R10 |
| a goal that is a hypothesis | `(by assumption)` | R11 |
| let Lean infer an argument | `all_insert _ x l hl …` | R12 |
| see the state | infoview | |
