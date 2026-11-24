# M035 · Iterative in-order traversal: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, pattern matching, `List`, `::`, `++`,
pairs, `induction … with`, `rw`, `simp`, `rfl`, stating a theorem. **New here:** reasoning about a
function defined by **well-founded recursion** (`termination_by`), which only unfolds through its
equation lemmas, and **generalising** an induction over the extra argument (the stack) so that the
induction hypothesis is strong enough. Core Lean only (no Mathlib).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat`, `Tree`, `Nat × Tree`, …).
- The guide's own objects stand in for the exercise's: `BT α` (a tree with values of type `α`),
  `pushAll` (structural, like `pushLeft`), `flat` (well-founded, like `loop`), `pre` (a traversal, like
  `inorder`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `l.node x r` | `Tree.node l x r` (dot notation: `l.f a b` is `Tree.f l a b` when `l : Tree`); likewise `l.fork a r` |
| `Tree.leaf`, `BT.tip` | the empty tree |
| `.leaf`, `.node l x r` (in a pattern or argument) | the constructor `Tree.leaf` / `Tree.node`, with the type `Tree` inferred from context |
| `t.size` | `Tree.size t`, the number of nodes of `t` (same dot notation) |
| `Nat × Tree`, `(x, r)`, `p.2` | the type of pairs, a pair, and the second component of the pair `p` (`p.1` is the first) |
| `st.map (fun p => p.2.size + 1)` | `List.map`: apply the function to every element of `st` (`fun p => e` is the function `p ↦ e`) |
| `(…).sum` | `List.sum`: add up a list of numbers; so `weight st` = Σ over pairs `(x, r)` in `st` of `r.size + 1` |
| `/-- … -/` | a doc comment on the next declaration; no effect on the proof |
| `List (Nat × Tree)` | a stack: a list of pairs `(x, r)`, a saved node value `x` with its right subtree `r`; the head is the top |
| `(x, r) :: st` | the stack with `(x, r)` on top of `st` |
| `a :: as ++ bs` | `(a :: as) ++ bs`: `::` binds tighter than `++` |
| `as ++ bs ++ cs` | `(as ++ bs) ++ cs`: `++` groups to the left |
| `inorder l ++ x :: inorder r` | `inorder l ++ (x :: inorder r)` |
| `ihl : ∀ (st : List (Nat × Tree)), …` | an induction hypothesis that holds for every stack (from `generalizing st`, R1) |
| `case leaf`, `case node` | the goal for that constructor after `induction` |
| `loop.eq_1`, `loop.eq_2` | the equation lemmas of `loop`, one per clause: `loop [] = []`, `loop ((x, r) :: st) = x :: loop (pushLeft r st)` |

**Well-founded recursion.** `loop ((x, r) :: st)` calls `loop (pushLeft r st)`, which is not a
sub-term of its argument, so Lean cannot accept `loop` by structural recursion. `termination_by st =>
weight st` names a measure $w : \text{stack} \to \mathbb N$ (here: the number of tree nodes still on the
stack, `weight`) and `decreasing_by` proves $w(\texttt{pushLeft } r\ st) < w((x, r) :: st)$; both are
already written and frozen. Lean then builds `loop` from a well-founded fixpoint, which `rfl` and
`decide` do not unfold inside a proof (`#eval` still runs it). You unfold it with its equation lemmas:
`rw [loop]` or `simp [loop]` (R5, R9). On a variable stack `loop st` no clause matches and `rw [loop]`
fails ("Failed to rewrite using equation theorems"). `pushLeft` and `inorder` are structural: `rfl` sees through them (R2).

**Why a helper lemma.** `iterInorder t = loop (pushLeft t [])`. Pushing the spine of `t` leaves
`(x, r)` pairs on the stack, and the left subtree's spine is pushed on top of them, so a proof about the
empty stack `[]` meets a non-empty stack after one step. State the general fact, for an arbitrary stack
`st` underneath: what does `loop (pushLeft t st)` emit? (All of `t` in order, then whatever `loop st`
emits.) Prove it by induction on `t` generalizing `st`, then instantiate `st := []`.

---

## Part 1 · `iterInorder_eq`

Statement: for every tree `t`, `iterInorder t = inorder t`: the stack-based traversal emits the same list
as the recursive one. First a helper (milestone) about `loop (pushLeft t st)` for every `st`, then the
theorem from it with `st := []`.

### The helper: induction with the stack generalised

**R1 · `induction t generalizing s with | tip => … | fork l a r ihl ihr => …`** changes the **goal list
and the context**: one goal per constructor. `generalizing s` removes `s` from the context before the
induction and puts it back in each case, so the hypotheses are `ihl : ∀ (s : σ), P l s` and
`ihr : ∀ (s : σ), P r s`: usable at any stack. Without it, `ihl : P l s` is only about the one `s` you
started with. Placeholders: `{α σ : Type} (P : BT α → σ → Prop) (t : BT α) (s : σ)`. In the exercise:
`induction t generalizing st with | leaf => … | node l x r ihl ihr => …`.

| Before | After |
|---|---|
| `s : σ ⊢ P t s` | `⊢ P BT.tip s`, `⊢ P (l.fork a r) s` |

**R2 · `rfl`** **closes** a goal whose two sides become the same term by unfolding *structural*
definitions. `pushAll [] s` unfolds to `s` and `[] ++ m` to `m`. It does not unfold a well-founded
definition (R5). Placeholders: `{α β : Type} (g : List α → List β) (s : List α)`; `g` is any function,
playing the role of `loop`.

| Before | After |
|---|---|
| `⊢ g (pushAll [] s) = [] ++ g s` | closed |

**R3 · `rw [pushAll]`** changes the **goal**: a structural definition applied to a constructor is
replaced by that clause, once (the first match). Placeholders: `{α : Type} (x : α) (xs s : List α)`. In
the exercise `rw [pushLeft]` turns `pushLeft (l.node x r) st` into `pushLeft l ((x, r) :: st)`; it leaves
`inorder (l.node x r)` on the right side alone.

| Before | After |
|---|---|
| `⊢ P (pushAll (x :: xs) s)` | `⊢ P (pushAll xs (x :: s))` |

**R4 · `rw [ih]`** with `ih : ∀ s, F s = G s` changes the **goal**: `rw` finds an instance `F e` in the
goal, fills the `∀` with `s := e`, and replaces it by `G e`. This is where `generalizing` pays off: `e` can
be a bigger stack such as `(x, r) :: st`. A helper theorem you proved earlier works the same way
(`rw [myHelper]`). Placeholders: `{σ β : Type} (F G : σ → β) (c : σ → σ) (s₀ : σ)`.

| Before | After |
|---|---|
| `⊢ P (F (c s₀))` | `⊢ P (G (c s₀))` |

**R5 · `rw [flat]`** on a **well-founded** definition changes the **goal**: the clause that matches is
applied once, through its equation lemma (`flat.eq_3 : flat ((x :: xs) :: rest) = x :: flat (xs ::
rest)`). This is the only way to make it compute in a proof: `rfl` fails. Placeholders:
`(x : Nat) (xs : List Nat) (rest : List (List Nat))`. In the exercise `rw [loop]` pops the top pair:
`loop ((x, r) :: st)` → `x :: loop (pushLeft r st)`. A bare variable stack `loop st` matches no clause,
so it is left alone.

| Before | After |
|---|---|
| `⊢ P (flat ((x :: xs) :: rest))` | `⊢ P (x :: flat (xs :: rest))` |

### Closing a list equation

**R6 · `List.append_assoc`** changes the **goal**. The lemma is `as ++ bs ++ cs = as ++ (bs ++ cs)`.
Placeholders: `{α : Type} (as bs cs : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs ++ cs)` | `⊢ P (as ++ (bs ++ cs))` |

**R7 · `List.cons_append`** changes the **goal**. The lemma is `a :: as ++ bs = a :: (as ++ bs)`, i.e.
`(a :: as) ++ bs = a :: (as ++ bs)`. Placeholders: `{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R8 · `simp [d]`** **closes** a list equation after unfolding the structural definition `d` on a
constructor: R6 and R7 are `simp` lemmas, so `simp` reassociates by itself until both sides agree.
Placeholders: `{α : Type} (l r : BT α) (a : α) (s : List α)`, `d := pre`. In the exercise, after the four
rewrites the goal is `inorder l ++ x :: (inorder r ++ loop st) = inorder (l.node x r) ++ loop st`, and
`simp [inorder]` closes it the same way.

| Before | After |
|---|---|
| `⊢ a :: (pre l ++ (pre r ++ s)) = pre (l.fork a r) ++ s` | closed |

### The main theorem from the helper

Unfold `iterInorder` (a plain definition: `simp only [iterInorder]` or `rw [iterInorder]`), rewrite with
the helper at `st := []` (R4), evaluate `loop []` (R9), drop `++ []` (R10). One `simp` given the
definition, the helper and `loop` does all four.

**R9 · `rw [flat]`** on the empty stack changes the **goal**: `flat []` → `[]` (`flat.eq_1`). Also a
well-founded definition, so `rfl` fails even on this. In the exercise: `loop []` → `[]`.

| Before | After |
|---|---|
| `⊢ P (flat [])` | `⊢ P []` |

**R10 · `List.append_nil`** changes the **goal**. The lemma is `as ++ [] = as`. Placeholders:
`{α : Type} (as : List α)`. (`[] ++ as = as` holds by `rfl`; `as ++ []` needs this lemma, because `++`
recurses on its left argument.)

| Before | After |
|---|---|
| `⊢ P (as ++ [])` | `⊢ P as` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: the top list of a `flat` stack comes out first.** `flat (m :: rest) = m ++ flat rest` by induction
on `m` (`rest` stays fixed in the recursion, so no `generalizing`). The tactics run on the first open goal:
`nil` with R5, R2; then `cons` with R5, R4, R7 (`rw` closes the last goal by `rfl` itself):

```lean-goal
⊢ flat (m :: rest) = m ++ flat rest
⊢ flat ([] :: rest) = [] ++ flat rest
⊢ flat rest = [] ++ flat rest
⊢ flat ((x :: xs) :: rest) = x :: xs ++ flat rest
⊢ x :: flat (xs :: rest) = x :: xs ++ flat rest
⊢ x :: (xs ++ flat rest) = x :: xs ++ flat rest
```

**W2: an accumulator needs `generalizing`.** `pushAll xs s = xs.reverse ++ s`. The recursive call is
`pushAll xs (x :: s)`, at a different `s`, so the induction is `generalizing s` (R1) and
`ih : ∀ (s : List α), pushAll xs s = xs.reverse ++ s`. Then R2 for `nil`; R3, R4 for `cons`, and `simp`
(with `List.reverse_cons : (a :: as).reverse = as.reverse ++ [a]` and R6) closes:

```lean-goal
⊢ pushAll xs s = xs.reverse ++ s
⊢ pushAll [] s = [].reverse ++ s
⊢ pushAll (x :: xs) s = (x :: xs).reverse ++ s
⊢ pushAll xs (x :: s) = (x :: xs).reverse ++ s
⊢ xs.reverse ++ x :: s = (x :: xs).reverse ++ s
```

**W3: computing with a well-founded definition.** `simp [flat]` applies the equation lemmas repeatedly
and proves `flat [[1, 2], [], [3]] = [1, 2, 3]`; `rfl` and `decide` do not.

---

## Traps

- `rfl`, `decide` and `by simp` without the name do not unfold `loop`: it is defined by well-founded
  recursion. Name it: `rw [loop]`, `simp [loop]`.
- Induction on `t` with the stack fixed gives `ihl : loop (pushLeft l st) = …` for the original `st`
  only, but the `node` case needs it at `(x, r) :: st`. Write `generalizing st` (R1).
- Proving `iterInorder t = inorder t` directly by induction gets stuck for the same reason: the stack
  under the left spine is not `[]`. Prove the general helper first, then specialise it.
- A helper theorem goes **above** the main theorem (outside the spec regions); Lean reads top to bottom.
- `rw [loop]` rewrites the first `loop` application that matches a clause. On `loop st` with `st` a
  variable it fails: Lean cannot tell which clause applies. Do `rw [pushLeft, ihl]` first so the stack
  has the shape `(x, r) :: st`.
- `a :: as ++ bs` is `(a :: as) ++ bs`, not `a :: (as ++ bs)` (R7).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with an IH for every stack | `induction t generalizing st with \| leaf => … \| node l x r ihl ihr => …` | R1 |
| close by unfolding structural defs | `rfl` | R2 |
| one step of a structural def | `rw [pushLeft]` | R3 |
| use the IH / a helper at a bigger stack | `rw [ihl]`, `rw [myHelper]` | R4 |
| one step of a well-founded def | `rw [loop]` (equation lemmas `loop.eq_1`, `loop.eq_2`) | R5, R9 |
| reassociate `++` | `rw [List.append_assoc]` | R6 |
| `(a :: as) ++ bs → a :: (as ++ bs)` | `rw [List.cons_append]` | R7 |
| close a list equation after unfolding | `simp [inorder]` | R8 |
| `as ++ [] → as` | `rw [List.append_nil]` | R10 |
| evaluate a well-founded def | `simp [loop]` | W3 |
| see the state | infoview | |
