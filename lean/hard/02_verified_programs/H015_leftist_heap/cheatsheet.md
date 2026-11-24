# H015 · Leftist heap: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `induction`, `cases`, `omega`, `have`/`show`,
inductive types, Props defined by pattern matching, `termination_by`, `<;>`). **New here:** Lean core's
`List.Perm` and `List.count` (no Mathlib), `fun_induction` (induction that follows the branches of a
function), `generalizing`, and the `rfl` pattern that substitutes an equation.

The guide never touches `Heap`, `merge` or `mkNode`. It uses its own objects:

| Guide object | Analogue in the exercise |
|---|---|
| `Tree` (`tip`, `bin x l r`) | `Heap` (`leaf`, `node rk x l r`) |
| `Tree.size`, `Tree.elems` | `Heap.rank`, `toList` |
| `pick x a b` (bigger child left) | `mkNode x a b` |
| `AllGe lo t`, `Above lo l` | `HeapOrd lo h` |
| `top t : Option Nat` | `findMin h` |
| `mergeL xs ys` (list merge) | `merge h1 h2` (same four-branch shape) |

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : α → Prop`), or a whole goal `P : Prop`. The step changes only the
  part inside `P (…)`.
- `{α : Type}` is any type. `[BEq α]` (a type with a Boolean equality test `==`) is met by `Nat`.
- "closed" means the step leaves no goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a reordering of `l₁` (same elements, same multiplicities). Written `l₁ ~ l₂` on paper |
| `List.count a l` | number of occurrences of `a` in `l` |
| `(b == a) = true` | the Boolean test `b == a` came out `true`; for `Nat` this is the same as `b = a` |
| `x :: l`, `l₁ ++ l₂` | cons, append |
| `a ∈ l` | `a` occurs in `l` |
| `∀ (y : Nat), y ∈ l → P y` | how the infoview prints the spec's `∀ y ∈ l, P y` (for every `y` in `l`) |
| `l₁.append l₂` | `List.append l₁ l₂`, the same as `l₁ ++ l₂`; shows up after `apply List.Perm.cons` takes a goal `x :: l ++ t` apart (`simp` turns it back) |
| `∀ {lo : Nat}, A → B` | an IH whose `lo` is implicit (braces): Lean fills `lo` from the type of the argument of type `A`, so call it as `ih o`, not `ih x o` |
| `Heap.node rk x l r`, `Heap.leaf` | the constructors; `.node`, `.leaf` in the source |
| `h.rank`, `(toList h).length` | dot notation: `Heap.rank h`, `List.length (toList h)` |
| `some m`, `none` | the two values of `Option Nat`; `findMin` returns one |
| `x✝`, `h✝`, `ih1✝` | inaccessible names Lean made up; name them with `with \| case3 x … ih => …` |
| `case case1` … `case case4` | the four branches of `merge` after `fun_induction` |
| `case isTrue`, `case isFalse` | the two branches after `split` on an `if` |
| `case inl`, `case inr.inl`, `case refl`, `case node.refl` | goals made by `rcases`/`cases` (`refl`: an equation was used up by substitution) |
| `x✝ : h✝ = Heap.leaf → False` | in `merge`'s `case2`: the first pattern (`.leaf, h`) did not match |

---

## Part 1 · `mkNode_perm` (milestone)

Statement: the list of `mkNode x a b` is a reordering of `x :: (toList a ++ toList b)`. Open
`mkNode`'s `if`; in one branch the lists are equal, in the other the children are swapped.

**R1 · `unfold f`** changes the **goal**: `f args` becomes the body of `f` with the arguments put in.
Placeholders: `(P : Tree → Prop) (x : Nat) (a b : Tree)`.

| Before | After |
|---|---|
| `⊢ P (pick x a b)` | `⊢ P (if b.size ≤ a.size then Tree.bin x a b else Tree.bin x b a)` |

**R2 · `split`** changes the **goal list**: a goal containing `if c then t else e` becomes two goals, one
with `h✝ : c` and `t`, one with `h✝ : ¬c` and `e`. Placeholders: `{α : Type} (c : Prop) [Decidable c]
(t e : α)` (`Decidable c`: Lean can compute whether `c` holds; `b.rank ≤ a.rank` on `Nat` qualifies).
Use `by assumption` or `by omega` to use the unnamed `h✝`.

| Before | After |
|---|---|
| `⊢ P (if c then t else e)` | `h✝ : c ⊢ P t`, `h✝ : ¬c ⊢ P e` |

**R3 · `simp [f]` on a `Perm` goal** **closes** it when both sides unfold to the same list:
`List.Perm.refl : l.Perm l` is a simp lemma. Placeholders: `(x : Nat) (a b : Tree)`.

| Before | After |
|---|---|
| `⊢ (Tree.bin x a b).elems.Perm (x :: (a.elems ++ b.elems))` | closed |

**R4 · `List.Perm.cons`** changes the **goal**: `List.Perm.cons (x : α) : l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)`.
With `apply` it drops a common head. As a term, `hp.cons x` (dot notation) turns `hp : l₁.Perm l₂`
into `(x :: l₁).Perm (x :: l₂)`. Placeholders: `{α : Type} (x : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (x :: l₁).Perm (x :: l₂)` | `⊢ l₁.Perm l₂` |

**R5 · `List.perm_append_comm`** **closes** the goal: `(l₁ ++ l₂).Perm (l₂ ++ l₁)` (arguments implicit).
Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (l₁ ++ l₂).Perm (l₂ ++ l₁)` | closed |

---

## Part 2 · `merge_heapOrd` (milestone)

Statement: if `h1` and `h2` are heap-ordered above `lo`, so is `merge h1 h2`. First prove (as a local
`have`) that `mkNode` keeps the order (R1, R2, R6); then follow `merge` with `fun_induction`, generalizing
`lo`: in `case3` the right spine is merged under the new root `x`, so the IH is needed at bound `x`.

**R6 · `refine ⟨?_, ?_, ?_⟩` (or `exact ⟨…⟩`) on a defined Prop** changes the **goal list**.
`AllGe lo (.bin x l r)` unfolds *by definition* to `lo ≤ x ∧ AllGe lo l ∧ AllGe lo r`, so the anonymous
constructor splits it without `unfold`. The same holds for `HeapOrd lo (.node …)`, `Leftist (.node …)`
and `IsHeap h` (`= HeapOrd 0 h ∧ Leftist h`). Placeholders: `(lo x : Nat) (l r : Tree)`.

| Before | After |
|---|---|
| `⊢ AllGe lo (Tree.bin x l r)` | `⊢ lo ≤ x`, `⊢ AllGe lo l`, `⊢ AllGe lo r` |

**R7 · `fun_induction f a b`** changes the **goal list**: one goal per branch of `f`'s definition, with
an induction hypothesis `ih1✝` for the recursive call of that branch. It works for well-founded
recursion like `merge` (each call shrinks *some* argument), where plain `induction` on one argument
fails. `mergeL` has exactly `merge`'s shape. Placeholders: `(xs ys : List Nat)`.

| Branch | State |
|---|---|
| before | `⊢ (mergeL xs ys).length = xs.length + ys.length` |
| `case1` (`[], ys`) | `ys✝ : List Nat ⊢ ys✝.length = [].length + ys✝.length` |
| `case2` (`xs, []`) | `x✝ : xs✝ = [] → False ⊢ xs✝.length = xs✝.length + [].length` |
| `case3` (`x ≤ y`) | `h✝ : x✝ ≤ y✝, ih1✝ : (mergeL xs✝ (y✝ :: ys✝)).length = xs✝.length + (y✝ :: ys✝).length ⊢ (x✝ :: mergeL xs✝ (y✝ :: ys✝)).length = (x✝ :: xs✝).length + (y✝ :: ys✝).length` |
| `case4` (`¬x ≤ y`) | `h✝ : ¬x✝ ≤ y✝, ih1✝ : (mergeL (x✝ :: xs✝) ys✝).length = (x✝ :: xs✝).length + ys✝.length ⊢ (y✝ :: mergeL (x✝ :: xs✝) ys✝).length = (x✝ :: xs✝).length + (y✝ :: ys✝).length` |

For `merge h1 h2` the four cases are the same: `case1` is `.leaf, h`; `case2` is `h, .leaf` (with
`h ≠ .leaf`); `case3`/`case4` are `.node r1 x l1 r1', .node r2 y l2 r2'` with `x ≤ y` / `¬x ≤ y`. The
goal is then about `mkNode x l1 (merge r1' …)`; `fun_induction` does not unfold `merge`.
Hypotheses about the arguments (`l1 : Leftist h1`) are taken into the IH as premises and come back in
each case about that case's pattern: in `merge_leftist`'s `case3` you get
`l1 : Leftist (Heap.node r1 x l1✝ r1')`, `ih : Leftist r1' → Leftist (Heap.node r2 y l2✝ r2') → …`.
The hypothesis keeps the name `l1`, so the pattern variable named `l1` in `with` becomes `l1✝`;
name the children `l1'`, `l2'` there instead.

**R8 · `fun_induction f a b generalizing n`** changes the **goal list** like R7, but each IH starts with
`∀ n`, so you may use it at a *different* `n`. Hypotheses that mention `n` (like `o1`, `o2`) are moved
into the IH as premises. Name the `✝` variables with
`with | case1 ys => … | case2 xs hxs => … | case3 x xs y ys hxy ih => … | case4 x xs y ys hxy ih => …`:
pattern variables, then the `if` condition, then the IH (W2). For `merge`:
`| case3 r1 x l1 r1' r2 y l2 r2' hxy ih`. Placeholders: `(n : Nat) (P : List Nat → Nat → Prop)`.

| Before | After (`case3`; `case4` alike) | New IH in `case3` |
|---|---|---|
| `⊢ P (mergeL xs ys) n` | `n : Nat ⊢ P (x✝ :: mergeL xs✝ (y✝ :: ys✝)) n` | `ih1✝ : ∀ (n : Nat), P (mergeL xs✝ (y✝ :: ys✝)) n` |

**R9 · `o.1`, `o.2.1`, `o.2.2`** change the **context** (with `have`) or build a term: the projections of
a hypothesis whose type unfolds to `A ∧ B ∧ C` (`∧` nests to the right: `.2.1` is `B`).
Placeholders: `(o : AllGe lo (.bin x l r))`.

| Before | After `have hr := o.2.2` |
|---|---|
| `o : AllGe lo (Tree.bin x l r) ⊢ P` | `hr : AllGe lo r ⊢ P` |

**R10 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int`, using hypotheses with `=`, `≤`,
`<`, `¬`. Anything else (`l.rank`, `2 ^ k`, `if … then 1 else 0`) is an unknown atom; equal atoms are
recognised. Placeholders: `(x y : Nat)`.

| Before | After |
|---|---|
| `h : ¬x ≤ y ⊢ y ≤ x` | closed |

---

## Part 3 · `mkNode_leftist` (milestone)

Statement: `mkNode x a b` is leftist when `a` and `b` are. No new entries: R1, R2, then R6 with
`rfl` for the rank field and `by omega` (R10) for `r.rank ≤ l.rank`, using the `h✝` from `split`.
W1 is the same pattern on `pick`.

---

## Part 4 · `heapOrd_le` (milestone)

Statement: `HeapOrd lo h` implies every element of `toList h` is `≥ lo`. Induction on `h`, generalizing
`lo` (the children are ordered above the root `x`, not above `lo`). Because the theorem binds `lo` with
braces (`{lo : Nat}`), the IHs are `ihl : ∀ {lo : Nat}, HeapOrd lo l → ∀ (y : Nat), y ∈ toList l → lo ≤ y`:
give `ihl` the child's order fact (`ol : HeapOrd x l`) and Lean takes the bound `x` from it.

**R11 · `induction t generalizing lo`** changes the **goal list**: one goal per constructor, and each
IH starts with `∀ lo`. `with | tip => … | bin x l r ihl ihr => …` names the new variables (W5).
Placeholders: `(P : Nat → Tree → Prop) (lo : Nat) (t : Tree)`.

| Before | After | New IHs in `bin` |
|---|---|---|
| `⊢ P lo t` | `lo : Nat ⊢ P lo Tree.tip`, `x✝ : Nat, l✝ r✝ : Tree ⊢ P lo (Tree.bin x✝ l✝ r✝)` | `l_ih✝ : ∀ (lo : Nat), P lo l✝`, `r_ih✝ : ∀ (lo : Nat), P lo r✝` |

**R12 · `obtain ⟨hx, hl, hr⟩ := o`** changes the **context**: `o`, whose type unfolds to a conjunction,
is replaced by its parts. Placeholders: `(o : AllGe lo (.bin x l r))`.

| Before | After |
|---|---|
| `o : AllGe lo (Tree.bin x l r) ⊢ P` | `hx : lo ≤ x, hl : AllGe lo l, hr : AllGe lo r ⊢ P` |

**R13 · `simp only [f] at h ⊢`** changes the **context and goal**: unfold `f` (here `Tree.elems`) in `h`
and in the goal in one step; `at h` alone leaves the goal, `at ⊢` alone leaves `h`. You can add lemmas:
`simp only [toList, List.mem_cons, List.mem_append] at hy`. Placeholders: `(Q : List Nat → Prop)`.

| Before | After |
|---|---|
| `h : Q (Tree.bin x a b).elems ⊢ Q (Tree.bin x a b).elems` | `h : Q (x :: (a.elems ++ b.elems)) ⊢ Q (x :: (a.elems ++ b.elems))` |

**R14 · `List.mem_cons`** changes the **context** (`rw [List.mem_cons] at hy`):
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`. Placeholders: `{α : Type} (a b : α) (l : List α)`.

| Before | After |
|---|---|
| `hy : a ∈ b :: l ⊢ P` | `hy : a = b ∨ a ∈ l ⊢ P` |

**R15 · `List.mem_append`** changes the **context**: `List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`.
Placeholders: `{α : Type} (a : α) (s t : List α)`.

| Before | After |
|---|---|
| `hy : a ∈ s ++ t ⊢ P` | `hy : a ∈ s ∨ a ∈ t ⊢ P` |

**R16 · `rcases hy with rfl | hy | hy`** changes the **goal list**: one goal per `∨` branch. The pattern
`rfl` on `y = x` substitutes one variable for the other everywhere (here `x` becomes `y`, so `hx : P x`
becomes `hx : P y`). Placeholders: `(y x : Nat) (s t : List Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `hy : y = x ∨ y ∈ s ∨ y ∈ t ⊢ P y` | `hx : P y ⊢ P y`, `hy : y ∈ s ⊢ P y`, `hy : y ∈ t ⊢ P y` |

**R17 · `Nat.le_trans`** changes the **goal**: `Nat.le_trans : n ≤ m → m ≤ k → n ≤ k`. `apply Nat.le_trans hab`
with `hab : a ≤ b` leaves `b ≤ c`; `exact Nat.le_trans hab hbc` closes it. Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

---

## Part 5 · `heapOrd_weaken` (milestone)

Statement: `HeapOrd lo h` implies `HeapOrd 0 h`. Only the root carries the bound, so no induction: one
`cases h`.

**R18 · `cases t`** changes the **goal list**: one goal per constructor, no IH.
`cases t with | tip => … | bin x l r => …` names the variables. Placeholders: `(P : Tree → Prop) (t : Tree)`.

| Before | After |
|---|---|
| `⊢ P t` | `⊢ P Tree.tip`, `x✝ : Nat, l✝ r✝ : Tree ⊢ P (Tree.bin x✝ l✝ r✝)` |

**R19 · `trivial`** **closes** `True`, also a defined Prop that unfolds to `True` (`HeapOrd lo .leaf`,
`Leftist .leaf`). As a term, `trivial : True`. Placeholders: `(lo : Nat)`.

| Before | After |
|---|---|
| `⊢ AllGe lo Tree.tip` | closed |

**R20 · `Nat.zero_le`** **closes**: `Nat.zero_le (n : Nat) : 0 ≤ n`.

| Before | After |
|---|---|
| `⊢ 0 ≤ n` | closed |

---

## Part 6 · `merge_spec`

Statement: merging two heaps gives a heap whose list is a reordering of `toList h1 ++ toList h2`.
Prove two more helpers first, each by `fun_induction merge h1 h2` (R7), then bundle with R6:

- `merge_leftist (h1 h2) : Leftist h1 → Leftist h2 → Leftist (merge h1 h2)`: in `case3`/`case4` apply
  `mkNode_leftist` to a child's `Leftist` (R9: `l1.2.2.1`) and the IH.
- `merge_perm (h1 h2) : (toList (merge h1 h2)).Perm (toList h1 ++ toList h2)`: `case1`/`case2` by R3;
  `case3`/`case4` start with `refine (mkNode_perm _ _ _).trans ?_` (R21), then `simp only [toList] at ih ⊢`
  (R13). `case3` is W4 (R4, R22, R23); `case4` must move `y` past `toList h1`, which is W3 (R24–R26, R10).

**R21 · `refine h₁.trans ?_`** changes the **goal**: `List.Perm.trans : l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`.
Given `h₁ : l₁.Perm l₂`, what is left is `l₂.Perm l₃`. Placeholders: `{α : Type} (l₁ l₂ l₃ : List α)`.

| Before | After |
|---|---|
| `⊢ l₁.Perm l₃` | `⊢ l₂.Perm l₃` |

**R22 · `List.Perm.append_left`** changes the **goal**:
`List.Perm.append_left (l : List α) : t₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)`: drop a common prefix.
Placeholders: `{α : Type} (l t₁ t₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (l ++ t₁).Perm (l ++ t₂)` | `⊢ t₁.Perm t₂` |

**R23 · `List.append_assoc`** changes the **goal**: `List.append_assoc : a ++ b ++ c = a ++ (b ++ c)`
(`++` groups to the left). `simp` uses it by itself, then closes `l.Perm l` (R3): that is the
`(by simp)` in W4. Placeholders: `{α : Type} (a b c : List α)`.

| Before | After |
|---|---|
| `⊢ P (a ++ b ++ c)` | `⊢ P (a ++ (b ++ c))` |

**R24 · `List.perm_iff_count`** changes the **goal** (or a hypothesis, with `at ih ⊢`):
`List.perm_iff_count : l₁.Perm l₂ ↔ ∀ a, List.count a l₁ = List.count a l₂` (needs `[BEq α] [LawfulBEq α]`,
i.e. `==` agrees with `=`; `Nat` qualifies). Placeholders: `(l₁ l₂ : List Nat)`.

| Before | After |
|---|---|
| `⊢ l₁.Perm l₂` | `⊢ ∀ (a : Nat), List.count a l₁ = List.count a l₂` |

**R25 · `List.count_append`** changes the **goal**:
`List.count_append : List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂`.
Placeholders: `(a : Nat) (l₁ l₂ : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.count a (l₁ ++ l₂))` | `⊢ P (List.count a l₁ + List.count a l₂)` |

**R26 · `List.count_cons`** changes the **goal**:
`List.count_cons : List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0`.
The `if` is one atom for `omega` (R10): it cancels when it appears on both sides.
Placeholders: `(a b : Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.count a (b :: l))` | `⊢ P (List.count a l + if (b == a) = true then 1 else 0)` |

**W3: a permutation by counting** (the shape of `merge_perm`'s `case4`). With
`ih : u.Perm (s ++ t)`: `rw [List.perm_iff_count] at ih ⊢`, `intro a`, `have := ih a`,
`simp only [List.count_append, List.count_cons] at this ⊢`, `omega`. The goals:

```lean-goal
⊢ (y :: u).Perm (s ++ y :: t)
⊢ ∀ (a : Nat), List.count a (y :: u) = List.count a (s ++ y :: t)
⊢ List.count a (y :: u) = List.count a (s ++ y :: t)
⊢ (List.count a u + if (y == a) = true then 1 else 0) = List.count a s + (List.count a t + if (y == a) = true then 1 else 0)
```

**W4: prefix and reassociation** (the shape of `case3`): `apply List.Perm.cons`,
`refine (List.Perm.append_left a ih).trans ?_`, `simp`:

```lean-goal
⊢ (x :: (a ++ d)).Perm (x :: (a ++ b ++ c))
⊢ (a ++ d).Perm (a ++ b ++ c)
⊢ (a ++ (b ++ c)).Perm (a ++ b ++ c)
```

---

## Part 7 · `insert_spec`

Statement: `insert x h` is a heap holding `x :: toList h`. `insert x h` is by definition
`merge (.node 1 x .leaf .leaf) h`, so this is `merge_spec` applied to the singleton, once you prove the
singleton is a heap: an `IsHeap` term built with R6, R20, R19, `rfl`, and

**R27 · `Nat.le_refl`** **closes**: `Nat.le_refl (n : Nat) : n ≤ n` (here `Heap.leaf.rank ≤ Heap.leaf.rank`, which is `0 ≤ 0`).

| Before | After |
|---|---|
| `⊢ n ≤ n` | closed |

The list side needs nothing: `toList (.node 1 x .leaf .leaf) ++ toList h` reduces to `x :: toList h`.

---

## Part 8 · `findMin_spec`

Statement: if `findMin h = some m`, then `m` is in the heap and below every element. `cases h`
(R18); `cases hm` in both cases; then R30 and `heapOrd_le` at bound `m` (R31).

**R28 · `cases h` with `h : top (.bin a l r) = some b`** changes the **context**: `cases` computes the left
side to `some a`, and since `some` is injective, one variable is substituted for the other everywhere and
`h` disappears. In the example `b` becomes `a`. In the exercise `hm : findMin (.node rk x l r) = some m`
turns the root `x` into `m` (the goal becomes `m ∈ toList (Heap.node rk m l r) ∧ …`), so you keep writing
`m`. Which name survives is Lean's choice: read the new context (Traps). Placeholders: `(a b : Nat) (l r : Tree)`.

| Before | After |
|---|---|
| `h : top (Tree.bin a l r) = some b ⊢ P b` | `ha : P a ⊢ P a` |

**R29 · `cases h` with `h : top .tip = some b`** **closes** the goal: the left side computes to `none`,
and `none = some b` has no proof. This disposes of the `leaf` case.

| Before | After |
|---|---|
| `h : top Tree.tip = some b ⊢ P` | closed |

**R30 · `List.mem_cons_self`** **closes**: `List.mem_cons_self : a ∈ a :: l` (all arguments implicit, so
write it without arguments). Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ a ∈ a :: l` | closed |

**R31 · named argument `f (x := v)`** changes how `f` is elaborated: it fixes the implicit argument named
`x`. `heapOrd_le (lo := m) ⟨…⟩` says which bound to use before the anonymous constructor ⟨…⟩ is checked,
which Lean could not infer otherwise. Example: `Nat.le_trans {n m k : Nat}`, so `(m := b)` picks the
middle term.

| Before | After `apply Nat.le_trans (m := b)` |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b ≤ c` |

---

## Part 9 · `deleteMin_spec`

Statement: `deleteMin h` is a heap, and `m :: toList (deleteMin h)` is a reordering of `toList h`.
`cases h`, `cases hm` (R18, R28, R29); `obtain` the parts of `w` (R12). `IsHeap` is an `∧` of two
defined conjunctions, so a nested pattern `⟨⟨…, …, …⟩, …, …, …, …⟩` splits it in one step (`_` drops a
part you do not need). The children `l r` are only
`HeapOrd m`, so weaken them with `heapOrd_weaken` before calling `merge_spec l r`; destructure its result
(R32) and put `m` in front with `hp.cons m` (R4).

**R32 · `have ⟨h₁, h₂⟩ := e`** changes the **context**: it adds both parts of `e : A ∧ B`.
Placeholders: `(A B : Prop) (e : A ∧ B)`.

| Before | After |
|---|---|
| `e : A ∧ B ⊢ P` | `h₁ : A, h₂ : B ⊢ P` |

---

## Part 10 · `rank_bound`

Statement: a leftist heap of rank `k` has at least `2 ^ k - 1` elements. Induction on `h` (no
generalizing). `leaf`: `simp [Heap.rank]`. `node rk x l r`: `w` says `rk = r.rank + 1` and
`r.rank ≤ l.rank`; then
$2^{r.rank+1} = 2^{r.rank} + 2^{r.rank} \le 2^{l.rank} + 2^{r.rank} \le (|l| + 1) + (|r| + 1) = |h| + 1$,
where $|t|$ is `(toList t).length`.

**R33 · `obtain ⟨rfl, h⟩ := w`** changes the **context**: when the first part of `w` is `k = e` with `k`
a local variable (here `rk`, bound by `induction … | node rk x l r`), `rfl` replaces `k` by `e`
everywhere. Placeholders: `(k n : Nat) (Q : Prop) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `w : k = n + 1 ∧ Q ⊢ P k` | `hq : Q ⊢ P (n + 1)` |

**R34 · `Nat.pow_le_pow_right`** changes the **context** (with `have`):
`Nat.pow_le_pow_right : n > 0 → i ≤ j → n ^ i ≤ n ^ j` (`n` implicit, so write `(n := 2)`, R31, and
`(by omega)` for `2 > 0`). Placeholders: `(i j : Nat) (hij : i ≤ j)`.

| Before | After `have hp := Nat.pow_le_pow_right (n := 2) (by omega) hij` |
|---|---|
| `hij : i ≤ j ⊢ P` | `hp : 2 ^ i ≤ 2 ^ j ⊢ P` |

**R35 · `show G'`** changes the **goal** to `G'`, which must be equal to it *by definition* (Lean checks
this by computing). Use it to unfold `(Heap.node (r.rank + 1) x l r).rank` and `toList (Heap.node …)`
by hand. Placeholders: `(x : Nat) (l r : Tree) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Tree.bin x l r).size` | `⊢ P (l.size + r.size + 1)` |

**R36 · `List.length_cons`** changes the **goal**: `List.length_cons : (a :: l).length = l.length + 1`.
Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).length` | `⊢ P (l.length + 1)` |

**R37 · `List.length_append`** changes the **goal**:
`List.length_append : (s ++ t).length = s.length + t.length`. Placeholders: `{α : Type} (s t : List α)`.

| Before | After |
|---|---|
| `⊢ P (s ++ t).length` | `⊢ P (s.length + t.length)` |

**R38 · `Nat.pow_succ`** changes the **goal**: `Nat.pow_succ : n ^ (m + 1) = n ^ m * n`. After it,
`omega` reads `2 ^ m * 2` as twice the atom `2 ^ m`, which is linear. Placeholders: `(n m : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n ^ (m + 1))` | `⊢ P (n ^ m * n)` |

**W1** (`unfold`, `split`, `show`, `omega` on `pick`):

```lean-goal
⊢ (pick x a b).size = a.size + b.size + 1
⊢ (if b.size ≤ a.size then Tree.bin x a b else Tree.bin x b a).size = a.size + b.size + 1
⊢ (Tree.bin x a b).size = a.size + b.size + 1
⊢ (Tree.bin x b a).size = a.size + b.size + 1
```

**W5** in `guide.lean` chains R11, R35, R36, R37, R10 on `t.elems.length = t.size`.

---

## Traps

- `merge` is defined by well-founded recursion, so `unfold merge`/`rfl` do not compute it and plain
  `induction h1` gives the wrong IH. Use `fun_induction merge h1 h2` (R7).
- Without `generalizing lo` (R8), `merge_heapOrd`'s IH is stuck at bound `lo`, but `case3` needs it at
  the new root `x` (W2).
- `IsHeap` asks for `HeapOrd 0`; the children of a node are only `HeapOrd x`. Weaken with
  `heapOrd_weaken` before you call `merge_spec` on them (Part 9).
- In `rank_bound`, do not `simp [Heap.rank]` in the `node` case: it turns `r.rank` into a `match` that
  `omega` cannot read. Use `show` (R35) and the length lemmas (R36–R38).
- In `merge_perm`'s `case4` the root `y` must move past all of `toList h1`; chaining `Perm` lemmas is
  painful, counting (W3) is one `omega`.
- `rfl` in `obtain`/`rcases` patterns replaces a *variable*; when both sides are variables, which one
  survives is Lean's choice (R16 keeps `y`). Read the new context before you name things.
- In `merge_leftist` the hypotheses are called `l1 l2`, the same as `merge`'s pattern variables for the left
  children. With `| case3 r1 x l1 r1' r2 y l2 r2' hxy ih` the children become `l1✝`, `l2✝` and the names
  `l1`, `l2` stay on the hypotheses; use `l1'`, `l2'` for the children (R7).
- An IH of a theorem with an implicit `{lo}` takes no bound argument: `ihl ol y hy`, not `ihl x ol y hy` (Part 4).
- Alternatives after `with` (`| case3 … =>`) list the variables in the order the infoview shows them,
  `✝` ones included; a wrong count shifts every name.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open a definition | `unfold mkNode` | R1 |
| case on an `if` in the goal | `split` | R2 |
| `Perm` goal that is equality after unfolding | `simp [toList]` | R3 |
| drop a common head / prefix of a `Perm` | `List.Perm.cons x hp`, `hp.cons x` / `List.Perm.append_left l hp` | R4, R22 |
| swap two appended lists | `List.perm_append_comm` | R5 |
| prove a defined conjunction | `exact ⟨h₁, h₂, h₃⟩` | R6 |
| induction following `merge` | `fun_induction merge h1 h2 generalizing lo with \| case1 … \| case4 … ih => …` | R7, R8 |
| parts of a defined conjunction | `o.1`, `o.2.1` / `obtain ⟨a, b, c⟩ := o` | R9, R12 |
| linear arithmetic | `omega` | R10 |
| structural induction with a moving bound | `induction h generalizing lo with …` | R11 |
| unfold in a hypothesis (and the goal, R13) | `simp only [toList] at h` | R13 |
| membership in `::` / `++` | `List.mem_cons`, `List.mem_append` | R14, R15 |
| split an `∨` and substitute | `rcases hy with rfl \| hy \| hy` | R16 |
| transitivity of `≤` | `Nat.le_trans h₁ h₂` | R17 |
| case on a constructor | `cases h with \| leaf => … \| node rk x l r => …` | R18 |
| `True`, `0 ≤ n`, `n ≤ n` | `trivial`, `Nat.zero_le n`, `Nat.le_refl n` | R19, R20, R27 |
| chain permutations | `refine (mkNode_perm _ _ _).trans ?_` | R21 |
| reassociate `++` | `List.append_assoc` (or `simp`) | R23 |
| permutation by counting | `rw [List.perm_iff_count] at ih` (and the goal), `intro a`, `simp only [List.count_append, List.count_cons] at this` (and the goal), `omega` | R24–R26 |
| use `findMin h = some m` | `cases hm` | R28, R29 |
| head is a member | `List.mem_cons_self` | R30 |
| set an implicit argument | `heapOrd_le (lo := m) …` | R31 |
| destructure a result | `have ⟨hh, hp⟩ := merge_spec …` | R32 |
| substitute a cached rank | `obtain ⟨rfl, hrl, ll, lr⟩ := w` | R33 |
| monotonicity of `2 ^ ·` | `Nat.pow_le_pow_right (n := 2) (by omega) hrl` | R34 |
| restate a goal by definition | `show 2 ^ (r.rank + 1) ≤ …` | R35 |
| lengths and powers for `omega` | `simp only [List.length_cons, List.length_append, Nat.pow_succ]` | R36–R38 |
| see the state | infoview | |
