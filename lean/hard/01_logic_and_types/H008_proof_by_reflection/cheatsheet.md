# H008 · Proof by reflection: a commutative-monoid normaliser: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `def` by pattern matching, `theorem`,
`intro`, `exact`, `rfl`, `rw`, `simp`, `have`. **New here:** core Lean only, no imports. Classes that
carry laws, induction on lists, on your own syntax type and on a *proof* of `List.Perm`, `split` on an
`if`, and *proof by reflection*: turn the statement into a computable check on syntax and let `decide`
run it.

**The idea.** An equation between two products in a commutative monoid (`op` associative and
commutative, `unit` neutral) holds exactly when both sides contain the same atoms with the same
multiplicities. So: write each side as a syntax tree `e : Expr`, whose meaning under an assignment
`ρ : Nat → α` (atom `i` means `ρ i`) is `Expr.denote ρ e`. Compute a normal form `norm e` (the sorted
list of atom indices). Prove once, for all trees, `norm e1 = norm e2 → Expr.denote ρ e1 = Expr.denote ρ e2`
(`reflect`). Then each concrete equation costs one `decide`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
  `∅` means no goal is left.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- `f : α → α → α` with laws as hypotheses stands for your `op`: `hassoc : ∀ a b c, f (f a b) c = f a (f b c)`
  plays `op_assoc`, `hc : ∀ a b, f a b = f b a` plays `op_comm`. `{α : Type}` is any type.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `op a b`, `unit` | `CMon.op a b`, `CMon.unit`: the file says `open CMon`, so the prefix is dropped |
| `inst✝ : CMon α` | the instance from `[CMon α]`: "α is a commutative monoid". `✝` marks a name you cannot type |
| `op_comm a b`, `unit_op a` | the class laws are *terms* (proofs): `op_comm a b : op a b = op b a` |
| `Expr.denote ρ e` | the meaning of tree `e` when atom `i` means `ρ i` (you write `e.denote ρ`) |
| `e.atoms`, `Expr.atom i`, `a.op b` | `Expr.atoms e`; the atom constructor; `Expr.op a b` (field notation: `a.op b`) |
| `Expr.unit`, `Expr.op` vs `unit`, `op` | the *syntax* constructors (trees) vs the monoid's *values* `CMon.unit`, `CMon.op`; `Expr.denote` maps the first to the second |
| `.atom i`, `.op a b`, `.unit`, `.refl _` | leading dot: the constructor or lemma of the namespace the expected type names (`Expr.atom i`, `List.Perm.refl _`); you write trees in `demo` this way |
| `denoteList ρ l` | `op (ρ i₁) (op (ρ i₂) (… unit))` for `l = [i₁, i₂, …]` |
| `i :: is ++ l2` | `(i :: is) ++ l2`: `::` binds tighter than `++` |
| `l₁.Perm l₂` | `List.Perm l₁ l₂`: `l₂` is a reordering of `l₁` (written `l₁ ~ l₂` in prose) |
| `l₁✝`, `a✝`, `h✝` | names Lean made up because the pattern said `_`; usable only through `ih`, `‹_›`, or by renaming |
| `if i ≤ j then x else y` | the body of `insertSorted` after unfolding; `split` (R13) cases on it |
| `case cons.isFalse` | the `cons` goal of an induction, in its `else` branch |
| `[a, b, c, d].getD i unit` | the `i`-th element (from 0), or `unit` when `i ≥ 4` (R20) |

---

## Part 1 · `denoteList_append`

Statement: `denoteList ρ (l1 ++ l2) = op (denoteList ρ l1) (denoteList ρ l2)`: the meaning of an appended list
is the product of the meanings. Milestone 1, used in Part 2.

**R1 · `induction l with | nil => … | cons x xs ih => …`** changes the **goal list and the context**: one goal
per constructor of `List`. The `cons` goal gets `x`, `xs` and `ih`, the statement for `xs`. Placeholders:
`{α : Type} (P : List α → Prop) (l : List α)`.

| Before | After |
|---|---|
| `l : List α ⊢ P l` | `⊢ P []`, `x : α, xs : List α, ih : P xs ⊢ P (x :: xs)` |

**R2 · `simp only [g]`** changes the **goal**: a function defined by pattern matching, applied to a
constructor, is replaced by the right side of that equation. Here `dbl (x :: xs) = x :: x :: dbl xs`.
In the problem: `denoteList`, `Expr.atoms`, `Expr.denote`, `insertSorted`. Placeholders:
`(x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (dbl (x :: xs))` | `⊢ P (x :: x :: dbl xs)` |

**R3 · `List.cons_append`, `List.nil_append`** change the **goal**. The lemmas are
`x :: xs ++ ys = x :: (xs ++ ys)` and `[] ++ ys = ys`. `simp` uses them by itself; `simp only [g]` cannot unfold
`g (x :: xs ++ ys)` until the `::` is outermost. Placeholders: `{α : Type} (x : α) (xs ys : List α)`.

| Before | After |
|---|---|
| `⊢ P (x :: xs ++ ys)` | `⊢ P (x :: (xs ++ ys))` |
| `⊢ P ([] ++ ys)` | `⊢ P ys` |

**R4 · a class law as a rewrite rule** changes the **goal**. A `class` bundles operations and laws; the laws
are theorems you can name. The guide's class `Semi` has `comb_assoc : comb (comb x y) z = comb x (comb y z)`,
like your `op_assoc`; `unit_op : op unit a = a` works the same way. `simp only [comb_assoc]` rewrites every
left-nested product. Placeholders: `{α : Type} [Semi α] (a b c : α)` (`[Semi α]`: α has `comb` and its law).

| Before | After |
|---|---|
| `⊢ P (comb (comb a b) c)` | `⊢ P (comb a (comb b c))` |

**R5 · `simp only [ih]`** changes the **goal**: a hypothesis `ih : lhs = rhs` (the induction hypothesis, or an
earlier milestone) used left to right. Placeholders: `(g k : List Nat → Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `ih : g xs = k xs ⊢ P (g xs)` | `⊢ P (k xs)` |

---

## Part 2 · `denote_atoms`

Statement: `denoteList ρ e.atoms = Expr.denote ρ e`: flattening a tree to its list of atoms keeps its meaning.
Milestone 2, used in Part 5 step 1. The `atom` case reaches `op (ρ i) unit = ρ i`; the `op` case needs Part 1.

**R6 · `induction t with | leaf n => … | node l r ihl ihr => …`** changes the **goal list and the context**:
one goal per constructor of your own inductive type; a constructor with two subtrees gives two induction
hypotheses. `Expr` has three constructors, so `induction e with | atom i => … | unit => … | op a b iha ihb => …`.
Placeholders: `(P : Tree → Prop) (t : Tree)` with `Tree := leaf (n : Nat) | node (l r : Tree)`.

| Before | After |
|---|---|
| `t : Tree ⊢ P t` | `n : Nat ⊢ P (Tree.leaf n)`, `ihl : P l, ihr : P r ⊢ P (l.node r)` |

**R7 · `rw [hc _ e]`** changes the **goal**: commutativity with the second argument fixed rewrites only
products whose right factor is `e`. Plain `rw [hc]` rewrites the first product it meets. In the problem,
`op_comm _ (unit : α)`: the ascription `(unit : α)` is needed because `unit` alone does not say which
monoid. Inside a `simp` set the fixed argument also keeps `simp` from reordering unrelated products.
Placeholders: `{α : Type} (f : α → α → α) (e a : α) (hc : ∀ a b : α, f a b = f b a)`.

| Before | After |
|---|---|
| `⊢ P (f a e)` | `⊢ P (f e a)` |

The `unit` case needs no entry: both sides compute to `unit`, so `rfl` closes it.

---

## Part 3 · `denoteList_perm`

Statement: `h : l1.Perm l2 → denoteList ρ l1 = denoteList ρ l2`. Milestone 3, used in Part 5 step 2. Prove
left-commutativity `op a (op b c) = op b (op a c)` first (R8, R9), then induct on `h`.

**R8 · `rw [← hassoc]`** changes the **goal**: associativity right to left regroups to the left.
Placeholders: `(f : α → α → α) (a b c : α)`, `hassoc` as above.

| Before | After |
|---|---|
| `⊢ P (f a (f b c))` | `⊢ P (f (f a b) c)` |

**R9 · `rw [hc a b]`** changes the **goal**: with both arguments given, exactly the product `f a b` is swapped.

| Before | After |
|---|---|
| `⊢ P (f (f a b) c)` | `⊢ P (f (f b a) c)` |

**W1: swapping the last two factors** (R8, R9 on `f`), the kind of chain behind left-commutativity here:

```lean-goal
⊢ f (f a b) c = f (f a c) b
⊢ f a (f b c) = f (f a c) b
⊢ f a (f c b) = f (f a c) b
```

after `rw [hassoc]`, then `rw [hc b c]`; `rw [← hassoc]` closes it.

**R10 · `induction h with | nil | cons x _ ih | swap x y l | trans _ _ ih1 ih2`** changes the **goal list
and the context**. `List.Perm` is an inductive `Prop` with four constructors, so a proof `h` of it can be
inducted on: `nil : [].Perm []`; `cons x : l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)`;
`swap x y l : (y :: x :: l).Perm (x :: y :: l)`; `trans : l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃`.
Placeholders: `{α β : Type} (g : List α → β) {l₁ l₂ : List α}` (`g` plays `denoteList ρ`).

| Before | After |
|---|---|
| `h : l₁.Perm l₂ ⊢ g l₁ = g l₂` | `⊢ g [] = g []` |
| | `ih : g l₁✝ = g l₂✝ ⊢ g (x :: l₁✝) = g (x :: l₂✝)` |
| | `⊢ g (y :: x :: l) = g (x :: y :: l)` |
| | `ih1 : g l₁✝ = g l₂✝, ih2 : g l₂✝ = g l₃✝ ⊢ g l₁✝ = g l₃✝` |

**R11 · `Eq.trans`** **closes** `a = c` from `h1 : a = b` and `h2 : b = c`. Dot form: `h1.trans h2`.

| Before | After |
|---|---|
| `h1 : a = b, h2 : b = c ⊢ a = c` | ∅ |

---

## Part 4 · `sortList_perm`

Statement: `(sortList l).Perm l`: insertion sort only reorders. Milestone 4, used in Part 5 step 2. Prove the
helper `(insertSorted i l).Perm (i :: l)` first, by induction on `l` with `split` on the `if`.

**R12 · `List.Perm.refl`** **closes** `l.Perm l`. Write `exact .refl _`: the leading dot means
`List.Perm.refl`, read off the goal's type.

| Before | After |
|---|---|
| `⊢ l.Perm l` | ∅ |

**R13 · `split`** changes the **goal list and the context**: a goal containing `if c then x else y` becomes
two goals, one with `h✝ : c` and the `then` branch, one with `h✝ : ¬c` and the `else` branch. `next h => …`
names the hypothesis. Placeholders: `(i j : Nat) {α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if i ≤ j then a else b)` | `h✝ : i ≤ j ⊢ P a`, `h✝ : ¬i ≤ j ⊢ P b` |

**R14 · `List.Perm.cons`** **closes** `(x :: l₁).Perm (x :: l₂)` from `h : l₁.Perm l₂`: write `h.cons x`.

| Before | After |
|---|---|
| `h : l₁.Perm l₂ ⊢ (x :: l₁).Perm (x :: l₂)` | ∅ |

**R15 · `List.Perm.trans`** **closes** `l₁.Perm l₃` from `h1 : l₁.Perm l₂` and `h2 : l₂.Perm l₃`: `h1.trans h2`.

| Before | After |
|---|---|
| `h1 : l₁.Perm l₂, h2 : l₂.Perm l₃ ⊢ l₁.Perm l₃` | ∅ |

**R16 · `List.Perm.swap`** **closes** `(y :: x :: l).Perm (x :: y :: l)`: `.swap x y l`. Mind the order: the
*first* two arguments appear swapped on the *left*.

| Before | After |
|---|---|
| `⊢ (y :: x :: l).Perm (x :: y :: l)` | ∅ |

**W2** chains R16, R14, R14, R15: `(List.Perm.swap x y l).trans ((h.cons y).cons x)` proves
`(y :: x :: l).Perm (x :: y :: l')` from `h : l.Perm l'`. The `else` branch of the helper,
`(j :: insertSorted i js).Perm (i :: j :: js)`, uses the same entries in the other order: first `ih` under `j`
(R14), then the swap (R16).

---

## Part 5 · `reflect`

Statement: `norm e1 = norm e2 → Expr.denote ρ e1 = Expr.denote ρ e2`. Chain:
`Expr.denote ρ e = denoteList ρ e.atoms` (Part 2) `= denoteList ρ (sortList e.atoms)` (Parts 3, 4), and
`sortList e.atoms` is `norm e` by definition.

**R17 · `rw [← hg]` with a `∀` lemma** changes the **goal**. Right to left, `rw` searches for the pattern
`G ?x`; the first match fixes `?x`, and only that instance is rewritten. A second side needs a second
`rw [← hg]` (or explicit arguments: `rw [← hg b]`). Placeholders:
`{α β γ : Type} (F : β → γ) (k : α → β) (G : α → γ) (hg : ∀ x, F (k x) = G x) (a b : α)`.
In the problem, `hg` is `denote_atoms ρ`, then `denoteList_perm ρ (sortList_perm eₖ.atoms)`.

| Before | After `rw [← hg]` | After `rw [← hg]` again |
|---|---|---|
| `⊢ G a = G b` | `⊢ F (k a) = G b` | `⊢ F (k a) = F (k b)` |

**R18 · `congrArg f`** **closes** `f a = f b` from `h : a = b`: apply `f` to both sides. `exact` compares up to
unfolding definitions (R21), so `h : norm e1 = norm e2` proves a goal about `sortList eₖ.atoms` (W3).

| Before | After |
|---|---|
| `h : a = b ⊢ f a = f b` | ∅ |

---

## Part 6 · `demo`

Statement: `op (op a b) (op c (op d unit)) = op d (op (op c a) b)` for any `a b c d : α`. Prove it with
`reflect`, not by rewriting: two trees, one `(by decide)`, one `ρ`.

**R19 · `decide`** **closes** a statement with no free variables whose truth is computable, by evaluating it:
`(Tree.node (.leaf 2) (.node (.leaf 0) (.leaf 1))).leaves = [2, 0, 1]`. Your own structurally recursive
functions (`Expr.atoms`, `insertSorted`, `sortList`, `norm`) evaluate too. It **fails** on anything mentioning
`a b : α`: that is why the trees hold atom *indices* and `ρ` supplies the values.

**R20 · `List.getD l i d`** is the `i`-th element of `l` (from 0), or the default `d` when `i` is out of
range. On a literal list it computes, so `show` accepts the value. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After `show P b` |
|---|---|
| `⊢ P ([a, b, c].getD 1 d)` | `⊢ P b` |

**R21 · `show G'`, and `exact`, work up to definitional unfolding**: changes the **goal** to anything equal to it
by computation. A recursive function on a concrete tree unfolds to its value; this is what lets
`exact reflect … ρ` match your goal. Placeholders: `(ρ : Nat → Nat)`, with
`Tree.sum ρ (leaf n) = ρ n`, `Tree.sum ρ (node l r) = Tree.sum ρ l + Tree.sum ρ r`.

| Before | After `show P (ρ 0 + ρ 1)` |
|---|---|
| `⊢ P (Tree.sum ρ ((Tree.leaf 0).node (Tree.leaf 1)))` | `⊢ P (ρ 0 + ρ 1)` |

**W4: reflection in miniature** (guide, on `Nat` and `Tree`). With a soundness fact
`sound : ∀ t1 t2, t1.leaves.reverse = t2.leaves → ∀ ρ, t1.sum ρ = t2.sum ρ`,

```lean-goal
⊢ a + b = b + a
```

is closed by `exact sound (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)) (by decide) (fun i => [a, b].getD i 0)`:
`decide` checks `[1, 0] = [1, 0]`, and `Tree.sum ρ` of the two trees unfolds to `a + b` and `b + a`.

---

## Traps

- No imports, no `grind`, no `ac_rfl`/`ac_nf`, no search tactics (`exact?`, `apply?`, `try?`): they are
  banned. The class `CMon` is the problem's own; core Lean has no commutative-monoid class.
- `demo` is the payoff: prove it with `reflect` and `by decide`. A chain of `op_assoc`/`op_comm` rewrites
  proves it too, but misses the point.
- `simp [op_comm]` with the bare law can reorder products in ways you did not want. Fix an argument:
  `op_comm _ (unit : α)` (R7). Without `(unit : α)` Lean cannot tell which monoid's `unit` you mean.
- `simp only [denoteList]` does nothing on `denoteList ρ (i :: is ++ l2)`: the outer function is `++`.
  Rewrite with `List.cons_append` first (R3), or use full `simp`, which does it by itself.
- Prove left-commutativity *before* `induction h`: a `have` after it lives in one case only.
- `exact .refl _` on `(insertSorted i []).Perm [i]` or `(sortList []).Perm []` works because `exact` unfolds
  the definitions (R21); `rw`/`simp only` are not needed there.
- In the `Perm` induction, `_` patterns give unnamed lists `l₁✝ l₂✝`; that is fine, `ih` mentions them.
- `rw [← denote_atoms]` rewrites only the first side it matches (R17). Rewrite twice.
- `List.Perm.swap x y l` proves `(y :: x :: l).Perm (x :: y :: l)`, not `(x :: y :: l).Perm (y :: x :: l)`.
  Use `.symm` (`h.symm : l₂.Perm l₁` from `h : l₁.Perm l₂`) or reorder if the directions do not line up.
- `decide` needs a closed statement. In `demo`, the trees use atom indices `0, 1, 2, 3`, never `a b c d`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on a list / your tree / a `Perm` proof | `induction l with \| nil => _ \| cons x xs ih => _` / `induction e with …` / `induction h with …` | R1, R6, R10 |
| unfold a recursive def on a constructor | `simp only [g]` (or `simp [g, …]`) | R2 |
| `x :: xs ++ ys`, `[] ++ ys` | `List.cons_append`, `List.nil_append` (in `simp` already) | R3 |
| use a class law | `simp [op_assoc, unit_op]`, `rw [op_comm a b]` | R4, R9 |
| use `ih` or a milestone | `simp [ih]`, `rw [lemma]` | R5 |
| commute only with `unit` | `op_comm _ (unit : α)` | R7 |
| regroup left | `rw [← op_assoc]` | R8 |
| chain two equations | `h1.trans h2` | R11 |
| `l.Perm l` | `exact .refl _` | R12 |
| case on an `if` | `split` | R13 |
| `Perm` under a head / swap / chain | `h.cons x`, `.swap x y l`, `h1.trans h2` | R14, R16, R15 |
| rewrite a side right to left | `rw [← lemma]` once per side | R17 |
| apply a function to an equation | `congrArg f h` | R18 |
| run a computable check | `(by decide)` | R19 |
| finite assignment of atoms | `fun i => [a, b, c, d].getD i unit` | R20 |
| goal equal by computation | `show G'`, or `exact` directly | R21 |
| see the state | infoview | |
