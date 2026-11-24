# M014 · A hand-built state monad and tree relabelling: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `def` by pattern matching, `structure`,
`theorem`, `intro`, `exact`, `rfl`, `rw`, `simp`, `induction`, `⟨_, _⟩`. **New here:** core Lean only, no
imports. The `Monad` and `LawfulMonad` type classes, `do` notation over a monad you defined yourself,
`induction … generalizing`, `obtain`, `omega`, and `List.range'`.

**The idea.** `St σ α := σ → α × σ` is a *state monad*: a computation takes the current state `s : σ`
and returns a value and the next state. Its `pure a` returns `a` and leaves the state alone; `bind m f`
runs `m`, then feeds its value `(m s).1` and next state `(m s).2` to `f`. A `do` block is sugar for a
chain of `bind`s ending in `pure`. `LawfulMonad` is the class of monads whose `pure`/`bind` satisfy the
monad laws (below); here they hold by computation. `relabel` threads a counter through a tree, left to
right: the final counter is `s + t.size` and the labels are `s, s+1, …, s + t.size - 1`.

The three laws `LawfulMonad.mk'` asks for (`x >>= f` is `bind x f`, `f <$> x` is `Functor.map f x`):

| Law | Statement |
|---|---|
| `id_map` | `∀ {α} (x : m α), id <$> x = x` |
| `pure_bind` | `∀ {α β} (x : α) (f : α → m β), pure x >>= f = f x` |
| `bind_assoc` | `∀ {α β γ} (x : m α) (f : α → m β) (g : β → m γ), x >>= f >>= g = x >>= fun x => f x >>= g` |

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
  `∅` means no goal is left.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- The guide uses its own monads: `Box α` (a structure with one field `val : α`, `bind m f := f m.val`) and
  the reader monad `Rd α := Nat → α` (`bind m f := fun e => f (m e) e`), plus a tree `Bin` with
  constructors `tip` and `fork l r`. They stand in for `St σ` and `Tree`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `St σ α` | `σ → α × σ`: a state-passing computation (the file's `def St`); `m s` runs `m` from state `s` |
| `α × σ`, `(a, s)` | the type of pairs (`Prod α σ`) and a pair with first component `a`, second `s` |
| `Monad (St σ)`, `LawfulMonad (St σ)` | type classes: "`St σ` has `pure`/`bind`" and "they obey the three laws below" |
| `do let n ← m; k n` | `bind m (fun n => k n)`: run `m`, call its value `n`, continue with `k n` |
| `do m; k` (a line without `←`) | `bind m (fun _ => k)`: run `m` for its effect only (`St.set` returns `()`) |
| `return e` | `pure e` at the end of a `do` block |
| `St.get`, `St.set s'` | read the state (`fun s => (s, s)`); overwrite it with `s'` (`fun _ => ((), s')`) |
| `x >>= f` | `bind x f`: run `x`, pass its value to `f`; `x >>= f >>= g` is `(x >>= f) >>= g` |
| `pure x` | the computation that returns `x` and changes nothing |
| `f <$> x` | `Functor.map f x`; `Monad` defines it as `x >>= fun a => pure (f a)` |
| `id <$> x` | mapping the identity function `id a = a` |
| `autoParam T tac` | "a proof of `T`, filled in by running `tac` when omitted" (only after `apply`, see Traps) |
| `p.fst`, `p.snd` | `p.1`, `p.2`: the two components of a pair `p : α × β` |
| `(relabel t s).snd` | the counter after relabelling `t` from `s` (`relabel t : St Nat LTree` applied to `s`) |
| `(relabel t s).fst.labels` | `LTree.labels (relabel t s).1`: the labels of the relabelled tree |
| `l.node r`, `Tree.leaf.size` | `Tree.node l r`; `Tree.size Tree.leaf` (field notation) |
| `(relabel l s).fst.node t'` | `LTree.node (relabel l s).1 t'`: the same field notation on an `LTree` |
| `List.range' s n` | `[s, s+1, …, s+n-1]`: `n` consecutive numbers from `s` (`List.range' 3 4 = [3, 4, 5, 6]`) |
| `case refine_1` | the first `?_` of a `refine` |
| `case node.refine_2` | the second `?_` of a `refine`, inside the `node` case of an induction |
| `x✝`, `α✝` | names Lean made up (for a `_` or an unnamed binder); you cannot type them |

---

## Part 1 · `stLawful`

Statement: `LawfulMonad (St σ)`: the hand-built state monad satisfies the monad laws. This is an `instance`,
so its body is a *term* of type `LawfulMonad (St σ)` (you may also write `:= by …`).

**R1 · `refine LawfulMonad.mk' m ?_ ?_ ?_`** changes the **goal list**: the class becomes its three laws.
`LawfulMonad.mk' (m : Type → Type) [Monad m] id_map pure_bind bind_assoc : LawfulMonad m`; the remaining five
fields (`map_const`, `seqLeft_eq`, …) are `autoParam`s that `mk'` proves by itself. Placeholders: `m := Box`.

| Before | After |
|---|---|
| `⊢ LawfulMonad Box` | `⊢ ∀ {α : Type} (x : Box α), id <$> x = x`, `⊢ ∀ {α β : Type} (x : α) (f : α → Box β), pure x >>= f = f x`, `⊢ ∀ {α β γ : Type} (x : Box α) (f : α → Box β) (g : β → Box γ), x >>= f >>= g = x >>= fun x => f x >>= g` |

**R2 · `intro α β x f`** changes the **context**: it introduces the binders of the `∀`, *implicit ones
included*, in order. Placeholders: `{α β : Type} (x : α) (f : α → Box β)`.

| Before | After |
|---|---|
| `⊢ ∀ {α β : Type} (x : α) (f : α → Box β), pure x >>= f = f x` | `α β : Type, x : α, f : α → Box β ⊢ pure x >>= f = f x` |

**R3 · `rfl`** **closes** an equation whose sides reduce to the same term by unfolding definitions and
instance fields: here `pure x >>= f` ↦ `f (⟨x⟩ : Box α).val` ↦ `f x`. For `St σ`, both sides of each law are
functions `σ → _ × σ`; Lean also identifies `fun s => g s` with `g` (η) and `(p.1, p.2)` with `p`, so all three
laws reduce to the same term.

| Before | After |
|---|---|
| `x : α, f : α → Box β ⊢ pure x >>= f = f x` | ∅ |

**R4 · `exact fun _ _ => rfl`** **closes** a `∀`-law in one term: R2 and R3 together. `fun` does not mention
implicit binders (Lean inserts `{α β}`), so write one `_` per **explicit** binder: `id_map` has 1,
`pure_bind` 2, `bind_assoc` 3. A wrong count is `Type mismatch … rfl`.

| Before | After |
|---|---|
| `⊢ ∀ {α β : Type} (x : α) (f : α → Box β), pure x >>= f = f x` | ∅ |

**W1.** The whole instance as one term, no tactics:
`LawfulMonad.mk' Box (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)` (R1 with R4 three times).

---

## Part 2 · `relabel_spec`

Statement: for every tree `t` and start counter `s`, `(relabel t s).2 = s + t.size` (the counter advances
once per leaf) and `(relabel t s).1.labels = List.range' s t.size` (the leaves read left to right carry
`s, s+1, …`). Prove both halves together: the labels half of a node needs the counter half of its left
subtree.

### Induction with a moving counter

**R5 · `induction t generalizing s with | tip => ?_ | fork l r ihl ihr => ?_`** changes the **goal list and
the context**: one goal per constructor. `generalizing s` makes each induction hypothesis hold for every start
value, which you need because the right subtree starts at a different counter. Placeholders:
`(P : Bin → Nat → Prop) (t : Bin) (s : Nat)`.

| Before | After |
|---|---|
| `t : Bin, s : Nat ⊢ P t s` | `s : Nat ⊢ P Bin.tip s`, `l r : Bin, s : Nat ⊢ P (l.fork r) s` |

The `fork` goal also has `ihl : ∀ (s : Nat), P l s` and `ihr : ∀ (s : Nat), P r s`; `t` is gone from both goals.

**R6 · `obtain ⟨h1, h2⟩ := ih a`** changes the **context**: it instantiates `ih : ∀ x, A x ∧ B x` at `a`
and splits the `∧`. `a` can be any term, such as `(relabel l s).2`. Placeholders:
`{α : Type} (A B : α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ P` | `h1 : A a, h2 : B a ⊢ P` |

In the `node` case: `ihl s` speaks about the left subtree from `s`; `ihr (relabel l s).2` about the right
subtree from the counter the left one left behind.

### Unfolding the `do` block

**R7 · `simp only [g, bind, pure]`** changes the **goal**: `g` unfolds a definition at a constructor, `bind`
and `pure` unfold the hand-made instance, and `simp only` β-reduces `(fun e => …) e` and projections of pairs
(`(a, b).snd` ↦ `b`). Add `at *` to do it in all hypotheses too. For the leaf case add every name the leaf
computation goes through (`fresh`, `St.get`, `St.set`, `LTree.labels`, `Tree.size`) and use plain `simp`, which
also closes what is left with R11. Placeholders: `sumTips : Bin → Rd Nat`, `(l r : Bin) (e : Nat)`.

| Before | After |
|---|---|
| `⊢ P (sumTips (l.fork r) e)` | `⊢ P (sumTips l e + sumTips r e)` |
| `⊢ P ((fun s => (a, s)) b).snd` | `⊢ P b` |

In the exercise, after R6 and R7 the `node` goal reads

```
⊢ (relabel r (relabel l s).snd).snd = s + (l.node r).size ∧
    ((relabel l s).fst.node (relabel r (relabel l s).snd).fst).labels = List.range' s (l.node r).size
```

so `hr1`, `hl1`, `hl2`, `hr2` match it literally. Split it with `refine ⟨?_, ?_⟩`.

### The counter half

**R8 · `rw [g]`** (or `simp only [g]`) changes the **goal**: a pattern-matching `def` applied to a
constructor becomes that case's right side. Use it for `Tree.size` and `LTree.labels`. Placeholders:
`Bin.leaves : Bin → Nat`, `(l r : Bin)`.

| Before | After |
|---|---|
| `⊢ P (l.fork r).leaves` | `⊢ P (l.leaves + r.leaves)` |

**R9 · `omega`** **closes** a linear arithmetic goal over `Nat`/`Int`, treating other terms (`l.size`) as
unknowns. Placeholders: `(s a b : Nat)`.

| Before | After |
|---|---|
| `⊢ s + a + b = s + (a + b)` | ∅ |

Counter half: `rw [hr1, hl1]` turns `(relabel r (relabel l s).snd).snd` into `s + l.size + r.size`, R8 unfolds
`(l.node r).size`, R9 finishes.

### The labels half

**R10 · `rw [List.range'_append_1]`** changes the **goal**. The lemma is
`List.range'_append_1 : List.range' s m ++ List.range' (s + m) n = List.range' s (m + n)` (`s m n : Nat`
implicit). The second start must be literally `s + m`: rewrite with `hl1` first (W3). `simp` applies it by
itself.

| Before | After |
|---|---|
| `⊢ P (List.range' s m ++ List.range' (s + m) n)` | `⊢ P (List.range' s (m + n))` |

**R11 · `rw [List.range'_one]`** changes the **goal**: `List.range'_one : List.range' s 1 = [s]`. This is what the
leaf case needs; `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P (List.range' s 1)` | `⊢ P [s]` |

Labels half: R8 on `LTree.labels`, then `rw [hl2, hr2]`, then `rw [hl1]` (it changes the start
`(relabel l s).snd` of the second range to `s + l.size`), R8 on `Tree.size`, then R10.

**W2.** `count t s` threads a counter through a `Bin` without a monad; `count t s = s + t.leaves` by R5, then in the
`fork` case `rw [count, ihr, ihl, Bin.leaves]` and R9. `ihr` is rewritten first: it is about `count r _` at any
start, including `count l s`.

**W3.** With `hc : c = s + a`, `rw [hc]` turns the goal into the shape R10 needs:

| Before | After |
|---|---|
| `hc : c = s + a ⊢ List.range' s a ++ List.range' c b = List.range' s (a + b)` | `⊢ List.range' s a ++ List.range' (s + a) b = List.range' s (a + b)` |

---

## Traps

- `apply LawfulMonad.mk'` does not fill the five `autoParam` fields: it leaves eight goals, five of them
  `autoParam …`. Pass the three laws as arguments (`LawfulMonad.mk' (St σ) law₁ law₂ law₃`) or use `refine` (R1).
- `intro` names implicit binders too: `intro x f` on `∀ {α β} (x : α) (f : …), …` names `α` and `β`, not `x`
  and `f` (R2). `fun` is the other way round: it skips them (R4).
- Without `generalizing s`, `ihr` is stuck at the original `s` and cannot speak about `(relabel l s).2` (R5).
- `ihr s` is the wrong instance: the right subtree starts at `(relabel l s).2`, not at `s`.
- `rw [hl1]` before `rw [hr1]` fails in the counter half: `hr1`'s left side contains `(relabel l s).snd`, which
  `hl1` would already have rewritten away. Rewrite the outer term first.
- `.1`/`.2` are printed `.fst`/`.snd`; both spellings are the same term.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build `LawfulMonad m` from three laws | `LawfulMonad.mk' m law₁ law₂ law₃` | R1 |
| introduce `∀ {α β} x f` | `intro α β x f` | R2 |
| a law that holds by computation | `rfl` | R3 |
| the same as a term | `fun _ _ => rfl` (one `_` per explicit binder) | R4 |
| IH for every start counter | `induction t generalizing s with \| … => …` | R5 |
| use an IH at a point and split `∧` | `obtain ⟨h1, h2⟩ := ih a` | R6 |
| unfold a `do` block over your monad | `simp only [g, bind, pure] at *` | R7 |
| unfold a recursive `def` at a constructor | `rw [g]` / `simp only [g]` | R8 |
| linear `Nat` arithmetic | `omega` | R9 |
| `range' s m ++ range' (s + m) n` | `rw [List.range'_append_1]` or `simp` | R10 |
| `range' s 1` | `rw [List.range'_one]` or `simp` | R11 |
| split `A ∧ B` | `refine ⟨?_, ?_⟩` | TACTIC_STATES |
| see the state | infoview | |
