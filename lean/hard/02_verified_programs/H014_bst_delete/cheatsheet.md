# H014 · BST delete: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching, `inductive`, `theorem`,
`induction`/`cases` on `Nat` and `List`, `simp`, `rw`, `exact`, `constructor`, `omega`.
**New here:** proofs about a user-defined binary tree: induction with two induction hypotheses
(IHs), generalizing the induction, inverting an inductive predicate (`BST`), `Option` results and
`match` inside a hypothesis or goal (`split`), destructuring with `obtain`/`rcases` and `rfl`
patterns, and the `grind` automation. No Mathlib: everything is core Lean.
(M019, BST insert, uses the same `Tree`, `mem`, `All`, `BST`; it is not assumed.)

The guide works on its own tree `Bin α` (constructors `tip` and `fork l a r`, any value type `α`),
its own function `size` and its own inductive predicate `Good Q t` ("`Q` holds at every value"),
never on the exercise's `Tree`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal the step does not touch; `k` is a hypothesis that finishes the
  example once the step has produced the right facts.
- `{α : Type}` is any type. A bracket such as `[Decidable c]` is a requirement (a *type class*):
  `Decidable c` means `c` can be computed to `true`/`false`, which `if c then … else …` needs; every
  `x < k` on `Nat` qualifies.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- "No goals" means the step closed the goal.

## Reading the goals

| You see | It means |
|---|---|
| `Tree`, `.leaf`, `.node l k r` | the exercise's tree: empty, or left subtree `l`, key `k : Nat`, right subtree `r` |
| `l.node k r` | how Lean prints `Tree.node l k r` (dot notation: the first explicit argument moves in front) |
| `Tree.leaf`, `Tree.leaf.node k r` | how Lean prints `.leaf` and `.node .leaf k r` (the full name, since nothing fixes the type) |
| `mem y t` | `y` occurs as a key of `t` (a `Prop`, defined by recursion: `mem y (l.node k r)` unfolds to `mem y l ∨ y = k ∨ mem y r`) |
| `All p t` | `p` holds at every key of `t`; unfolds to `All p l ∧ p k ∧ All p r` |
| `(· < k)`, `fun x => x < k` | the predicate "is below `k`"; `(k < ·)` is "is above `k`". Lean prints the `fun` form |
| `BST t` | `t` is a binary search tree: an inductive predicate whose `node` constructor needs four premises: `All (· < k) l`, `All (k < ·) r`, `BST l`, `BST r` |
| `popMin t : Option (Nat × Tree)` | `none` on a leaf, else `some (m, t')`: the minimum `m` and the tree without it. `Nat × Tree` is the type of pairs `(m, t')` |
| `match popMin l with` … `\| none => … \| some (m, l') => …` | the `match` inside `popMin`'s or `delete`'s definition, shown after unfolding (printed over several lines) |
| `if x < k then … else …` | the `if` inside `delete`, shown after unfolding |
| `y ≠ x` | `¬(y = x)` |
| `ihl : BST l → (…)` | an IH whose premise (here `BST l`) came from a hypothesis `h : BST t` that Lean generalized automatically; apply it to `bl : BST l` first |
| `x✝`, `heq✝`, `h✝`, `h✝¹`, `m✝`, `l'✝`, `a✝¹`, `this✝`, `left✝`, `right✝` | inaccessible names: hypotheses created by a tactic (`left✝`, `right✝` come from a `_` in `obtain ⟨_, hmem, _⟩`), not nameable in your proof until `rename_i` (R11). A superscript (`h✝¹`) marks an older one with the same name |
| `heq✝ : popMin l = none` | the fact recorded by `split` (R6, R23): which `match` arm this goal is in |
| `inst✝ : Decidable c` | an instance hypothesis, there for the `if` |
| `case leaf`, `case node` | the goals made by `induction`/`cases` (R1, R5) |
| `case h_1`, `case h_2` | the goals made by `split` on a `match`, one per arm in order |
| `case isTrue`, `case isFalse` | the goals made by `split` on an `if` |
| `case inl`, `case inr.inl`, `case inr.inr` | the goals made by `rcases` on `A ∨ B ∨ C` |

---

## Part 1 · `all_iff` (milestone)

Statement: `All p t ↔ ∀ y, mem y t → p y`. Restates `All` as "every member satisfies `p`", so the
rest of the exercise only reasons about `mem`.

**R1 · `induction t with | tip => ?_ | fork l a r ihl ihr => ?_`** changes the **goal list and the
context**: one goal per constructor. The `fork` goal gets the subtrees and one IH per recursive
argument: `ihl` for `l`, `ihr` for `r`. Writing `=> ?_` leaves that case open as a goal, to be done
with `·` afterwards; you can also write the tactics directly after `=>`. Placeholders:
`{α : Type} (P : Bin α → Prop) (t : Bin α)`.

| Before | After |
|---|---|
| `⊢ P t` | `⊢ P Bin.tip`, `l : Bin α, a : α, r : Bin α, ihl : P l, ihr : P r ⊢ P (l.fork a r)` |

**R2 · `simp only [f]`** changes the **goal** (or, with `at h`, the **context**): `f` applied to a
constructor is replaced by the matching equation of `f`'s definition. `simp only [f]` uses `f`'s
equations and nothing else, so you see exactly one unfolding. Use it for `All`, `mem`, `popMin`,
`delete`. Placeholders: `{α : Type} (l r : Bin α) (a : α) (P : Nat → Prop)`.

| | Before | After |
|---|---|---|
| goal | `⊢ P (size (l.fork a r))` | `⊢ P (size l + 1 + size r)` |
| `at h` | `h : P (size (l.fork a r)) ⊢ P (size l + 1 + size r)` | `h : P (size l + 1 + size r) ⊢ P (size l + 1 + size r)` |

**R3 · `simp only [e q]`**, with `e : Q → (A ↔ B)` and `q : Q`, changes the **goal**: every `A`
becomes `B`. `simp` rewrites with an `↔` as with an `=`. An IH with a premise must get that premise
first: `simp only [mem, ihl bl]`, not `simp only [mem, ihl]`. An IH without premise (as in
`all_iff`) is passed as is. Placeholders: `(Q A B : Prop) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P A` | `⊢ P B` |

**R4 · `grind`** **closes** a goal that follows from the hypotheses by propositional logic (`∧ ∨ ¬ → ↔`),
equalities and linear arithmetic over `Nat`, treating other predicates (`A y`, `mem y l`) as opaque
atoms. It also instantiates `∀` hypotheses when a matching term occurs. `omega` does only the
arithmetic part and fails as soon as an atom matters. Placeholders: `(A : Nat → Prop) (k x y : Nat)`.

| Before | After |
|---|---|
| `hA : A y → k < y, hx : x < k ⊢ A y → y ≠ x` | no goals |

**W4: what `grind` does with the quantifiers.** Distributing `∀` over `∨` is pure logic, which
`grind` closes in one step:

```lean-goal
⊢ ((∀ (y : Nat), L y → p y) ∧ ∀ (y : Nat), R y → p y) ↔ ∀ (y : Nat), L y ∨ R y → p y
```

---

## Part 2 · `popMin_none` (milestone)

Statement: `popMin t = none → t = .leaf`. Used in the `none` arm of `popMin_spec` and `mem_delete`.

**R5 · `cases t with | tip => ?_ | fork l a r => ?_`** changes the **goal list and the context**: as
R1, one goal per constructor, but with no IHs. Use it when the proof does not recurse.
Placeholders: `{α : Type} (P : Bin α → Prop) (t : Bin α)`.

| Before | After |
|---|---|
| `⊢ P t` | `⊢ P Bin.tip`, `l : Bin α, a : α, r : Bin α ⊢ P (l.fork a r)` |

**R6 · `split at h`** changes the **goal list and the context**. With
`h : (match g z with | none => b | some a => f a) = c`, it makes one goal per `match` arm. Each gets
`heq✝ : g z = <that arm's pattern>` and `h` with that arm's value; the pattern variables (`a✝`)
enter the context, and `x✝` (the matched value) is left over, unused. Placeholders:
`{γ α β : Type} (g : γ → Option α) (z : γ) (b c : β) (f : α → β) (G : Prop)`. In the exercise the
`match` comes from unfolding `popMin` (R2 `at h`), and `g z` is `popMin l`. In the guide,
`‹_›` (E012) passes the hypothesis whose type the slot expects, here the inaccessible `heq✝`.

| Before | After |
|---|---|
| `⊢ G` (with the `match` in `h`) | `heq✝ : g z = none, h : b = c ⊢ G`, `heq✝ : g z = some a✝, h : f a✝ = c ⊢ G` |

**R7 · `simp at h`** with `h : none = some x` (or `some x = none`) **closes** the goal: `simp`
rewrites `h` to `False`, and a `False` hypothesis proves anything. Placeholders:
`{α : Type} (x : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : none = some x ⊢ G` | no goals |

**W2: a `match` in a hypothesis, end to end (R6, R11, R7/R13-style `simp at h`).** With
`h : (match g z with | none => 0 | some m => m + 1) = n + 1`, `split at h` gives

```lean-goal
⊢ g z = some n
```

twice: once with `heq✝ : g z = none, h : 0 = n + 1` (`simp at h` closes it: `0 = n + 1` is false),
once with `heq✝ : g z = some m✝, h : m✝ + 1 = n + 1` (`rename_i m hm`, `simp at h` gives `h : m = n`,
then `rw [hm, h]`).

---

## Part 3 · `popMin_spec` (milestone)

Statement: if `BST t` and `popMin t = some (m, t')`, then `BST t'`, the members of `t` are `m` and
the members of `t'`, and every key of `t'` is above `m`. Used in the last arm of `mem_delete` and
`delete_bst`.

**R8 · `induction t generalizing b with …`** changes the **goal list and the context**: as R1, but `b`
(and every hypothesis mentioning it) is taken out of the context first, so each IH starts with
`∀ b`. Without `generalizing`, the IH speaks about the same `b` as the goal and is useless when the
recursive call returns a different value (in `popMin_spec`: the minimum of `l` is not `m`).
Hypotheses that mention `t` itself (`hb` here, `h : BST t` in the exercise) are generalized
automatically. Placeholders: `{α β : Type} (f : Bin α → Option β) (Q : Bin α → β → Prop) (t : Bin α) (b : β)`.

| Before | After |
|---|---|
| `hb : f t = some b ⊢ Q t b` | `hb : f Bin.tip = some b ⊢ Q Bin.tip b`, `hb : f (l.fork a r) = some b ⊢ Q (l.fork a r) b` |

In the `fork` goal the IHs are `ihl : ∀ (b : β), f l = some b → Q l b` and the same for `r`.

**R9 · `cases h with | fork hq gl gr => ?_`** changes the **context**: a proof `h` of an inductive
predicate is replaced by the premises of the only constructor that can have built it
(`Good.tip` cannot build `Good Q (l.fork a r)`, so that case disappears). In the exercise:
`cases h with | node hl hr bl br => ?_` gives `hl : All (fun x => x < k) l`, `hr : All (fun x => k < x) r`,
`bl : BST l`, `br : BST r`. Placeholders: `{α : Type} (Q : α → Prop) (l r : Bin α) (a : α)`.

| Before | After |
|---|---|
| `h : Good Q (l.fork a r) ⊢ G` | `hq : Q a, gl : Good Q l, gr : Good Q r ⊢ G` |

**R10 · `rw [e] at h₁ h₂`** / **`rw [e] at h ⊢`**, with `e : ∀ x, A x ↔ B x`, changes the
**context** (and, with `⊢`, the **goal**): `A …` becomes `B …` in each listed place. `e`'s arguments
are found separately in each place, so `rw [all_iff] at hl hr` works although `hl` and `hr` use
different predicates. Placeholders: `{α : Type} (A B : α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `h1 : A a, h2 : A b ⊢ G` | `h1 : B a, h2 : B b ⊢ G` |
| `h : A a ⊢ A b` | `h : B a ⊢ B b` |

**R11 · `rename_i x y`** changes the **context**: the last inaccessible names, in order, get the
names you give, skipping named hypotheses. After R6 in `popMin_spec` (arm `some`) the inaccessible
names are `x✝ m✝ l'✝ heq✝` (then the named `hp`), so `rename_i m' l' hs` names the last three and leaves `x✝`. Placeholders: `(A B G : Prop)`; here the inaccessible names
come from `intro _ _`.

| Before | After |
|---|---|
| `a✝¹ : A, a✝ : B ⊢ G` | `ha : A, hb : B ⊢ G` |

**R12 · `obtain rfl := h`**, with `h : t = c` and `t` a local variable, changes the **context**: `t`
is replaced by `c` everywhere and disappears. `h` can be a lemma application:
`obtain rfl := popMin_none l hn`. Placeholders: `{α : Type} (t : Bin α) (P : Bin α → Prop)`.

| Before | After |
|---|---|
| `h : t = Bin.tip ⊢ P t` | `⊢ P Bin.tip` |

**R13 · `simp at h`** with `h : some (a, b) = some (c, d)` changes the **context**: `h` becomes
`a = c ∧ b = d`, since `some` and pairing are injective. Placeholders: `{α β : Type} (a c : α) (b d : β)`.

| Before | After |
|---|---|
| `h : some (a, b) = some (c, d)`, `⊢ G` | `h : a = c ∧ b = d ⊢ G` |

**R14 · `obtain ⟨rfl, rfl⟩ := h`**, with `h : a = c ∧ e = t`, changes the **context**: both
equations are substituted. A variable on the right side is replaced by the left side (`c := a`,
then `t := e`), so `c` and `t` disappear. In `popMin_spec` this replaces `m t'` by `k r` (arm `none`)
or by `m'` and `l'.node k r` (arm `some`). Placeholders: `{α : Type} (a c : α) (s t : Bin α) (P : α → Bin α → Prop)`.

| Before | After |
|---|---|
| `h : a = c ∧ s.fork a s = t ⊢ P c t` | `⊢ P a (s.fork a s)` |

**R15 · `.1`, `.2`, `.inl`, `.inr`** (term notation) change the **goal** when used with `refine`. For
`e : A ↔ B`: `e.1 : A → B` (`Iff.mp`), `e.2 : B → A` (`Iff.mpr`). For `e : A ∧ B`: `e.1 : A`,
`e.2 : B`. `.inl ha : A ∨ B` and `.inr hb : A ∨ B` (`Or.inl`, `Or.inr`; the leading dot lets Lean
read the type from the goal). So `(all_iff _ _).2 h` turns `h : ∀ y, mem y t → p y` into `All p t`, and
`(hmem m').2 (.inl rfl)` proves `mem m' l` from `hmem : ∀ y, mem y l ↔ y = m' ∨ mem y l'`.
Placeholders: `{α : Type} (A B C : α → Prop) (x : α)`.

| Before | After `refine (e x).2 ?_` | After `exact .inr hc` |
|---|---|---|
| `⊢ A x` | `⊢ B x ∨ C x` | no goals |

**R16 · `obtain ⟨h₁, h₂, h₃⟩ := e`**, with `e : A ∧ B ∧ C`, changes the **context**: it gains the
three facts. `e` may be a lemma or IH application (`obtain ⟨b', hmem, hlt⟩ := ihl bl _ _ hs`); `_`
drops a piece you do not need. Placeholders: `(Q A B C G : Prop) (e : Q → A ∧ B ∧ C) (q : Q)`.

| Before | After |
|---|---|
| `⊢ G` | `ha : A, hb : B, hc : C ⊢ G` |

**R17 · `refine .fork ?_ gl gr`** changes the **goal**: to prove an inductive predicate, apply one
constructor; arguments given now are checked, each `?_` becomes a new goal. In the exercise:
`refine .node ?_ hr (ihl bl) br` (its four premises in the order of `BST.node`), or `exact .node …`
with all four given. Placeholders: `{α : Type} (Q : α → Prop) (l r : Bin α) (a : α)`.

| Before | After |
|---|---|
| `⊢ Good Q (l.fork a r)` | `⊢ Q a` |

**R18 · `intro y hy`** changes the **goal and the context**: `∀ y, A y → B y` loses its binder and
premise, which enter the context. In term mode the same is `fun y hy => …`. Placeholders:
`{α : Type} (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), A y → B y` | `y : α, hy : A y ⊢ B y` |

**R19 · `rcases h with h | rfl | h`**, with `h : A y ∨ y = c ∨ B y`, changes the **goal list**: one
goal per disjunct. The `rfl` pattern substitutes `y := c` in the middle one (so `kc : Q c` reads
`kc : Q y`). Placeholders: `{α : Type} (A B Q : α → Prop) (c y : α)`.

| Before | After |
|---|---|
| `h : A y ∨ y = c ∨ B y ⊢ Q y` | `h : A y ⊢ Q y`, `kc : Q y ⊢ Q y`, `h : B y ⊢ Q y` |

**R20 · `Nat.lt_trans`** **closes** `n < k`. The lemma is `Nat.lt_trans : n < m → m < k → n < k`.
Placeholders: `(n m k : Nat)`.

| Before | After `exact Nat.lt_trans h₁ h₂` |
|---|---|
| `h₁ : n < m, h₂ : m < k ⊢ n < k` | no goals |

**W1: induction, inversion, constructor (R1, R9, R17).** `Good Q t → Good Q' t` when `Q a → Q' a`
for all `a`: `induction t`; `tip`: `exact .tip`; `fork`: `cases h` into `hq gl gr`, then
`exact .fork (hQ a hq) (ihl gl) (ihr gr)`, which uses both IHs, each applied to its premise.

---

## Part 4 · `mem_delete`

Statement: `BST t → (mem y (delete x t) ↔ mem y t ∧ y ≠ x)`. After `simp only [delete]` the goal
contains `delete`'s nested `if … else if … else match popMin r with …`; R22 and R23 split it.

**R21 · `have := e`** changes the **context**: it gains `this : T` for `e : T` (an older `this`
becomes `this✝`). `have := hl y` instantiates `hl : ∀ y, mem y l → y < k` at the goal's `y`.
`grind` usually finds such instances itself; stating them shows what it uses and helps when it
fails. Placeholders: `(A B : Nat → Prop) (hA : ∀ y, A y → B y) (y : Nat)`.

| Before | After |
|---|---|
| `⊢ B 0` | `this : A y → B y ⊢ B 0` |

**R22 · `split`** on `if c then x else y` in the goal changes the **goal list**: one goal with
`h✝ : c`, one with `h✝ : ¬c`. A nested `if` sits in the `else` goal and needs a second `split`.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (if c then x else y)` | `h✝ : c ⊢ P x`, `h✝ : ¬c ⊢ P y` |

**R23 · `split`** on a `match` in the goal changes the **goal list**: one goal per arm, each with
`heq✝ : g z = <pattern>` (as R6, but for the goal). Name the new facts with R11:
`rename_i m r' hs` gives `hs : popMin r = some (m, r')`. Placeholders:
`{γ α β : Type} (g : γ → Option α) (z : γ) (b : β) (f : α → β) (P : β → Prop)`. Before:

```lean-goal
⊢ P (match g z with | none => b | some a => f a)
```

| After |
|---|
| `heq✝ : g z = none ⊢ P b`, `heq✝ : g z = some a✝ ⊢ P (f a✝)` |

**R24 · `simp only [f, e] at *`** changes the **goal and the context**: every hypothesis and the goal
are rewritten at once. In the last arm of `mem_delete`, `simp only [mem, hmem] at *` unfolds `mem`
and replaces `mem y r` by `y = m ∨ mem y r'` everywhere, so `grind` sees one vocabulary.
Placeholders: `{α : Type} (l r : Bin α) (a : α) (n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : size (l.fork a r) = n ⊢ P n` | `h : size l + 1 + size r = n ⊢ P n` |

**W3: `∀` facts as `grind` input (R21, R4).** With `hL : ∀ z, L z → z < k`, `hR : ∀ z, R z → k < z`,
`hx : x < k`, the instances `have := hL y; have := hR y` give

```lean-goal
⊢ (L y ∨ y = k ∨ R y) ∧ y ≠ x ↔ L y ∧ y ≠ x ∨ y = k ∨ R y
```

which `grind` closes: `R y` rules out `y = x` because `x < k < y`.

---

## Part 5 · `delete_bst`

Statement: `BST t → BST (delete x t)`. No new entries: induction (R1), inversion (R9), unfolding (R2),
the two `if`s and the `match` (R22, R23), then the constructor `BST.node` (R17). Each `All` premise is
proved through `all_iff` (R10 or R15, then R18). In the `x < k` branch the hole is
`All (· < k) (delete x l)`: a member of `delete x l` is a member of `l` by `(mem_delete x y l bl).1`,
then `.1` of the `∧` (R15). In the last arm the new root is `m`, the minimum of `r`: first
`k < m` (from `hr` and `popMin_spec`'s membership part), then every key of `l` is `< k < m` (R20).

---

## Traps

- `omega` closes `y ≠ x` from `y < k` and `x = k`, but cannot see inside `mem y l`; `grind` mixes
  both (R4).
- `induction t` without `generalizing m t'` in `popMin_spec` gives an IH about the same `m`, but the
  minimum of `l` is a different number: the IH is unusable (R8).
- Invert `h : BST t` only after `induction t` (or `cases t`): once `t` is `l.node k r`, `cases h`
  has the single `node` case (R9); on a bare variable `t` it also produces a `leaf` case.
- An IH with a premise is a function: `ihl bl`, not `ihl`, inside `simp only [...]` (R3).
- `split` names its facts `heq✝`, `h✝`: inaccessible until `rename_i` (R11), which names the LAST
  ones in order, so give exactly as many names as you need from the end.
- `split` on a `match` over a plain variable substitutes the variable and leaves no `heq✝`; over
  `popMin l` (not a variable) it records `heq✝ : popMin l = …`.
- `obtain ⟨rfl, rfl⟩ := hp` needs a variable on one side of each equation; it replaces the right-hand
  variable (`m`, `t'`) by the left side (R14).
- `(· < k)` is printed `fun x => x < k`; after `rw [all_iff] at hl` it becomes
  `hl : ∀ (y : Nat), mem y l → y < k`.
- `All` premises of `BST.node` must be given as `All …`, not in `∀` form: wrap with
  `(all_iff _ _).2` (R15).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a tree | `induction t with \| leaf => … \| node l k r ihl ihr => …` | R1 |
| induction with a varying output | `induction t generalizing m t' with …` | R8 |
| case on a tree, no IH | `cases t with \| leaf => … \| node l k r => …` | R5 |
| unfold `f` at a constructor | `simp only [f]` / `simp only [f] at h` / `at *` | R2, R24 |
| rewrite with an IH that has a premise | `simp only [mem, ihl bl]` | R3 |
| `All` ↔ `∀ y, mem y t → p y` | `rw [all_iff] at hl hr` (R10 for the goal too) / `(all_iff _ _).2 h` | R10, R15 |
| logic + arithmetic over `mem`-atoms | `grind` | R4 |
| `match` in a hypothesis | `split at h` | R6 |
| `if` / `match` in the goal | `split` | R22, R23 |
| name `heq✝`, `h✝`, `m✝` | `rename_i a b hs` | R11 |
| `none = some _` in `h` | `simp at h` | R7 |
| `some (a, b) = some (c, d)` in `h` | `simp at h` → `a = c ∧ b = d` | R13 |
| substitute equations | `obtain rfl := h` / `obtain ⟨rfl, rfl⟩ := h` | R12, R14 |
| take apart `A ∧ B ∧ C` | `obtain ⟨ha, hb, hc⟩ := e` | R16 |
| invert `h : BST (.node l k r)` | `cases h with \| node hl hr bl br => …` | R9 |
| build `BST (.node l k r)` | `refine .node ?_ ?_ ?_ ?_` / `exact .node …` | R17 |
| use an `↔` / `∧` / build an `∨` | `e.1`, `e.2`, `.inl h`, `.inr h` | R15 |
| three-way `∨` with an equation | `rcases h with h \| rfl \| h` | R19 |
| `a < c` from `a < b` and `b < c` | `Nat.lt_trans h₁ h₂` | R20 |
| instantiate a `∀` fact | `have := hl y` | R21 |
| introduce `∀ y, A y → B y` | `intro y hy` | R18 |
| see the state | infoview | |
