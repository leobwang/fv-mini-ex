# H004 · Well-founded relations: Acc, lex, descending chains: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `have`, `refine`, `cases`/`induction`
on `Nat`, anonymous constructors `⟨…⟩`, `∃`/`∧`/`¬`/`=`. **New here:** the core-Lean inductive predicate `Acc`
and the structure `WellFounded`, induction on an `Acc` proof and well-founded induction
(`WellFounded.induction`), `generalizing`, the lexicographic relation `Prod.Lex`, transport `▸`, classical
reasoning (`Classical.byContradiction`, `Classical.choose`), subtypes `{x // p x}`, `let`, and the recursor
`Nat.rec` used as an iterator. Core Lean only: no Mathlib.

**The maths.** `r : α → α → Prop` is a relation; read `r y x` as "`y` is one step *below* `x`" (`y` is an
`r`-predecessor of `x`).

- `Acc r x` (*`x` is accessible*) is the inductive predicate with one rule: if every predecessor `y` of `x` is
  accessible, so is `x`. Rule: `Acc.intro x (h : ∀ y, r y x → Acc r y) : Acc r x`. Since a proof is a finite
  tree, every descending path from an accessible `x` is finite.
- `WellFounded r` means every `x` is accessible: `WellFounded.intro (h : ∀ a, Acc r a)`.
- A *descending chain* is `f : Nat → α` with `r (f (n + 1)) (f n)` for every `n`: `f 0 > f 1 > f 2 > …`.
- `Prod.Lex r s` on `α × β`: `(a₁, b₁)` is below `(a₂, b₂)` when `r a₁ a₂` (any `b₁, b₂`), or `a₁ = a₂` and
  `s b₁ b₂`. This is dictionary order.

The four facts: (1) well-founded ⇒ irreflexive (`r a a` would give an infinite chain `a > a > …`); (2) `r, s`
well-founded ⇒ `Prod.Lex r s` well-founded; (3) well-founded ⇒ no descending chain; (4) no descending chain ⇒
well-founded. (4) is classical: from a non-accessible `a`, choose a non-accessible predecessor, again and
again (dependent choice), and that is a chain.

## How to read an entry

Each entry is one tactic or one term-building move. It says what changes (**goal**, **context**, or
**goal list**), gives the lemma's statement when there is one, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `C`, `P`, `Q` are "the rest of your goal": predicates such as `C : α → Prop` or `P : α × β → Prop`.
- Placeholders are written as Lean binders: `{α β : Type}` are any types; `(r : α → α → Prop)` and
  `(s : β → β → Prop)` are relations; `(A G : Prop)` are propositions; `(p : α → Prop)` is a property.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Acc r a` | `a` is accessible for `r` (see above). Its one constructor is `Acc.intro` |
| `WellFounded r` | every element is `Acc r`; a structure with constructor `WellFounded.intro` |
| `α × β`, `(a, b)` | the product type and a pair; `p.1`, `p.2` are its components |
| `Prod.Lex r s p q` | `p` is below `q` in the lexicographic order (constructors `.left`, `.right`, R7) |
| `¬A` | `A → False` (R2) |
| `x ≠ y` | `¬(x = y)`, i.e. `x = y → False` |
| `{ x // p x }` | the *subtype*: pairs `⟨v, hv⟩` of a value `v : α` and a proof `hv : p v` (R16) |
| `z.val` (also written `z.1`) | the value inside `z : { x // p x }`; `z.2 : p z.val` is the proof (R17) |
| `Classical.choose h` | for `h : ∃ x, Q x`, a witness picked by the axiom of choice (R18) |
| `t : α := e` (in the context) | a local definition made by `let` (R19); Lean unfolds `t` to `e` when needed |
| `Nat.rec x (fun x y => g y) n` | `g` applied `n` times to `x` (R20). Lean renames the bound variables (`x`, `x_1`) |
| `(fun n => e) k` | a function applied but not yet simplified: it is `e` with `k` for `n`. `exact` sees through it |
| `⋯` | a proof term Lean does not print |
| `a✝`, `h✝`, `x✝` | names Lean invented; you cannot type them. Name them in `with \| intro x hx ih` |
| `case h`, `case intro`, `case left` | the goal belongs to that constructor or induction alternative |

---

## Part 1 · `wf_irrefl`

Statement: `WellFounded r → ¬ r a a`. Well-founded induction on `a` (R1), with goal `C a := ¬ r a a`. In the
induction step the goal is `¬r a a` and `ih : ∀ (y : α), r y a → ¬r y y`. Assume `hr : r a a` (R2); then
`a` is a predecessor of itself, so the IH at `y := a` applies (R3).

**R1 · `induction a using hw.induction with | _ x ih => …`** changes the **goal and the context**. The lemma
is `WellFounded.induction : WellFounded r → ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a`, where the motive
`C : α → Prop` is the current goal read as a function of `a`. The only alternative is called `h`; `_` matches
it. Placeholders: `{α : Type} (r : α → α → Prop) (C : α → Prop) (hw : WellFounded r) (a : α)`.

| Before | After |
|---|---|
| `a : α ⊢ C a` | `x : α ⊢ C x` (and `ih : ∀ (y : α), r y x → C y`) |

Everything still in the goal goes into `C`; everything already introduced stays fixed. So introduce only what
must stay fixed before you induct.

**R2 · `intro h`** on `¬A` changes the **goal and the context**: `¬A` is `A → False`, so `h : A` is added and
the goal becomes `False`. As a term: `fun h => …`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R3 · `exact ih y hy hq`** **closes** the goal by applying an induction hypothesis. `ih` is a function: give it
the point `y`, the step `hy : r y x`, and then whatever its conclusion still expects. When the conclusion is
`¬Q y`, that is a function `Q y → False`, so one more argument `hq : Q y` gives `False`. Placeholders:
`{α : Type} (r : α → α → Prop) (Q : α → Prop) (x y : α)`.

| Before | After |
|---|---|
| `hy : r y x, hq : Q y ⊢ False` | closed by `exact ih y hy hq` (with `ih : ∀ y, r y x → ¬Q y`) |

---

## Part 2 · `acc_lex` (milestone)

Statement: `WellFounded s → Acc r a → ∀ b, Acc (Prod.Lex r s) (a, b)`. Prove it first; `wf_lex` is one line
from it. A double induction: outer on `ha : Acc r a` generalizing `b` (R4, R5), inner on `b` by `hs` (R1).
After R6 and `intro p hp` the state is

```
iha : ∀ (y : α), r y a → ∀ (b : β), Acc (Prod.Lex r s) (y, b)
ihb : ∀ (y : β), s y b → Acc (Prod.Lex r s) (a, y)
hp : Prod.Lex r s p (a, b)
goal: Acc (Prod.Lex r s) p
```

and `cases hp` (R7) gives the two cases: the first component went down (use `iha`) or it stayed `a` and the
second went down (use `ihb`) (R3).

**R4 · `induction ha with | intro x hx ih => …`** (with `ha : Acc r a`) changes the **goal and the context**.
`Acc` has one constructor, so there is one goal, for a fresh `x` with `hx : ∀ y, r y x → Acc r y` (the
constructor's argument) and the IH `ih : ∀ y, r y x → C y`. Same shape as R1, but from a proof of `Acc r a`
instead of `WellFounded r`. Placeholders: `{α : Type} (r : α → α → Prop) (C : α → Prop) (a : α) (ha : Acc r a)`.

| Before | After |
|---|---|
| `ha : Acc r a ⊢ C a` | `x : α ⊢ C x` (and `hx`, `ih : ∀ (y : α), r y x → C y`) |

**R5 · `induction ha generalizing b with …`** changes the **goal and the context**: `b` is taken out of the
context before the induction and put back after, so the IH holds for *every* `b`. Without it, `b` stays fixed
and the IH is about that one `b`, which is useless in the `left` case of R7 (the second component there is
arbitrary). Placeholders: `{α β : Type} (C : α → β → Prop) (ha : Acc r a) (b : β)`.

| Before | After |
|---|---|
| `ha : Acc r a, b : β ⊢ C a b` | `x : α, b : β ⊢ C x b` (and `ih : ∀ (y : α), r y x → ∀ (b : β), C y b`) |

**R6 · `constructor`** on `Acc r a` changes the **goal**: it applies `Acc.intro`, so you must show that every
predecessor is accessible. Placeholders: `{α : Type} (r : α → α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ Acc r a` | `⊢ ∀ (y : α), r y a → Acc r y` |

Then `intro p hp` (Lean basics).

**R7 · `cases hp with | left _ _ h => … | right _ h => …`** (with `hp : Prod.Lex r s p (a, b)`) changes the
**goal list**: one goal per constructor of `Prod.Lex`, and `p` is replaced by the pair that constructor
builds. The constructors are
`Prod.Lex.left {a₁} (b₁) {a₂} (b₂) (h : r a₁ a₂) : Prod.Lex r s (a₁, b₁) (a₂, b₂)` and
`Prod.Lex.right (a) {b₁ b₂} (h : s b₁ b₂) : Prod.Lex r s (a, b₁) (a, b₂)`; `with` names only the explicit
arguments, hence `left _ _ h` and `right _ h`. Placeholders:
`{α β : Type} (r : α → α → Prop) (s : β → β → Prop) (P : α × β → Prop) (a : α) (b : β) (p : α × β)`.

| Before | After |
|---|---|
| `⊢ P p` (with `hp : Prod.Lex r s p (a, b)`) | `h : r a₁✝ a ⊢ P (a₁✝, b₁✝)`, `h : s b₁✝ b ⊢ P (a, b₁✝)` |

In `acc_lex` the `left` goal is `Acc (Prod.Lex r s) (a₁✝, b₁✝)`: `iha _ h _`. The `right` goal is
`Acc (Prod.Lex r s) (a, b₁✝)`: `ihb _ h`.

---

## Part 3 · `wf_lex`

Statement: `WellFounded r → WellFounded s → WellFounded (Prod.Lex r s)`. Open the structure (R8), split the pair
(R9), get `Acc r a` from `hr` (R10) and apply the milestone `acc_lex`. One line in term mode:
`⟨fun ⟨a, b⟩ => …⟩`. In tactic mode put R9's pattern inside R8's binder, `refine ⟨fun ⟨a, b⟩ => ?_⟩`, which
leaves `a : α, b : β` and the goal `Acc (Prod.Lex r s) (a, b)`. A plain R8 leaves `x : α × β ⊢ Acc (Prod.Lex r s) x`,
which has no `∀` for `intro ⟨a, b⟩` to open (it fails with "no additional binders"); there, `obtain ⟨a, b⟩ := x`
splits the pair instead.

**R8 · `refine ⟨fun x => ?_⟩`** on `WellFounded r` changes the **goal and the context**: `WellFounded r` is a
structure with the single field `∀ a, Acc r a`, so `⟨…⟩` is `WellFounded.intro …`. Placeholders:
`{α : Type} (r : α → α → Prop)`.

| Before | After |
|---|---|
| `⊢ WellFounded r` | `x : α ⊢ Acc r x` |

**R9 · `intro ⟨x, y⟩`** on `∀ p : α × β, P p` changes the **context and the goal**: the pair is split into its
components. As a term: `fun ⟨x, y⟩ => …`. Placeholders: `{α β : Type} (P : α × β → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (p : α × β), P p` | `x : α, y : β ⊢ P (x, y)` |

**R10 · `hw.apply x`** **closes** `Acc r x`. The lemma is `WellFounded.apply : WellFounded r → ∀ a, Acc r a`
(the field of R8, read back). Placeholders: `(hw : WellFounded r) (x : α)`.

| Before | After |
|---|---|
| `hw : WellFounded r ⊢ Acc r x` | closed by `exact hw.apply x` |

---

## Part 4 · `acc_not_in_chain` (milestone)

Statement: for a chain `f` (`hf : ∀ n, r (f (n + 1)) (f n)`), an accessible `x` is never on it:
`Acc r x → ∀ n, f n ≠ x`. Prove it first; `no_descending_chain` uses it at `n = 0`. Induct on `hx` (R4), with
`f, hf` fixed, so `ih : ∀ (y : α), r y x → ∀ (n : Nat), f n ≠ y`. `intro n hn` gives `hn : f n = x` and the goal
`False` (`≠` is a `¬`, R2). The next chain element `f (n + 1)` is a predecessor of `x`: transport `hf n` along
`hn` (R11) and apply the IH at index `n + 1` to `rfl` (R3).

**R11 · `exact h ▸ hp`** **closes** `P b` from `h : a = b` and `hp : P a`: `▸` rewrites the type of `hp` with
`h` (in whichever direction makes it fit the goal). It works inside a larger term, where `rw` cannot be used.
Placeholders: `{α : Type} (P : α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `h : a = b, hp : P a ⊢ P b` | closed |

In the milestone: `hn ▸ hf n : r (f (n + 1)) x`.

---

## Part 5 · `no_descending_chain`

Statement: `WellFounded r → ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n)`. Take the chain apart (R12); `f 0` is
accessible (R10); `acc_not_in_chain` then says `f 0 ≠ f 0`, which `rfl` refutes (R3).

**R12 · `intro ⟨x, hx⟩`** on `¬∃ x, P x` changes the **context and the goal**: the assumed `∃` is split into
the witness and its property, and the goal is `False`. As a term: `fun ⟨x, hx⟩ => …`. Placeholders:
`{α : Type} (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∃ x, P x` | `x : α, hx : P x ⊢ False` |

---

## Part 6 · `not_acc_step` (milestone)

Statement: `¬ Acc r x → ∃ y, r y x ∧ ¬ Acc r y`: a non-accessible point has a non-accessible predecessor.
Prove it first; it is the step of the chain in Part 7. Classical: assume the conclusion fails
(`hno : ¬∃ y, r y x ∧ ¬Acc r y`, R13) and contradict `hx` by proving `Acc r x` (R15, R14). That leaves
`y : α, hy : r y x` and the goal `Acc r y`; prove it by contradiction again (R13), and `hno ⟨y, hy, hy'⟩`
closes.

**R13 · `refine Classical.byContradiction fun hn => ?_`** changes the **goal and the context**. The lemma is
`Classical.byContradiction : (¬p → False) → p`. It is classical: Lean proves it from the axiom of choice
(`Classical.choice`, allowed here). Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ A` | `hn : ¬A ⊢ False` |

**R14 · `refine .intro x fun y hy => ?_`** on `Acc r x` changes the **goal and the context**: R6 in term form,
with the predecessor and its step already introduced. `.intro` means `Acc.intro` (a leading `.` takes the
constructor from the expected type). Placeholders: `{α : Type} (r : α → α → Prop) (x : α)`.

| Before | After |
|---|---|
| `⊢ Acc r x` | `y : α, hy : r y x ⊢ Acc r y` |

**R15 · `refine hn ?_`** with `hn : ¬A` changes the **goal**: to prove `False` it suffices to prove `A`.
`apply hn` does the same. Placeholders: `(A : Prop) (hn : ¬A)`.

| Before | After |
|---|---|
| `hn : ¬A ⊢ False` | `hn : ¬A ⊢ A` |

In the milestone R15 and R14 combine into one term: `hx (.intro x fun y hy => ?_)`.

---

## Part 7 · `wf_of_no_descending_chain`

Statement: `(¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n)) → WellFounded r`. Open the structure (R8) and argue by
contradiction (R13): `ha : ¬Acc r a`, goal `False`; reduce it to building a chain (R15). Now build it, carrying
the proof of `¬Acc` along in a subtype `{ x // ¬Acc r x }`:

1. `next : { x // ¬Acc r x } → { x // ¬Acc r x }` (R19): from `z`, `not_acc_step z.2` (R17) is an `∃`; take
   its witness (R18) and pack it with the second half of its spec (R16).
2. `f : Nat → { x // ¬Acc r x }`: iterate `next` from `⟨a, ha⟩` with `Nat.rec` (R19, R20, R16).
3. The chain is `fun n => (f n).1`. Its step at `n` is the first half of `Classical.choose_spec (not_acc_step (f n).2)`:
   `exact` accepts it because `(f (n + 1)).1` unfolds by computation to `Classical.choose (not_acc_step (f n).2)` (R20).
   If you write `refine ⟨fun n => (f n).1, fun n => ?_⟩` first, the goal prints unreduced as
   `r ((fun n => (f n).val) (n + 1)) ((fun n => (f n).val) n)`; that is the same proposition, and the same `exact` closes it.

After the two `let`s the context shows

```
next : { x // ¬Acc r x } → { x // ¬Acc r x } := fun x => ⟨Classical.choose ⋯, ⋯⟩
f : Nat → { x // ¬Acc r x } := fun n => Nat.rec ⟨a, ha⟩ (fun x x_1 => next x_1) n
goal: ∃ f, ∀ (n : Nat), r (f (n + 1)) (f n)
```

**R16 · `exact ⟨v, hv⟩`** **closes** a subtype goal `{ x // p x }`: an element of the subtype is a value and a
proof about it (constructor `Subtype.mk`). Placeholders: `{α : Type} (p : α → Prop) (v : α) (hv : p v)`.

| Before | After |
|---|---|
| `hv : p v ⊢ { x // p x }` | closed |

**R17 · `z.1`, `z.2`** for `z : { x // p x }`: `z.1 : α` is the value (Lean prints it `z.val`) and
`z.2 : p z.val` is the proof. `exact z.2` **closes** the goal. Placeholders: `{α : Type} (p : α → Prop)`.

| Before | After |
|---|---|
| `z : { x // p x } ⊢ p z.val` | closed by `exact z.2` |

**R18 · `Classical.choose`, `Classical.choose_spec`** change the **context** (here through `have`). For
`h : ∃ x, Q x`: `Classical.choose h : α` is a witness and `Classical.choose_spec h : Q (Classical.choose h)`.
You need them because an `∃` proof cannot be taken apart (with `obtain`) when the goal is data, such as the
body of a function `Nat → α`. Placeholders: `{α : Type} (Q : α → Prop) (h : ∃ x, Q x) (G : Prop)`.
For `h : ∃ y, A y ∧ B y`, the two halves are `(Classical.choose_spec h).1` and `.2`.

| Before | After `have hc := Classical.choose_spec h` |
|---|---|
| `⊢ G` (with `h : ∃ x, Q x`) | `hc : Q (Classical.choose h) ⊢ G` |

**R19 · `let t : T := e`** changes the **context**: it adds a local definition `t : T := e`; the goal is
unchanged. Unlike `have`, Lean remembers the body, so later goals about `t` can be checked by unfolding it.
Placeholders: `{α : Type} (g : α → α) (a : α)`.

| Before | After |
|---|---|
| `⊢ P (g a)` | `t : α := g a ⊢ P (g a)` |

**R20 · `Nat.rec x (fun _ y => g y) n`** is `g` applied `n` times to `x`. `Nat.rec` is the recursor of `Nat`:
`Nat.rec x step 0` computes to `x` and `Nat.rec x step (n + 1)` to `step n (Nat.rec x step n)`. These are
definitional, so `show`, `exact` and `rfl` use them without any lemma. `show G'` changes the **goal** to a
definitionally equal `G'`. Placeholders: `{α : Type} (P : α → Prop) (g : α → α) (x : α) (n : Nat)`.

| Before | After `show P (g (Nat.rec x (fun _ y => g y) n))` |
|---|---|
| `⊢ P (Nat.rec x (fun x y => g y) (n + 1))` | `⊢ P (g (Nat.rec x (fun x y => g y) n))` |

`Nat.rec` needs its expected type to be known (here `α`); give the `let` a type, as in
`let f : Nat → { x // ¬Acc r x } := fun n => Nat.rec ⟨a, ha⟩ (fun _ z => next z) n`.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a smaller relation keeps accessibility.** With `hsub : ∀ x y, q x y → r x y` and `ha : Acc r a`, prove
`Acc q a`: `induction ha with | intro x _ ih =>` (R4), `constructor` (R6), `intro y hy`, then
`exact ih y (hsub y x hy)` (R3). Before the induction:

```lean-goal
⊢ Acc q a
```

**W2: a predecessor for every point gives a chain.** With `hs : ∀ x, ∃ y, s y x`: `let pred : α → α := fun x =>
Classical.choose (hs x)` (R19, R18), `let c : Nat → α := fun k => Nat.rec a (fun _ x => pred x) k` (R20), then
`exact ⟨c, fun k => Classical.choose_spec (hs (c k))⟩`, accepted by unfolding `c (k + 1)` (R20). The goal
throughout:

```lean-goal
⊢ ∃ c, ∀ (k : Nat), s (c (k + 1)) (c k)
```

Part 7 is the same construction, except that the predecessor exists only for non-accessible points, so the
proof of `¬Acc` must travel with the point: hence the subtype.

**W3: the two `Prod.Lex` constructors on pairs of numbers.** `(1, 9)` is below `(2, 0)` by
`.left _ _ (by decide)` (first components `1 < 2`); `(2, 3)` is below `(2, 7)` by `.right _ (by decide)` (same
first component, `3 < 7`).

---

## Traps

- **Banned shortcuts** (former card NOTE): core's ready-made lex lemmas (`Prod.lexAccessible`,
  `WellFounded.prod_lex`, `Prod.instWellFoundedRelation`, …) and `termination_by`/`decreasing_by` recursion are
  banned. Prove `acc_lex` by `induction` on `Acc` (R4), not by recursion on the function.
- **Forgetting `generalizing b`** in `acc_lex`: the outer IH is then about one fixed `b`, but the `left` case
  of R7 needs it at an arbitrary second component `b₁✝` (R5).
- **Order of the two inductions in `acc_lex`:** outer on `ha` (first component), inner on `b`. Inside the inner
  one, `a` is fixed, which is exactly what the `right` case needs.
- **Direction of `r`.** `r y x` means `y` is *below* `x`. The chain condition is `r (f (n + 1)) (f n)`: each
  element is below the previous one. The IH of R1/R4 speaks about predecessors `y` with `r y x`.
- **`obtain` on an `∃` while building data.** Inside the `let` of a function you cannot destructure an `∃`
  proof; use `Classical.choose`/`Classical.choose_spec` (R18).
- **The chain has to carry `¬Acc`.** `Nat.rec` over plain `α` loses the proof that the current point is
  non-accessible, which the next `not_acc_step` needs. Iterate on `{ x // ¬Acc r x }` and project with `.1`.
- **`Nat.rec` without an expected type** fails to elaborate; annotate the `let` (R20).
- **`intro ⟨a, b⟩` after `refine ⟨fun x => ?_⟩`** fails: the binder is already used up. Write the pattern in the
  binder, `refine ⟨fun ⟨a, b⟩ => ?_⟩` (R8, R9).
- `▸` may need the expected type: write it where the goal is known (`exact hn ▸ hf n` or as an argument).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| well-founded induction | `induction a using hw.induction with \| _ x ih => …` | R1 |
| prove `¬A` | `intro h` / `fun h => …` | R2 |
| use the IH | `ih y hy` (plus more args if its conclusion is `¬…`) | R3 |
| induction on `ha : Acc r a` | `induction ha with \| intro x hx ih => …` | R4 |
| IH for every `b` | `induction ha generalizing b with …` | R5 |
| prove `Acc r a` | `constructor` / `.intro a fun y hy => …` | R6, R14 |
| split a lex step | `cases hp with \| left _ _ h => … \| right _ h => …` | R7 |
| prove `WellFounded r` | `⟨fun a => …⟩` | R8 |
| split a pair binder | `intro ⟨a, b⟩` / `fun ⟨a, b⟩ => …` | R9 |
| `Acc r a` from `hw : WellFounded r` | `hw.apply a` | R10 |
| rewrite inside a term | `h ▸ e` | R11 |
| assume an `∃` for `¬∃` | `intro ⟨x, hx⟩` / `fun ⟨x, hx⟩ => …` | R12 |
| proof by contradiction | `Classical.byContradiction fun hn => …` | R13 |
| `False` from `hn : ¬A` | `hn ?_`, `apply hn` | R15 |
| subtype element / parts | `⟨v, hv⟩`, `z.1`, `z.2` | R16, R17 |
| witness of an `∃` as data | `Classical.choose h`, `Classical.choose_spec h` | R18 |
| local definition | `let t : T := e` | R19 |
| iterate `g` `n` times | `Nat.rec x (fun _ y => g y) n` | R20 |
| milestones | `acc_lex`, `acc_not_in_chain`, `not_acc_step` | Parts 2, 4, 6 |
| see the state | infoview | |
