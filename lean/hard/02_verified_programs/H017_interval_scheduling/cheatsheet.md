# H017 · Greedy interval scheduling is optimal: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `structure` and field access `x.f`, pattern-matching `def`,
`List`, `intro`, `exact`, `apply`, `rw`, `simp`, `cases`, `induction`, `have`. **New here:** core Lean only
(no Mathlib): `induction … generalizing`, `split` on an `if` in the goal, recursive predicates (a `def`
returning `Prop`) and how Lean unfolds them, the sublist relation `List.Sublist` and `cases` on it,
`List.Pairwise` (sortedness), `omega`, `rename_i`, `absurd`, and the exchange argument.

The problem in one paragraph. An interval `i : Iv` has a start `i.s` and a finish `i.f` (both `Nat`).
`Compatible t S` says the intervals of `S`, in order, each start at or after the previous one's finish, and
the first starts at or after the threshold `t`. `greedy t xs` scans `xs` and takes an interval `i` exactly
when `t ≤ i.s`, after which the threshold becomes `i.f`. On input sorted by finish time, greedy is
optimal: its output is a sublist of the input (MILESTONE 1), compatible (MILESTONE 2), and at least as long
as every compatible sublist (MILESTONE 4, the exchange argument; MILESTONE 3 is a helper for it). The spec
starts at threshold `0`, but every induction needs an arbitrary threshold `t`.

## How to read an entry

Each entry is one tactic or one lemma used with `apply`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `G`) is "the rest of your goal". The step changes only the part inside `P (…)`, wherever it sits
  in a larger goal. A hypothesis `h` or `k` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (in the exercise, `Iv`). `[Decidable c]`
  says the proposition `c` can be decided by a program (true of `t ≤ x` on `Nat`), which an `if c then … else …`
  needs.
- The guide's own objects: `bump` (a threshold scan on `Nat`), `Above` (a recursive chain predicate), `Asc`
  (a `def` around `List.Pairwise`), `Capped` and `keepLe`. They have the exercise's shapes, not its content.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- `∅` means the goal is closed.

## Reading the goals

| You see | It means |
|---|---|
| `x.s`, `x.f` | the start and the finish of the interval `x : Iv` |
| `S.Sublist xs` | `List.Sublist S xs`: `S` is `xs` with some entries deleted, order kept. Lemma docs write `S <+ xs` |
| `[].Sublist []` | the only sublist of `[]` is `[]` (constructor `List.Sublist.slnil`) |
| `List.Pairwise R l` | `R a b` for every `a` that comes before `b` in `l`. `SortedByFinish xs` is this with `R a b := a.f ≤ b.f` |
| `y ∈ xs` | `List.Mem`: `y` occurs in `xs` |
| `l₁ ⊆ l₂` | `List.Subset`: `∀ a, a ∈ l₁ → a ∈ l₂` (R17) |
| `(x :: l).length` | `List.length`; `List.length_cons` turns it into `l.length + 1` (R21) |
| `Compatible t (y :: S')` | a recursive `Prop`; Lean unfolds it to `t ≤ y.s ∧ Compatible y.f S'` when the list is a cons (R8, R11), and to `True` at `[]` (R7). On a variable list `S` it does not unfold |
| `if t ≤ x.s then … else …` | greedy's choice; `split` (R4) cases on it |
| `h✝`, `a✝`, `head✝`, `tail✝`, `tail_ih✝`, `l₁✝` | inaccessible names: Lean made them, you cannot type them. `rename_i` names them (R23), `with` patterns avoid them (R1, R16) |
| `case isTrue`, `case isFalse` | the `if` branch after `split` |
| `case cons`, `case cons_cons`, `case slnil` | the `List.Sublist` constructor after `cases hsub` (R13, R16) |
| `case cons.isTrue.cons.cons` | tags join with `.`: list `cons` case, `if` true branch, sublist `cons`, then `S` a cons |
| `case nil.slnil` | the list `nil` case after `cases hsub` with `hsub : S.Sublist []` (R13) |
| `case refine_1`, `refine_2`, `refine_3` | the goals `refine ⟨?_, ?_, ?_⟩` makes, in order (Part 5) |
| `∀ (y : Iv), y ∈ xs → x.f ≤ y.f` | how Lean prints `∀ y ∈ xs, x.f ≤ y.f` (the bounded-quantifier form you may type) |
| `this` | the name `have := e` gives its fact (R20) |

---

## Part 1 · `greedy_sublist` (MILESTONE 1)

Statement: `(greedy t xs).Sublist xs` for every threshold `t`. Induct on `xs`; greedy's threshold moves from
`t` to `x.f` when it takes `x`, so the induction hypothesis must hold for every threshold (R1).

**R1 · `induction xs generalizing t`** changes the **goal list**: one goal per constructor of `List`. The
variable `t` is removed from the context first and quantified in the induction hypothesis, so in the
`cons` case you get `tail_ih✝ : ∀ (t : Nat), P t tail✝` and can use it at any threshold (`ih x.f`).
Placeholders: `{α : Type} (P : Nat → List α → Prop) (t : Nat) (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ P t xs` | `t : Nat ⊢ P t []`, `tail✝ : List α ⊢ P t (head✝ :: tail✝)` |

The `cons` goal also has `head✝ : α` and `tail_ih✝ : ∀ (t : Nat), P t tail✝`. Write
`induction xs generalizing t with | nil => … | cons x xs ih => …` to name them yourself (W1, W3). For
MILESTONE 4, generalize both: `generalizing t S`.

**R2 · `simp [f]`** **closes** the `nil` goal: `f t []` unfolds to `[]` and `simp` knows `[] <+ l`
(`List.nil_sublist`). Placeholders: `(t : Nat)`, with `bump` the guide's scan.

| Before | After |
|---|---|
| `⊢ (bump t []).Sublist []` | ∅ |

In the problem: `simp [greedy]` closes `(greedy t []).Sublist []`.

**R3 · `simp only [f]`** changes the **goal**: `f` applied to a cons is replaced by the body of `f`'s
`cons` clause, here an `if`. Placeholders: `(t x : Nat) (xs : List Nat) (P : List Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (bump t (x :: xs))` | `⊢ P (if t ≤ x then x :: bump (x + 1) xs else bump t xs)` |

In the problem: `simp only [greedy]` turns `greedy t (x :: xs)` into
`if t ≤ x.s then x :: greedy x.f xs else greedy t xs`.

**R4 · `split`** changes the **goal list and the context**: with an `if c then a else b` in the goal, it
makes one goal per branch, adds the branch condition as an inaccessible hypothesis, and replaces the `if` by
the branch. Placeholders: `{α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h✝ : c ⊢ P a`, `h✝ : ¬c ⊢ P b` |

**R5 · `List.Sublist.cons_cons`** changes the **goal**. The lemma (a constructor of `List.Sublist`) is
`(a : α) : l₁ <+ l₂ → a :: l₁ <+ a :: l₂`: keep the same head on both sides. Term form with dot notation:
`h.cons_cons a`, e.g. `(ih x.f).cons_cons x`. Placeholders: `{α : Type} (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ (a :: l₁).Sublist (a :: l₂)` | `⊢ l₁.Sublist l₂` |

**R6 · `List.Sublist.cons`** changes the **goal**. The lemma is `(a : α) : l₁ <+ l₂ → l₁ <+ a :: l₂`:
skip a head on the right. Term form: `h.cons a`, e.g. `(ih t).cons x`. Placeholders: as in R5.

| Before | After |
|---|---|
| `⊢ l₁.Sublist (a :: l₂)` | `⊢ l₁.Sublist l₂` |

---

## Part 2 · `greedy_compatible` (MILESTONE 2)

Statement: `Compatible t (greedy t xs)`. Same induction as Part 1 (R1, R3, R4). The new part is working
with the recursive predicate `Compatible`.

**R7 · `trivial`** **closes** a goal that unfolds to `True`. `Above t []` (like `Compatible t []`) is
defined to be `True`. Placeholders: `(t : Nat)`.

| Before | After |
|---|---|
| `⊢ Above t []` | ∅ |

In the problem the `nil` goal reads `Compatible t (greedy t [])`: `greedy t []` unfolds to `[]` and then
`Compatible t []` to `True`, and `trivial` sees through both.

**R8 · `refine ⟨?_, ?_⟩`** changes the **goal list**: `Above t (x :: xs)` is defined as
`t ≤ x ∧ Above (x + 1) xs`, and the anonymous constructor `⟨_, _⟩` sees through the definition to the `∧`.
`exact ⟨e₁, e₂⟩` does the same in one step. Placeholders: `(t x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ Above t (x :: xs)` | `⊢ t ≤ x`, `⊢ Above (x + 1) xs` |

In the problem's taken branch the goal is `Compatible t (x :: greedy x.f xs)`, i.e.
`t ≤ x.s ∧ Compatible x.f (greedy x.f xs)`: the first half is the `h✝` from `split` (R9), the second is
`ih x.f`.

**R9 · `assumption`** **closes** the goal with a hypothesis of exactly that type, inaccessible ones
included (you cannot type `h✝`, but `assumption` finds it). Inside a term write `by assumption`:
`⟨by assumption, …⟩`. Placeholders: `(t x : Nat)`.

| Before | After |
|---|---|
| `a✝ : t ≤ x ⊢ t ≤ x` | ∅ |

---

## Part 3 · `compatible_mono` (MILESTONE 3)

Statement: `Compatible t' S → t ≤ t' → Compatible t S`. Lowering the threshold keeps a chain compatible,
because only the first interval is compared with it. No induction: case on `S` (R10) so that `Compatible`
unfolds, then rebuild the pair (R8) from the halves of `h` (R11).

**R10 · `cases S`** changes the **goal list**: one goal for `S = []` and one for `S = head✝ :: tail✝`
(`cases S with | nil => … | cons i is => …` names them). Placeholders: `{α : Type} (P : List α → Prop)
(S : List α)`.

| Before | After |
|---|---|
| `S : List α ⊢ P S` | `⊢ P []`, `tail✝ : List α ⊢ P (head✝ :: tail✝)` |

**R11 · `h.1`, `h.2`** change the **context** (with `have`): `h : Above t (x :: xs)` unfolds to
`t ≤ x ∧ Above (x + 1) xs`, and `.1`/`.2` are its two halves. This works only once the list is a cons:
on `h : Compatible t S` with `S` a variable, `h.1` fails (R10 first). Placeholders:
`(t x : Nat) (xs : List Nat)`.

| Before | After `have h1 := h.1` | After `have h2 := h.2` |
|---|---|---|
| `h : Above t (x :: xs) ⊢ G` | `h1 : t ≤ x ⊢ G` | `h2 : Above (x + 1) xs ⊢ G` |

**R12 · `Nat.le_trans`** changes the **goal**. The lemma is `n ≤ m → m ≤ k → n ≤ k`; `apply
Nat.le_trans hab` with `hab : a ≤ b` leaves the second link. Term form: `Nat.le_trans hab hbc`.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `hab : a ≤ b ⊢ a ≤ c` | `⊢ b ≤ c` |

---

## Part 4 · `greedy_stays_ahead` (MILESTONE 4, the exchange argument)

Statement: on sorted `xs`, if `S <+ xs` and `Compatible t S`, then `S.length ≤ (greedy t xs).length`.
Induct on `xs` generalizing **both** `t` and `S` (R1): the competitor `S` shrinks along with `xs`. In the
`cons x xs` case, after unfolding greedy and splitting its `if` (R3, R4), case on how `S` uses `x` (R16):

| greedy | `S` | argument |
|---|---|---|
| takes `x` | skips `x`, `S = []` | `0 ≤ …` |
| takes `x` | skips `x`, `S = y :: S'` | **exchange**: `y ∈ xs`, so sortedness gives `x.f ≤ y.f`, and `S'` is compatible after `y.f` (`hc.2`), hence after `x.f` (MILESTONE 3), IH bounds `S'`, and `S` is one longer than `S'` |
| takes `x` | keeps `x` (`S = x :: l₁✝`) | IH at threshold `x.f` for `l₁✝` (pass it as `_`), then `+1` on both sides |
| skips `x` (`¬t ≤ x.s`) | skips `x` | IH at the same threshold `t` |
| skips `x` | keeps `x` | impossible: `hc.1 : t ≤ x.s` |

**R13 · `cases hsub`, `hsub : S.Sublist []`** changes the **context**: only `List.Sublist.slnil : [] <+ []`
proves a sublist of `[]`, so `S` is replaced by `[]` and `hsub` is gone. Placeholders: `{α : Type}
(S : List α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `hsub : S.Sublist [] ⊢ P S` | `⊢ P []` |

**R14 · `simp`** **closes** `[].length ≤ n`: it rewrites `[].length` to `0` and `0 ≤ n` to `True`.
Placeholders: `{α : Type} (n : Nat)`.

| Before | After |
|---|---|
| `⊢ [].length ≤ n` | ∅ |

In the problem's `nil` case: `cases hsub` (R13), then `simp` closes `[].length ≤ (greedy t []).length`.

**R15 · `List.pairwise_cons`** changes the **context** (with `have`). The lemma is the iff
`Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l`; `.mp` uses it left to right, `.1` is
"`a` is related to every later entry" and `.2` is "the tail is pairwise". It applies to
`hs : SortedByFinish (x :: xs)` directly, because Lean unfolds the `def` to `List.Pairwise …` (W4). Write
the type to keep the `def` name: `have hs' : SortedByFinish xs := (List.pairwise_cons.mp hs).2`.
Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After `have h2 := (List.pairwise_cons.mp hs).2` |
|---|---|
| `hs : List.Pairwise R (a :: l) ⊢ G` | `h2 : List.Pairwise R l ⊢ G` |

`have h1 := (List.pairwise_cons.mp hs).1` adds `h1 : ∀ (a' : α), a' ∈ l → R a a'`. In the problem:
`hfx : ∀ (y : Iv), y ∈ xs → x.f ≤ y.f`, so `hfx y hy : x.f ≤ y.f`.

**R16 · `cases hsub`, `hsub : S.Sublist (a :: l)`** changes the **goal list and the context**: a sublist of
`a :: l` either skips `a` (constructor `cons`, giving `S <+ l`) or keeps it (constructor `cons_cons`,
`S` becomes `a :: l₁✝` with `l₁✝ <+ l`). `slnil` cannot match `a :: l` and gives no goal. With names:
`cases hsub with | cons _ h => … | cons_cons _ h => …`; the `_` is the head `a`, already known.
Placeholders: `{α : Type} (a : α) (l S : List α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `hsub : S.Sublist (a :: l) ⊢ P S` | `a✝ : S.Sublist l ⊢ P S`, `a✝ : l₁✝.Sublist l ⊢ P (a :: l₁✝)` |

In the problem, the keep case turns `hc : Compatible t S` into `hc : Compatible t (x :: l₁✝)`, so `hc.2`
(R11) is `Compatible x.f l₁✝`: exactly what the IH at `x.f` needs. In the skip case `S` is still a
variable, so `hc` does not unfold: `cases S` (R10) first.

**R17 · `List.Sublist.subset`** changes the **goal**. The lemma is `l₁ <+ l₂ → l₁ ⊆ l₂`, and `l₁ ⊆ l₂`
means `∀ a, a ∈ l₁ → a ∈ l₂`, so `apply hsub.subset` turns membership in `l₂` into membership in `l₁`.
Term form: `hsub.subset hy`. Placeholders: `{α : Type} (y : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `hsub : l₁.Sublist l₂ ⊢ y ∈ l₂` | `⊢ y ∈ l₁` |

**R18 · `List.mem_cons_self`** **closes** `a ∈ a :: l`. All its arguments are implicit, so write it bare:
`List.mem_cons_self`, not `List.mem_cons_self a l`. Placeholders: `{α : Type} (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ a ∈ a :: l` | ∅ |

Together: `have hy : y ∈ xs := hsub'.subset List.mem_cons_self` with `hsub' : (y :: S').Sublist xs`.

**R19 · `List.sublist_of_cons_sublist`** changes the **context** (with `have`). The lemma is
`a :: l₁ <+ l₂ → l₁ <+ l₂`: drop the head of the smaller list. Placeholders: `{α : Type} (a : α)
(l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `hsub : (a :: l₁).Sublist l₂ ⊢ G` | `h : l₁.Sublist l₂ ⊢ G` |

**R20 · `have := e`** changes the **context**: it adds `this : T`, where `T` is the type Lean computes for
`e`. Use it to put an instance of the induction hypothesis into the context, where `omega` (R22) can read
it. Placeholders: `{α : Type} (Q R : Nat → List α → Prop) (ih : ∀ t l, Q t l → R t l)`.

| Before | After |
|---|---|
| `hq : Q t l ⊢ G` | `this : R t l ⊢ G` |

In the problem's exchange case: `have := ih x.f S' hs' (List.sublist_of_cons_sublist hsub') h1` adds
`this : S'.length ≤ (greedy x.f xs).length`.

**R21 · `simp only [List.length_cons]`** changes the **goal**: `(a :: l).length = l.length + 1`.
Placeholders: `{α : Type} (a b : α) (l₁ l₂ : List α) (P : Nat → Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a :: l₁).length (b :: l₂).length` | `⊢ P (l₁.length + 1) (l₂.length + 1)` |

In the problem: `(y :: S').length ≤ (x :: greedy x.f xs).length` becomes
`S'.length + 1 ≤ (greedy x.f xs).length + 1`.

**R22 · `omega`** **closes** a goal of linear arithmetic over `Nat` (or `Int`): `+`, `-`, numerals, `≤`,
`<`, `=`, using the hypotheses in the context. Any other term, such as `l.length`, is an unknown number.
Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `this : l₁.length ≤ l₂.length ⊢ l₁.length + 1 ≤ l₂.length + 1` | ∅ |

**R23 · `rename_i h`** changes the **context**: the last inaccessible hypothesis gets the name `h`. After
`split` (R4) the condition is `h✝`; `rename_i htx` names it so you can pass it to `absurd`.
Placeholders: `(c G : Prop)`.

| Before | After |
|---|---|
| `a✝ : ¬c ⊢ G` | `hc : ¬c ⊢ G` |

**R24 · `absurd h hn`** **closes** any goal from `h : c` and `hn : ¬c`. The lemma is
`absurd : a → ¬a → b`. In the problem: `absurd hc.1 htx` with `hc.1 : t ≤ x.s` and `htx : ¬t ≤ x.s`.
Placeholders: `(c G : Prop)`.

| Before | After |
|---|---|
| `h : c, hn : ¬c ⊢ G` | ∅ |

---

## Part 5 · `greedy_optimal`

Statement: `SortedByFinish xs → IsOptimal xs (greedy 0 xs)`. `IsOptimal xs S` is defined as
`S.Sublist xs ∧ Compatible 0 S ∧ ∀ S', S'.Sublist xs → Compatible 0 S' → S'.length ≤ S.length`. Split it
into three goals with `refine ⟨?_, ?_, ?_⟩` (it sees through the `def`, like R8), then close them with
MILESTONES 1, 2 and 4 at `t := 0` (for the third, `intro S' hsub hc` first). A term
`⟨e₁, e₂, fun S' hsub hc => e₃⟩` works too.

**R25 · `unfold D`** changes the **goal**: the name `D` is replaced by its body. Optional here; use it to
see what `IsOptimal` asks before splitting it. Placeholders: `(xs : List Nat) (k : Nat) (P : Prop → Prop)`,
with `Capped` a guide `def`.

| Before | After |
|---|---|
| `⊢ P (Capped xs k)` | `⊢ P (xs.length ≤ k ∧ ∀ (x : Nat), x ∈ xs → x ≤ k)` |

### Worked combinations (W1–W5, on objects that are not the exercise's)

**W1.** `(keepLe k xs).Sublist xs` for a filter: induction (R1), unfold (R3), `split` (R4), then
`ih.cons_cons x` (R5) or `ih.cons x` (R6). The bound `k` does not move, so no `generalizing`.

```lean-goal
⊢ (keepLe k xs).Sublist xs
```

**W2.** If `S <+ x :: xs` and `x ∉ S`, then `S <+ xs`: `cases hsub with | cons _ h => … | cons_cons _ h => …`
(R16); in the `cons_cons` case `absurd List.mem_cons_self hx` (R18, R24).

```lean-goal
⊢ S.Sublist xs
```

**W3.** A sublist is no longer than the list: `induction xs generalizing S` (R1), `cases hsub` (R13, R16),
`have := ih …` (R20), `simp only [List.length_cons]; omega` (R21, R22). The same bookkeeping as
MILESTONE 4's two "keep/skip" cases.

```lean-goal
⊢ S.length ≤ xs.length
```

**W4.** Sortedness through a `def`: from `hs : Asc (x :: xs)` and `hsub : (y :: S).Sublist xs`, get
`hy : y ∈ xs` (R17, R18), `hs' : Asc xs` (R15, with the type written), and `x ≤ y` as
`(List.pairwise_cons.mp hs).1 y hy`; `S.Sublist xs` is R19.

```lean-goal
⊢ x ≤ y ∧ Asc xs ∧ S.Sublist xs
```

**W5.** Two steps into a chain: `h.1 : t ≤ i` and `h.2.1 : i + 1 ≤ j` (R11), then `Nat.le_trans` twice
(R12), bridging `i` to `i + 1` with `Nat.le_succ i : i ≤ i + 1`.

```lean-goal
⊢ t ≤ j
```

---

## Traps

- The spec starts greedy at threshold `0`, but greedy calls itself at `x.f`. Prove every milestone for an
  arbitrary `t` and `induction xs generalizing t` (R1); an induction on the spec statement itself has an
  IH about threshold `0` only, which is useless.
- MILESTONE 4 must also generalize `S`: the competitor in the IH is `S'` or `l₁`, not `S`.
- `split` needs the `if` in the goal: `simp only [greedy]` first (R3). Before that, the goal only says
  `greedy t (x :: xs)`.
- `hc.1`, `hc.2` need `S` to be a cons. After `cases hsub` the keep case has `S = x :: l₁✝`; the skip case
  does not, so `cases S` there (R10).
- `omega` reads only the context and linear arithmetic. Put the IH instance in with `have := …` (R20) and
  expose `+ 1` with `List.length_cons` (R21) before calling it.
- `List.mem_cons_self` takes no explicit arguments in this Lean version (R18).
- `cases hsub with | cons _ h | cons_cons _ h` needs two names per arm: the head (`_`) and the sublist proof.
- `t1 ; t2` runs `t2` on the first goal only. After `split` or `cases`, use bullets `·` or `case …`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction, the IH at every threshold | `induction xs generalizing t with \| nil => … \| cons x xs ih => …` | R1 |
| close `(greedy t []).Sublist []` | `simp [greedy]` | R2 |
| open greedy at a cons | `simp only [greedy]` | R3 |
| case on greedy's `if` | `split` | R4 |
| `a :: l₁ <+ a :: l₂` / `l₁ <+ a :: l₂` | `h.cons_cons a` / `h.cons a` | R5, R6 |
| `Compatible t []` | `trivial` | R7 |
| build `Compatible t (i :: is)` | `exact ⟨h₁, h₂⟩` / `refine ⟨?_, ?_⟩` | R8 |
| use the `h✝` from `split` | `by assumption` | R9 |
| `S` empty or a cons | `cases S with \| nil => … \| cons i is => …` | R10 |
| halves of `Compatible t (i :: is)` | `h.1`, `h.2` | R11 |
| chain two `≤` | `Nat.le_trans h₁ h₂` | R12 |
| `S <+ []` → `S = []` | `cases hsub` | R13 |
| `[].length ≤ n` | `simp` | R14 |
| head and tail of sortedness | `(List.pairwise_cons.mp hs).1`, `.2` | R15 |
| does `S` keep or skip the head | `cases hsub with \| cons _ h => … \| cons_cons _ h => …` | R16 |
| `y ∈ xs` from `(y :: S') <+ xs` | `hsub.subset List.mem_cons_self` | R17, R18 |
| `S' <+ xs` from `(y :: S') <+ xs` | `List.sublist_of_cons_sublist hsub` | R19 |
| IH instance into the context | `have := ih x.f S' hs' hsub h1` | R20 |
| lengths, then arithmetic | `simp only [List.length_cons]; omega` | R21, R22 |
| name the `if` condition | `rename_i htx` | R23 |
| contradiction | `absurd hc.1 htx` | R24 |
| see a `def`'s body | `unfold IsOptimal` | R25 |
| see the state | infoview | |
