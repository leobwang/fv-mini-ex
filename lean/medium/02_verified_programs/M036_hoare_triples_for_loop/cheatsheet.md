# M036 · Hoare triples for a for-loop (mvcgen warm-up): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, `Nat`, `theorem`, `have`, `∧`/`∨`, anonymous
projections. **New here:** imperative `do` notation over `Id` (below), and `Std.Do`, core Lean's library for
verifying monadic programs: Hoare triples, the verification-condition generator `mvcgen`, a loop
invariant over a `List.Cursor`, `grind` as the closer for the conditions it leaves, and
`Id.of_wp_run_eq`, which turns a triple into a fact about the value `.run`. No Mathlib. (M018 proves a
similar loop by unfolding it to `List.foldl`; here you reason in Hoare logic instead.)

**The program.** `maxLoop xs : Id Nat` is written in `do` notation. `Id` is the identity monad: an `Id Nat`
is just a `Nat` computed by a pure function, and `(maxLoop xs).run` is that `Nat`. Inside `do`,
`let mut m := 0` declares a local variable that later lines may reassign (`m := x`); `for x in xs do body`
runs `body` once per element of `xs`, left to right, with the current value of `m`; `if c then m := x`
without `else` leaves `m` unchanged; `return m` ends with the final value. Lean compiles this into a fold
over `xs`; here you never look at that translation, `mvcgen` does.

## How to read an entry

Each entry is one tactic, one lemma used with `rw`/`grind`, or one way to use a lemma as a term. It says
what changes (**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows
the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Prop → Prop` when the step rewrites a proposition). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- The `mvcgen` entries (R1, R3) need a real program, so they use small ones from `guide.lean`:
  `clampLo t n` returns `max n t` with an `if`, `sumBig t l` sums the elements of `l` above `t`.

## Reading the goals

| You see | It means |
|---|---|
| `Id Nat` | a program that returns a `Nat` and has no effects; `do`, `let mut`, `for` are notation for a pure function |
| `prog.run` | `Id.run prog`: the value the `Id` program computes |
| `⦃P⦄ prog ⦃Q⦄` | Hoare triple (`Std.Do.Triple`): if assertion `P` holds before, `Q` holds after `prog` returns |
| `⌜p⌝` | the proposition `p : Prop` viewed as an assertion (`Id` has no state, so it is just `p`). Type `\ulc` `\urc` |
| `⇓ r => ⌜Q r⌝` | postcondition on the returned value `r`; printed `PostCond.noThrow fun r => ⌜Q r⌝`. Type `\d=` |
| `⦃`, `⦄` | type `\{{` and `\}}` |
| `wp⟦prog⟧ Q` | weakest precondition: the assertion "running `prog` establishes `Q`" (R8) |
| ⊢ₛ A (in a hypothesis or goal) | the assertion A holds. Not the goal turnstile ⊢ |
| `∀ x ∈ xs, Q x` | `∀ x, x ∈ xs → Q x`; printed `∀ (x : Nat), x ∈ xs → Q x` (R11) |
| `case vc1.step.isTrue` | verification condition 1: one loop step, `then` branch of the body's `if` |
| `case vc2.step.isFalse` | the same step, `else` branch |
| `case vc3.pre` | the invariant at loop entry: `cur.prefix = []`, the `let mut` at its initial value |
| `case post.success` | the invariant at exit (`cur.prefix = xs`) implies the postcondition; often closed by `mvcgen` itself |
| `xs.Cursor`, `cur.prefix` | a split of `xs` into processed `prefix` and remaining `suffix` (R2) |
| `pref✝`, `cur✝`, `suff✝` | in a step VC: processed part, current element, rest, with `h✝ : xs = pref✝ ++ cur✝ :: suff✝` |
| `b✝ : Nat` | the value of the `let mut` before this step |
| `s✝ : Nat := b✝ + cur✝` | a `let` hypothesis: `s✝` names the updated value of the `let mut` |
| `__do_jp✝ : … := fun __r a => pure a` | a "join point" `mvcgen` makes for the code after an `if`; ignore it |
| `h✝`, `h✝¹`, `h✝²` | inaccessible hypotheses made by `mvcgen` (the cursor split, the branch condition, the invariant for `pref✝`); you cannot type their names, `grind` uses them |
| `{ down := p }` | `⌜p⌝` unfolded, as `#check @Id.of_wp_run_eq` prints it (an assertion over `Id` wraps a `Prop` in a structure with one field `down`) |

---

## Part 1 · `maxLoop_spec`

Statement: `⦃⌜True⌝⦄ maxLoop xs ⦃⇓ r => ⌜(∀ x ∈ xs, x ≤ r) ∧ (r = 0 ∨ r ∈ xs)⌝⦄`: the loop returns an
upper bound of `xs` that is `0` or an element of `xs` (so it is the maximum, and `0` for `[]`).

### Hoare triples and `mvcgen`

**R1 · `mvcgen [f]`** changes the **goal list**: a Hoare triple becomes its verification conditions (VCs),
plain `Prop` goals with no `⦃ ⦄` left. `[f]` tells it to unfold `f`. An `if` in the program gives one VC per
branch, tagged `isTrue` / `isFalse`, with the condition (or its negation) as a hypothesis. Placeholders:
`(t n : Nat)`, the program `clampLo t n`.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ clampLo t n ⦃PostCond.noThrow fun r => ⌜t ≤ r⌝⦄` | `h✝ : n < t ⊢ t ≤ t`, `h✝ : ¬n < t ⊢ t ≤ n` |

**R2 · `List.Cursor`**: a value `cur : xs.Cursor` has fields `cur.prefix`, `cur.suffix` and
`cur.property : cur.prefix ++ cur.suffix = xs`. A loop invariant is stated about `cur.prefix`, the elements
already processed. In a step VC the cursor is split open as `xs = pref✝ ++ cur✝ :: suff✝`: the invariant is
assumed for `pref✝` and must be proved for `pref✝ ++ [cur✝]`. Placeholders: `(xs : List Nat) (cur : xs.Cursor)`.

**R3 · `mvcgen [f] invariants · ⇓⟨cur, s⟩ => ⌜I⌝`** changes the **goal list**: a triple about a `for` loop
becomes one VC per branch of the loop body (`step.isTrue`, `step.isFalse`), plus the entry VC (`pre`: `I` with
`cur.prefix = []` and the initial value of the `let mut`) and the exit VC (`post.success`: `I` with
`cur.prefix = xs` implies the postcondition) unless `mvcgen` closes them by itself. In the pattern `⟨cur, s⟩`,
`cur` is the cursor and `s` the current value of the (single) `let mut`; the names are yours. Write the `·`
line right after `mvcgen … invariants`, at the same column or indented further. Placeholders: `(t : Nat) (xs : List Nat)`, the program `sumBig t xs`, invariant
`⌜s ≤ cur.prefix.sum⌝`.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ sumBig t xs ⦃PostCond.noThrow fun r => ⌜r ≤ xs.sum⌝⦄` | `h✝¹ : t < cur✝, h✝ : b✝ ≤ pref✝.sum ⊢ s✝ ≤ (pref✝ ++ [cur✝]).sum`, `h✝¹ : ¬t < cur✝ ⊢ b✝ ≤ (pref✝ ++ [cur✝]).sum`, `⊢ 0 ≤ [].sum` |

Here the `post.success` VC (`s ≤ xs.sum` → `r ≤ xs.sum`) was immediate, so `mvcgen` closed it. The `then`
branch updates the `let mut`, so its goal is about the new value `s✝ : Nat := b✝ + cur✝`; the `else` branch
keeps `b✝`.

**Choosing the invariant.** Take the postcondition, replace the whole list `xs` by `cur.prefix` and the
result `r` by the loop variable. At exit `cur.prefix = xs`, so it gives the postcondition back; at entry it
must hold for `[]` and the initial value. `mvcgen [f] invariants?` prints a suggestion
(`Try this: [apply] invariants · ⇓⟨xs, letMuts⟩ => …`) that shows the syntax, but its body only says "at the
start, or at the end and the postcondition holds", so it is too weak for the step VCs. `[apply]` means
`invariants?` also uses that suggestion, so replace it by `invariants` with your own `·` line.

With the invariant for `maxLoop`, `mvcgen` leaves three VCs:

| VC tag | What it asks |
|---|---|
| `vc1.step.isTrue` | branch `m < x`: the invariant for `pref ++ [x]` with the new value `x` |
| `vc2.step.isFalse` | branch `¬m < x`: the invariant for `pref ++ [x]` with the old value `m` |
| `vc3.pre` | the invariant for `[]` and `0` (`mvcgen` already turned `0 = 0` into `True`) |

### Closing the VCs

Every VC is about membership in `pref✝ ++ [cur✝]` or in `[]`. `grind` (R7) uses R4–R6 by itself; they are
listed so that you can read the VCs and fix a `grind` failure by hand.

**R4 · `List.mem_append`** changes the **goal**: `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. Placeholders:
`{α : Type} (a : α) (s t : List α)`, `(P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a ∈ s ++ t)` | `⊢ P (a ∈ s ∨ a ∈ t)` |

**R5 · `List.mem_singleton`** changes the **goal**: `a ∈ [b] ↔ a = b`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a ∈ [b])` | `⊢ P (a = b)` |

**R6 · `List.mem_nil_iff`** changes the **goal**: `a ∈ [] ↔ False`; this is what the `pre` VC needs.
Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `⊢ P (a ∈ [])` | `⊢ P False` |

**R7 · `grind`** **closes** the goal. It combines linear arithmetic over `Nat` (`+`, `<`, `≤`, numerals),
case splits on `∧`, `∨` and `if`, instantiating `∀` hypotheses at the terms it sees (here: the invariant
`∀ x, x ∈ pref✝ → x ≤ b✝` at each `x ∈ pref✝ ++ [cur✝]`), and rewriting with lemmas tagged for it, R4–R6
among them. Placeholders: `(p : List Nat) (a b c : Nat)`. Write `all_goals grind` to run it on every VC
(TACTIC_STATES, "Structure").

| Before | After |
|---|---|
| `hb : b ≤ c ⊢ ∀ (y : Nat), y ∈ p ++ [c] → y ≤ c` | closed by `grind` |
| `h : a ∈ p ∨ a = c ⊢ a ∈ p ++ [c]` | closed by `grind` |

The first row also uses `h : ∀ y, y ∈ p → y < b`.

**W1 (guide.lean): invariant from the postcondition.** `sumL` sums a list; the triple says every element is at
most the result. Invariant `⌜∀ y ∈ cur.prefix, y ≤ s⌝`. `mvcgen` leaves the step and entry VCs, and
`all_goals grind` closes them:

```lean-goal
⊢ ∀ (y : Nat), y ∈ pref✝ ++ [cur✝] → y ≤ s✝
⊢ ∀ (y : Nat), y ∈ [] → y ≤ 0
```

---

## Part 2 · `maxLoop_run`

Statement: `x ∈ xs → x ≤ (maxLoop xs).run`: a plain inequality about the computed value, no triple. Reuse
Part 1 rather than reasoning about the loop again.

**R8 · `Id.of_wp_run_eq`** changes the **context** (used with `have`). The lemma is
`prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x`. With `x := prog.run`, proved by `rfl`, it turns
"`P` holds after `prog`" into `P prog.run`. Placeholders: `{α : Type} (prog : Id α) (P : α → Prop)`,
`hw` the weakest-precondition fact.

| Before | After `have h := Id.of_wp_run_eq rfl P hw` |
|---|---|
| `⊢ G` | `h : P prog.run ⊢ G` |

**R9 · a triple is the `wp` argument** changes the **context** the same way. `⦃⌜True⌝⦄ prog ⦃Q⦄` is by
definition `⌜True⌝` entails `wp⟦prog⟧ Q`, which is what R8's third argument asks for. Write `_` for `P`:
Lean reads it off the triple's postcondition `⇓ a => ⌜P a⌝`. Placeholders: as R8, with
`ht : ⦃⌜True⌝⦄ prog ⦃⇓ a => ⌜P a⌝⦄`.

| Before | After `have h := Id.of_wp_run_eq rfl _ ht` |
|---|---|
| `⊢ G` | `h : P prog.run ⊢ G` |

**R10 · `h.1`** changes the **context**: from `h : A ∧ B`, `h.1 : A` (`And.left`) and `h.2 : B`. It also works
directly on a term, as in `(Id.of_wp_run_eq rfl _ ht).1`. Placeholders: `(A B : Prop)`.

| Before | After `have hA := h.1` |
|---|---|
| `h : A ∧ B ⊢ G` | `hA : A ⊢ G` |

**R11 · `h x hx`** changes the **context**: `h : ∀ x ∈ xs, Q x` is a function of `x` and a proof of `x ∈ xs`.
Placeholders: `{α : Type} (xs : List α) (Q : α → Prop) (x : α) (hx : x ∈ xs)`.

| Before | After `have hq := h x hx` |
|---|---|
| `hx : x ∈ xs ⊢ G` | `hq : Q x ⊢ G` |

**W2 (guide.lean): term mode.** R9, R10 and R11 chain into one term, with no `by`:
`Id.of_wp_run_eq rfl _ (sumL_bound xs) y hy : y ≤ (sumL xs).run`. Here the postcondition is a single `∀`, so
no `.1` is needed; with a conjunction, project first.

---

## Traps

- Without `invariants`, `mvcgen` on a loop leaves an extra goal `case inv1` of type
  `Invariant xs Nat PostShape.pure` and VCs mentioning `?inv1`. Give the invariant with `invariants` (R3).
- The invariant must mention `cur.prefix`, not `xs`: with `xs` the entry VC asks for `∀ x ∈ xs, x ≤ 0`,
  a bound on elements the loop has not seen yet, which is false for most `xs`.
- The entry VC fixes the initial value: with `let mut m := 0`, an invariant `m ∈ cur.prefix` (without
  `m = 0 ∨ …`) is false at entry, because `0 ∉ []`.
- ⊢ₛ (an assertion holds) is not the goal turnstile ⊢. You never need to prove a ⊢ₛ goal by hand here: the
  triple of Part 1 is that proof (R9).
- `Id.of_wp_run_eq rfl _ spec` proves the whole postcondition of `.run`; the goal of Part 2 is only its first
  conjunct, applied to `x` and `hx` (R10, R11).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| triple → VCs (no loop) | `mvcgen [f]` | R1 |
| triple about a `for` loop → VCs | `mvcgen [f] invariants` then `· ⇓⟨cur, m⟩ => ⌜I cur.prefix m⌝` | R2, R3 |
| find the invariant | postcondition with `xs ↦ cur.prefix`, `r ↦ m` | R3 |
| see the invariant syntax | `mvcgen [f] invariants?` | R3 |
| `a ∈ s ++ t`, `a ∈ [b]`, `a ∈ []` | `List.mem_append`, `List.mem_singleton`, `List.mem_nil_iff` (`grind` knows them) | R4–R6 |
| close all VCs | `all_goals grind` | R7 |
| triple → fact about `.run` | `Id.of_wp_run_eq rfl _ spec` | R8, R9 |
| first conjunct | `h.1` | R10 |
| use `∀ x ∈ xs, Q x` | `h x hx` | R11 |
| see the state | infoview | |
