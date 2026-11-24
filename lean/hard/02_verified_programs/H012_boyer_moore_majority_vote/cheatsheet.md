# H012 · Boyer-Moore majority vote with mvcgen: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `do` notation, `List`, `Nat`, `theorem`, `simp`, `rw`.
**New here:** `Std.Do`, core Lean's library for verifying monadic programs: Hoare triples, the
verification-condition generator `mvcgen`, loop invariants over a `List.Cursor`, composing a proved
spec into a caller, and `grind` as the closer for the resulting arithmetic goals. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`grind`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[BEq α]` is a
  requirement on `α` (a *type class*): `[BEq α]` gives a Boolean test `a == b`, `[LawfulBEq α]` says that
  test agrees with `=`. `Nat` has both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- The `mvcgen` entries (R11–R16) need a real program, so they use small ones from `guide.lean`
  (`twice n` computes `n + n`, `sumL` sums a list, `evens` counts even and odd elements, `quad` calls
  `twice`, `countTwice` calls `twice` and then loops).

## Reading the goals

| You see | It means |
|---|---|
| `Id Nat` | a program that returns a `Nat` and has no effects; `do`, `let mut`, `for` are notation for a pure function |
| `prog.run` | `Id.run prog`: the value the `Id` program computes |
| `List.count a l` | number of elements `x` of `l` with `x == a`. You may type `l.count a` (dot notation fills the list argument); Lean prints `List.count a l` |
| `⦃P⦄ prog ⦃Q⦄` | Hoare triple (`Std.Do.Triple`): if assertion `P` holds before, `Q` holds after `prog` |
| `⌜p⌝` | the proposition `p : Prop` viewed as an assertion (`Id` has no state, so it is just `p`) |
| `⇓ r => ⌜Q r⌝` | postcondition on the returned value `r`; printed `PostCond.noThrow fun r => ⌜Q r⌝` |
| `{ down := p }` | `⌜p⌝` after unfolding (R17) |
| `wp⟦prog⟧ Q` | weakest precondition: the assertion "running `prog` establishes `Q`" |
| ⊢ₛ A (in a goal) | the assertion A holds. Not the same symbol as the goal turnstile ⊢ (R17, R18) |
| `case vc1.step.isTrue` | verification condition 1: one loop step, `then` branch of the body's `if` |
| `case vc4.pre`, `case vc5.post.success` | invariant at loop entry (`prefix = []`); invariant at exit implies the postcondition |
| `xs.Cursor`, `cur.prefix` | a split of `xs` into processed `prefix` and remaining `suffix` (R12) |
| `pref✝`, `cur✝`, `suff✝` | in a step VC: processed part, current element, rest, with `xs = pref✝ ++ cur✝ :: suff✝` |
| `b✝ : Nat × Nat`, `b✝.fst` | the loop state when there are two `let mut`s (R14); `.fst`, `.snd` are `.1`, `.2` |
| `k✝ : Nat := k✝¹ + 1` | a `let` hypothesis: `k✝` is a name for the value `k✝¹ + 1` (the updated `let mut`) |
| `r✝`, `h✝` | inaccessible names made by `mvcgen` (a call's result, a hypothesis); you cannot type them |

---

## Part 1 · `MajInv` (the loop invariant, a milestone `def`)

Statement: `MajInv p c k : Prop`, what is true after the loop has processed the prefix `p` and holds candidate
`c` with counter `k`. No tactics here; this is the design step.

The vote is a pairing argument. Each `k := k - 1` cancels one copy of the candidate against one *different*
element. So after `p`, the `p.length - k` elements that are not "unpaired copies of `c`" form pairs of distinct
values. Consequences you can state as bounds on `List.count y p`:

- a value `y ≠ c` takes at most one slot per pair, so it fills at most half of those `p.length - k` slots;
- `c` itself fills the `k` unpaired slots plus at most half of the paired ones.

Write both as `Nat` inequalities **without division and without `-`** (multiply by 2, move `k` to the other
side); `grind` handles `+`, `≤` and `2 * _` best. The invariant must make all five milestones of Part 2
provable: in particular, `majInv_final` must be able to rule out every `m ≠ c` that is a strict majority.

---

## Part 2 · `majInv_nil`, `majInv_reset`, `majInv_match`, `majInv_cancel`, `majInv_final`

Statements: one lemma per verification condition of `majority_spec` (Part 3): the invariant holds at the start;
each of the three branches of the loop body preserves it; at the end it forces `c = m`. Each proof:
unfold `MajInv` (R8), then `grind` (R9), which uses R1–R7 by itself. `majInv_nil` is a `simp [MajInv]`
(R1, R2).

### Counting and lengths

**R1 · `List.count_nil`** changes the **goal**: `List.count a [] = 0`. Placeholders: `{α : Type} [BEq α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (List.count a [])` | `⊢ P 0` |

**R2 · `List.length_nil`** changes the **goal**: `[].length = 0`. Placeholders: `{α : Type}`.

| Before | After |
|---|---|
| `⊢ P [].length` | `⊢ P 0` |

**R3 · `List.count_append`** changes the **goal**: `List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂`.
Every VC is about `pref✝ ++ [cur✝]`, so this is the lemma that splits off the new element. Placeholders:
`{α : Type} [BEq α] (a : α) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.count a (l₁ ++ l₂))` | `⊢ P (List.count a l₁ + List.count a l₂)` |

**R4 · `List.count_singleton`** changes the **goal**: `List.count a [b] = if (b == a) = true then 1 else 0`.
Placeholders: `{α : Type} [BEq α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (List.count a [b])` | `⊢ P (if (b == a) = true then 1 else 0)` |

**R5 · `beq_iff_eq`** changes the **goal**: `(a == b) = true ↔ a = b`, so the Boolean test of R4 becomes an
equation that the hypotheses `h✝ : cur✝ = cand✝` / `¬cur✝ = cand✝` can decide. Placeholders:
`{α : Type} [BEq α] [LawfulBEq α] (a b : α)`, `(P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((b == a) = true)` | `⊢ P (b = a)` |

**R6 · `List.length_append`** changes the **goal**: `(as ++ bs).length = as.length + bs.length`. Placeholders:
`{α : Type} (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs).length` | `⊢ P (as.length + bs.length)` |

**R7 · `List.length_singleton`** changes the **goal**: `[a].length = 1`. Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `⊢ P [a].length` | `⊢ P 1` |

### Unfolding and closing

**R8 · `unfold D at *`** changes the **goal and the context**: the defined name `D` is replaced by its body in
the goal and in every hypothesis. `grind` does not look inside your definitions, so do this first. Placeholders:
`D` defined by `def D (n : Nat) : Prop := n ≤ 5`, `(n m : Nat)`.

| Before | After |
|---|---|
| `h : D n ⊢ D m` | `h : n ≤ 5 ⊢ m ≤ 5` |

**R9 · `grind`** **closes** the goal. It combines linear arithmetic over `Nat` (`+`, truncated `-`, `*` by a
numeral, `<`, `≤`), instantiating `∀` hypotheses at the terms it sees (`h : ∀ y, y ≠ c → …` with `hx : x ≠ c`),
splitting `if`, and rewriting with library lemmas tagged for it, R1–R7 among them. So
`List.count a (l ++ [b]) = List.count a l` with `hb : b ≠ a` is one `grind`.

**R10 · `grind [l₁, l₂]`** **closes** the goal using, in addition, the named lemmas `lᵢ`: `grind` instantiates a
lemma when terms matching its conclusion appear. Example: `ev_add_two : Ev n → Ev (n + 2)` with `hm : m = n + 2`
proves `Ev m` by `grind [ev_add_two]`. This is how Part 3 feeds the milestones to the VCs.

---

## Part 3 · `majority_spec`

Statement: `⦃⌜True⌝⦄ majority xs ⦃⇓ r => ⌜∀ m, xs.length < 2 * List.count m xs → r = m⌝⦄`: the returned
candidate equals every strict-majority element (if one exists).

**R11 · `mvcgen [f]`** changes the **goal list**: a Hoare triple becomes its verification conditions (VCs), plain
`Prop` goals. `[f]` tells it to unfold `f`. A `let` in the program becomes a `let` hypothesis. Placeholders:
`(n : Nat)`, the program `twice n`.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ twice n ⦃PostCond.noThrow fun r => ⌜r = 2 * n⌝⦄` | `a✝ : Nat := n + n ⊢ a✝ = 2 * n` |

**R12 · `List.Cursor`** is not a step; it is the type of `cur` in `⇓⟨cur, s⟩ => …`. A value `cur : xs.Cursor` has fields `cur.prefix`, `cur.suffix` and
`cur.property : cur.prefix ++ cur.suffix = xs`. A loop invariant is stated about `cur.prefix`, the elements
already processed. In a step VC the cursor is split open as `xs = pref✝ ++ cur✝ :: suff✝`: the invariant is
assumed for `pref✝` and must be proved for `pref✝ ++ [cur✝]`.

**R13 · `mvcgen [f] invariants · ⇓⟨cur, s⟩ => ⌜I⌝`** changes the **goal list**: a triple about a `for` loop becomes
one VC per branch of the loop body (`step`), plus the entry VC (`pre`: `I` with `cur.prefix = []` and the
initial `let mut` value) and the exit VC (`post.success`: `I` with `cur.prefix = xs` implies the
postcondition), unless `mvcgen` closes those by itself. `s` is the current value of the `let mut`.
Write the `·` line under `mvcgen`; `mvcgen [f] invariants?` prints a starting suggestion. Placeholders:
`(xs : List Nat)`, the program `sumL xs`.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ sumL xs ⦃PostCond.noThrow fun r => ⌜r = xs.sum⌝⦄` | `s✝ : Nat := b✝ + cur✝, h✝ : b✝ = pref✝.sum ⊢ s✝ = (pref✝ ++ [cur✝]).sum` |

**R14 · two `let mut`s** change the shape of the invariant: the loop state is a pair, so write
`⇓⟨cur, st⟩ => ⌜… st.1 … st.2 …⌝`, with `st.1` the first-declared `let mut`. In the VCs the state is
`b✝ : Nat × Nat`, and `let` hypotheses give the values: `e✝¹ : Nat := b✝.fst` (old), `e✝ : Nat := e✝¹ + 1`
(updated). An `if` in the body gives one VC per branch,
tagged `isTrue` / `isFalse` (nested `if`: `isFalse.isTrue`, …). Placeholders: `(xs : List Nat)`, the program
`evens xs` (`let mut e` counts evens, `let mut o` odds).

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ evens xs ⦃PostCond.noThrow fun r => ⌜r.fst + r.snd = xs.length⌝⦄` | `h✝¹ : cur✝ % 2 = 0, e✝ : Nat := e✝¹ + 1 ⊢ e✝ + o✝ = (pref✝ ++ [cur✝]).length`, `h✝¹ : ¬cur✝ % 2 = 0, o✝ : Nat := o✝¹ + 1 ⊢ e✝ + o✝ = (pref✝ ++ [cur✝]).length` |

With the invariant `⌜MajInv cur.prefix st.1 st.2⌝`, `majority` produces five VCs, one per milestone:

| VC tag | What it asks | Milestone |
|---|---|---|
| `vc1.step.isTrue` | branch `k = 0`: invariant for `pref ++ [x]` with candidate `x`, counter 1 | `majInv_reset` |
| `vc2.step.isFalse.isTrue` | branch `x = cand`: counter `k + 1` | `majInv_match` |
| `vc3.step.isFalse.isFalse` | branch `x ≠ cand`, `k ≠ 0`: counter `k - 1` | `majInv_cancel` |
| `vc4.pre` | `MajInv [] 0 0` | `majInv_nil` |
| `vc5.post.success` | invariant on all of `xs` → the postcondition | `majInv_final` |

The branch facts arrive as hypotheses (`k✝ = 0`, `¬k✝¹ = 0`, `cur✝ = cand✝`), and the state as `b✝.fst`,
`b✝.snd` with `cand✝ : Nat := b✝.fst`. `grind [milestones]` (R10) matches each VC to its lemma.

**W1 (guide.lean): named invariant + one lemma per VC.** `maxL` (largest element) with
`MaxInv p m := ∀ y, y ∈ p → y ≤ m` and the invariant `⌜MaxInv cur.prefix m⌝` leaves these VCs, closed by
`all_goals grind [maxInv_nil, maxInv_up, maxInv_keep]`:

```lean-goal
⊢ MaxInv (pref✝ ++ [cur✝]) cur✝
⊢ MaxInv (pref✝ ++ [cur✝]) b✝
⊢ MaxInv [] 0
```

---

## Part 4 · `majorityChecked_spec`

Statement: `⦃⌜True⌝⦄ majorityChecked xs ⦃⇓ r => ⌜∀ m, r = some m ↔ xs.length < 2 * List.count m xs⌝⦄`: the
checked vote returns `some m` exactly for the strict-majority element, `none` if there is none.

**R15 · `mvcgen [g, f_spec]`** changes the **goal list and the context**: at the call `let a ← f …` inside `g`,
`mvcgen` uses the proved triple `f_spec` instead of unfolding `f`. The context gains the result `r✝` and its
postcondition `h✝`. Here: use `majority_spec` (Part 3) for the call `let c ← majority xs`. Placeholders:
`(n : Nat)`, `quad n` calling `twice n`, with `twice_spec` from R11.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ quad n ⦃PostCond.noThrow fun r => ⌜r = 4 * n⌝⦄` | `h✝ : r✝ = 2 * n ⊢ r✝ + r✝ = 4 * n` |

**R16 · `invariants | inv1 c _ => ⇓⟨cur, k⟩ => ⌜… c …⌝`** sets the invariant of loop 1 **and names** the
inaccessible variables in its scope, in order: the call's result as `c`, its postcondition as `_`. Needed
because the loop runs after `let c ← …`, and a `·` invariant cannot mention `r✝`. Loops are numbered `inv1`,
`inv2`, … in program order; in `majorityChecked` (with `majority_spec` used, so `majority`'s loop is not
expanded) the counting loop is `inv1`. Placeholders: `(xs : List Nat) (n : Nat)`, `countTwice xs n`.

| Before | After |
|---|---|
| `⊢ ⦃⌜True⌝⦄ countTwice xs n ⦃PostCond.noThrow fun r => ⌜r = List.count (2 * n) xs⌝⦄` | `h✝ : b✝ = List.count r✝ pref✝ ⊢ k✝ = List.count r✝ (pref✝ ++ [cur✝])`, `h✝ : b✝ = List.count r✝ pref✝ ⊢ b✝ = List.count r✝ (pref✝ ++ [cur✝])`, `⊢ r✝ = List.count (2 * n) xs` |

For `majorityChecked` the counting invariant is `n = List.count c cur.prefix`. Besides the two step VCs, the
final `if xs.length < 2 * n` gives two `post.success` VCs (`isTrue`: goal about `some c`, `isFalse`: about
`none`). Both have `majority_spec`'s postcondition `∀ m, … → c = m` in context; `grind` (R9) instantiates it.

---

## Part 5 · `majority_run`

Statement: given `hm : xs.length < 2 * List.count m xs`, `(majority xs).run = m`: a plain equation about the
value, no triple.

**R17 · `Id.of_wp_run_eq`** changes the **goal**. The lemma is
`prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x`. With `x := prog.run` (proved by `rfl`),
`apply Id.of_wp_run_eq rfl P` turns a goal `P prog.run` into a weakest-precondition goal. Placeholders:
`{α : Type} (prog : Id α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P prog.run` | `⊢ ⊢ₛ wp⟦prog⟧ (PostCond.noThrow fun a => { down := P a })` |

**R18 · a triple proves a `wp` goal** **closes** the goal: `⦃⌜True⌝⦄ prog ⦃Q⦄` is by definition
`⌜True⌝ ⊢ₛ wp⟦prog⟧ Q`, so `exact spec` works, also on the `{ down := P a }` form R17 leaves (it is
`⌜P a⌝` unfolded). Placeholders: `{α : Type} (prog : Id α) (P : α → Prop)`,
`h : ⦃⌜True⌝⦄ prog ⦃⇓ a => ⌜P a⌝⦄`.

| Before | After |
|---|---|
| `⊢ ⊢ₛ wp⟦prog⟧ (PostCond.noThrow fun a => ⌜P a⌝)` | closed by `exact h` |

**W2 (guide.lean): term mode.** `Id.of_wp_run_eq rfl P spec` is itself a proof of `P prog.run`. When `P r` is
`∀ k, … → r = k`, apply the result to further arguments: `Id.of_wp_run_eq rfl (fun r => ∀ k, xs.sum = k → r = k)
(sumL_spec xs) k hk : (sumL xs).run = k`. Its spec's exit VC:

```lean-goal
⊢ ∀ (k : Nat), xs.sum = k → r✝ = k
```

---

## Traps

- `List.count m xs` is the number of occurrences of `m` in `xs`. "Strict majority" is
  `xs.length < 2 * List.count m xs`: no division, so no rounding.
- `k - 1` on `Nat` is truncated at 0. In the `cancel` branch you have `¬k = 0`, so it is a real decrement;
  `grind` uses that hypothesis.
- `grind` does not unfold `MajInv` by itself: `unfold MajInv at *` first (R8). Without it `grind` treats
  `MajInv p c k` as an opaque proposition and fails.
- Without `invariants`, `mvcgen` on a loop leaves an extra goal `case inv1` of type `Invariant xs Nat PostShape.pure`
  and VCs mentioning `?inv1`. Give the invariant with `invariants` (R13).
- The loop state order is the `let mut` order: `st.1` is `cand`, `st.2` is `k`.
- In `majorityChecked` the candidate is the inaccessible `r✝`: a `·` invariant cannot name it; use
  `| inv1 c _ =>` (R16). List `majority_spec` in `mvcgen [...]`, or nothing is known about `c`.
- ⊢ₛ (an assertion holds) is not the goal turnstile ⊢: `⊢ ⊢ₛ wp⟦…⟧ …` is one goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| count / length of `[]`, `l ++ l'`, `[a]` | `List.count_nil`, `List.count_append`, `List.count_singleton`, `List.length_append`, `List.length_singleton` (`grind` knows them) | R1–R7 |
| `(b == a) = true` → `b = a` | `beq_iff_eq` | R5 |
| see inside your predicate | `unfold MajInv at *` | R8 |
| `Nat` arithmetic + `∀` hypotheses + `if` | `grind` | R9 |
| … using your lemmas | `grind [l₁, l₂]` | R10 |
| triple → VCs | `mvcgen [f]` | R11 |
| loop invariant (one `let mut`) | `mvcgen [f] invariants` then `· ⇓⟨cur, s⟩ => ⌜I cur.prefix s⌝` | R12, R13 |
| two `let mut`s | `⇓⟨cur, st⟩ => ⌜… st.1 … st.2 …⌝` | R14 |
| all VCs at once | `all_goals grind [...]` | R10 |
| use a proved spec at a call | `mvcgen [g, f_spec]` | R15 |
| invariant that names a call's result | `invariants` then `\| inv1 c _ => ⇓⟨cur, n⟩ => ⌜… c …⌝` | R16 |
| triple → equation on `.run` | `Id.of_wp_run_eq rfl P spec args…` | R17, R18, W2 |
| see the state | infoview | |
