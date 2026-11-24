# H011 · Dutch national flag: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `apply`, `rw`, `simp`, `omega`,
`termination_by`, anonymous constructors `⟨_, _⟩`). No Mathlib: this is a core-Lean problem.
**New here:** core `Array` (indexing with a bound proof, `swap`, `Perm`), `fun_induction` on a
recursive loop, a loop invariant carried through the induction, and index-case analysis with `split`
and `omega`.

The guide never touches `dnfLoop`. It works on `sweep`, a two-way partition with the same shape: an
`if h : guard` around a `match a[i]` with three constructors, one branch that swaps, and an `else`
exit. Its invariant is "`[0, lo)` is `neg`".

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type (here: the colour type).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `if h : c then x else y` | a dependent `if`: in the `then` branch `h : c` is in scope. In `dnfLoop`, `h` is the bound proof that makes `a[mid]` legal |
| `match a[mid] with` and its branches `.red`, `.white`, `.blue` | case on the colour of cell `mid`; `fun_induction` turns each branch into a goal with the fact `hc : a[mid] = Color.red` (etc.) |
| `a[i]` | cell `i` of array `a`. It silently carries a proof of `i < a.size`; without one in scope Lean reports "failed to prove index is valid" |
| `a.size` | the length of `a` |
| `a.swap i j hi hj` | `a` with cells `i` and `j` exchanged; `hi : i < a.size`, `hj : j < a.size` are the bounds |
| `⋯` | a proof term Lean does not print (here: the bounds of `swap`) |
| `xs.Perm ys` | `Array.Perm`: `ys` is a rearrangement of `xs` (same elements, same multiplicities) |
| `∀ (i : Nat) (h : i < a.size), i < lo → a[i] = Color.red` | for every in-bounds index below `lo` the cell is red; the named binder `h` is the bound `a[i]` uses |
| `h_1 : i < …` | Lean renamed a binder `h` to `h_1` because an `h` is already in the context |
| `Color.red` | the constructor `.red` printed with its type name |
| `hi - 1` | truncated `Nat` subtraction: `0 - 1 = 0` |
| `¬(lo ≤ mid ∧ mid < hi ∧ hi ≤ a.size)` | the loop guard is false: the exit case |
| `a✝`, `h✝`, `x✝`, `ih1✝` | inaccessible names: Lean made them, you cannot type them; name them with `case case1 a lo i h hc ih =>` (R1). `omega` still uses them |
| `h✝¹`, `h✝` | two inaccessible hypotheses of the same name; `h✝` is the newest (after two `split`s: `h✝¹ : ¬i = lo`, `h✝ : i = mid`) |
| `case case1` … `case case4` | the goals `fun_induction` makes: red, white, blue branch, exit |
| `case refine_1` | the goal for the first `?_` of a `refine` |
| `case isTrue`, `case isFalse` | the two goals from `split` on an `if` |
| `case pos`, `case neg` | the two goals from `by_cases` |
| `case case1.refine_1.isFalse.isTrue` | nested case names joined by dots: `case1`, its first `?_`, the `else` of the first `split`, the `then` of the second |

---

## Part 1 · `dnf_perm` (milestone `loop_perm`)

Statement: `(dnf a).Perm a`: the output is a rearrangement of the input. Prove the milestone
`loop_perm : (dnfLoop a lo mid hi).Perm a` for ALL `lo mid hi` first; `dnf_perm` is one instance.

**R1 · `fun_induction f x y z`** changes the **goal list**. It does induction following the recursion
of `f`: one goal per branch of `f`'s body, with the branch's facts and an induction hypothesis (IH) for
each recursive call. The goal's `f x y z` is replaced by the branch's recursive call (or result).
For `sweep a lo i` it produces `case1` (`neg`, swap), `case2` (`zero`), `case3` (`pos`), `case4` (exit).
Placeholders: the function `sweep` and its arguments `(a : Array Sign) (lo i : Nat)`.

| Before | After |
|---|---|
| `⊢ (sweep a lo i).size = a.size` | case1: `x✝ : a✝[i✝] = Sign.neg, ih1✝ : (sweep (a✝.swap lo✝ i✝ ⋯ ⋯) (lo✝ + 1) (i✝ + 1)).size = (a✝.swap lo✝ i✝ ⋯ ⋯).size ⊢ (sweep (a✝.swap lo✝ i✝ ⋯ ⋯) (lo✝ + 1) (i✝ + 1)).size = a✝.size` |
| | case2: `x✝ : a✝[i✝] = Sign.zero, ih1✝ : (sweep a✝ lo✝ (i✝ + 1)).size = a✝.size ⊢ (sweep a✝ lo✝ (i✝ + 1)).size = a✝.size` |
| | case4: `h✝ : ¬(lo✝ ≤ i✝ ∧ i✝ < a✝.size) ⊢ a✝.size = a✝.size` |

Each case has the guard `h✝ : lo✝ ≤ i✝ ∧ i✝ < a✝.size` too. Name everything in order with
`case case1 a lo i h hc ih => …` (case4 has no `hc`, `ih`), or
`fun_induction f x y z with | case1 a lo i h hc ih => … | case2 … `.

**R2 · `Array.swap_perm`** **closes** the goal. Statement:
`Array.swap_perm (h₁ : i < xs.size) (h₂ : j < xs.size) : (xs.swap i j h₁ h₂).Perm xs`.
Write `Array.swap_perm _ _`; Lean fills the bounds from the goal.
Placeholders: `{α : Type} (xs : Array α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size)`.

| Before | After |
|---|---|
| `⊢ (xs.swap i j hi hj).Perm xs` | closed |

**R3 · `Array.Perm.trans`** changes the **goal**. Statement: `xs.Perm ys → ys.Perm zs → xs.Perm zs`.
`apply Array.Perm.trans ih` leaves the second half; `ih.trans h` (dot notation) gives the whole proof
at once. Placeholders: `{α : Type} (xs ys zs : Array α) (ih : xs.Perm ys)`.

| Before | After |
|---|---|
| `⊢ xs.Perm zs` | `⊢ ys.Perm zs` |

**R4 · `Array.Perm.refl`** **closes** the goal. Statement: `Array.Perm.refl xs : xs.Perm xs`. Write
`.refl xs` when Lean knows the expected type. Placeholders: `{α : Type} (xs : Array α)`.

| Before | After |
|---|---|
| `⊢ xs.Perm xs` | closed |

**R5 · `unfold d`** changes the **goal**: the defined name `d` is replaced by its body. You rarely need
it before `exact`: Lean unfolds definitions itself when it checks a term against a goal, so a milestone
about `sweep a 0 0` already proves a goal about `start a`. Placeholders: `start` defined by
`def start (a : Array Sign) : Array Sign := sweep a 0 0`.

| Before | After |
|---|---|
| `⊢ P (start a)` | `⊢ P (sweep a 0 0)` |

**W1** (in the guide) chains R1, R3 + R2 in the swap branch, and R4 at the exit to prove
`(sweep a lo i).Perm a`.

---

## Part 2 · `dnf_sorted` (milestones `FlagInv`, `loop_sorted`)

Statement: `SortedByColor (dnf a)`: for all `i ≤ j < size`, `rank a[i] ≤ rank a[j]`. The loop
state is `[0, lo)` red, `[lo, mid)` white, `[mid, hi)` unread, `[hi, size)` blue; `FlagInv a lo mid hi`
says exactly this plus the bounds `lo ≤ mid ≤ hi ≤ a.size`. Prove `loop_sorted`
(`FlagInv a lo mid hi → SortedByColor (dnfLoop a lo mid hi)`) first, then apply it at `0 0 a.size`.

### Induction with the invariant in the context

**R6 · `fun_induction` with a hypothesis about the arguments** changes the **goal list** as R1 does,
and each IH gets that hypothesis as a **premise** (instantiated at the new arguments). Using the IH
then means proving the hypothesis for the next loop state: invariant preservation. The hypothesis
itself stays named in each case. Placeholders: `(hlo : lo ≤ i)` playing the role of `hinv`.

| Before | After |
|---|---|
| `hlo : lo ≤ i ⊢ (sweep a lo i).size = a.size` | case1: `ih1✝ : lo✝ + 1 ≤ i✝ + 1 → (sweep (a✝.swap lo✝ i✝ ⋯ ⋯) (lo✝ + 1) (i✝ + 1)).size = (a✝.swap lo✝ i✝ ⋯ ⋯).size, hlo : lo✝ ≤ i✝ ⊢ (sweep (a✝.swap lo✝ i✝ ⋯ ⋯) (lo✝ + 1) (i✝ + 1)).size = a✝.size` |
| | case2: `ih1✝ : lo✝ ≤ i✝ + 1 → (sweep a✝ lo✝ (i✝ + 1)).size = a✝.size, hlo : lo✝ ≤ i✝ ⊢ (sweep a✝ lo✝ (i✝ + 1)).size = a✝.size` |
| | case4: `hlo : lo✝ ≤ i✝ ⊢ a✝.size = a✝.size` |

**R7 · `obtain ⟨h1, h2, h3⟩ := h`** changes the **context**: a conjunction hypothesis is replaced by its
parts. `∧` nests to the right, so one pattern of six names splits a six-part `FlagInv`; `obtain` looks
through the `def`. Placeholders: `(A B C : Prop) (h : A ∧ B ∧ C)`.

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ⊢ G` | `h1 : A, h2 : B, h3 : C ⊢ G` |

**R8 · `apply ih`** changes the **goal**: with `ih : I → Q` and goal `Q`, the goal becomes `I`.
In `loop_sorted` this turns "sorted after the loop" into "the invariant holds at the next state".
Placeholders: `(I Q : Prop) (ih : I → Q)`.

| Before | After |
|---|---|
| `ih : I → Q ⊢ Q` | `ih : I → Q ⊢ I` |

**R9 · `refine ⟨by omega, ?_, ?_⟩`** changes the **goal list**: the goal is a conjunction (or a `def`
whose body is one, such as `FlagInv`); every `by tac` part is proved on the spot and every `?_`
becomes a goal. Use it to dispatch the arithmetic parts of the invariant at once.
Placeholders: `(lo i : Nat) (A B : Prop) (h : lo < i)`.

| Before | After |
|---|---|
| `h : lo < i ⊢ lo ≤ i ∧ A ∧ B` | `⊢ A`, `⊢ B` |

**R10 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int` (`+`, `-`, numerals, `<`,
`≤`, `=`, `∧`, `∨`, `¬`) using the context's hypotheses of that kind. It knows `Nat` subtraction is
truncated. If those hypotheses are contradictory it closes **any** goal, `a[lo] = Color.red` included:
this is how an impossible index case is killed. Placeholders: `(lo mid hi : Nat)`.

| Before | After |
|---|---|
| `h1 : lo ≤ mid, h2 : mid < hi ⊢ lo ≤ hi - 1` | closed |
| `h1 : i < lo + 1, h2 : ¬i = lo, h3 : lo ≤ i ⊢ G` | closed |

**R11 · `Array.size_swap`** changes the **goal**. Statement: `(xs.swap i j hi hj).size = xs.size`. `simp`
uses it by itself, so `by simp; omega` proves a bound such as `hi ≤ (a.swap lo mid ⋯ ⋯).size`.
Placeholders: `{α : Type} (xs : Array α) (i j n : Nat) (hi : i < xs.size) (hj : j < xs.size)`.

| Before | After |
|---|---|
| `⊢ n ≤ (xs.swap i j hi hj).size` | `⊢ n ≤ xs.size` |

### One region of the invariant after a swap

**R12 · `intro k hk hlt`** changes the **goal and the context**: the `∀` binders and the premise move
into the context. The binder `hk` is the bound that makes `xs[k]` legal. Also works on a goal
`SortedByColor b` (a `def` whose body is a `∀`). Placeholders: `{α : Type} (xs : Array α) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ ∀ (k : Nat) (hk : k < xs.size), k < n → P xs[k]` | `k : Nat, hk : k < xs.size, hlt : k < n ⊢ P xs[k]` |

**R13 · `rw [Array.getElem_swap]`** changes the **goal**: a cell of a swapped array becomes a nested `if`.
Statement: `(xs.swap i j hi hj)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k]`.
Placeholders: `{α : Type} (xs : Array α) (i j k : Nat)` with bounds `hi hj` and
`hk : k < (xs.swap i j hi hj).size`.

| Before | After |
|---|---|
| `⊢ P (xs.swap i j hi hj)[k]` | `⊢ P (if k = i then xs[j] else if k = j then xs[i] else xs[k])` |

**R14 · `split`** changes the **goal list**: the first `if c then x else y` in the goal gives one goal
with `c` and the `then` branch, one with `¬c` and the `else` branch. After R13 you `split` twice:
three cells, `k = i`, `k = j`, neither. `next h => …` names the new hypothesis.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (x y : α)` (`[Decidable c]`: `c` can be tested, as
`k = i` on `Nat` can).

| Before | After |
|---|---|
| `⊢ P (if c then x else y)` | `h✝ : c ⊢ P x`, `h✝ : ¬c ⊢ P y` |

**R15 · `simpa using hk`** **closes** the goal: it simplifies `hk` and the goal with the same `simp`
lemmas and closes the goal with the result. Here R11 turns a bound on the swapped array into one on the
original, which is what the old invariant's `∀ i (h : i < a.size)` needs.
Placeholders: `{α : Type} (xs : Array α) (i j k : Nat) (hk : k < (xs.swap i j hi hj).size)`.

| Before | After |
|---|---|
| `hk : k < (xs.swap i j hi hj).size ⊢ k < xs.size` | closed |

**W2** (in the guide) is one full preservation step on `sweep`: after a swap at `lo`, the prefix
`[0, lo + 1)` is still `neg`. It chains R12, R13, R14 twice, R10 for the impossible cell, and R15:

```lean-goal
⊢ ∀ (k : Nat) (hk : k < (a.swap lo i ⋯ hi).size), k < lo + 1 → (a.swap lo i ⋯ hi)[k] = Sign.neg
⊢ (a.swap lo i ⋯ hi)[k] = Sign.neg
⊢ (if k = lo then a[i] else if k = i then a[lo] else a[k]) = Sign.neg
⊢ a[i] = Sign.neg
⊢ (if k = i then a[lo] else a[k]) = Sign.neg
```

### The non-swap branch and moving indices

**R16 · `by_cases h : p`** changes the **goal list**: one goal with `h : p`, one with `h : ¬p`. Use it
for "is `i` the cell just added to the region (`i = mid`)?" and to split the exit case by regions.
Placeholders: `(p G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : p ⊢ G`, `h : ¬p ⊢ G` |

**R17 · `subst h`** changes the **context and the goal**: with `h : i = m` and `m` a variable, `m` is
replaced by `i` everywhere and `h` disappears (if only the left side is a variable, that one is
replaced). Placeholders: `(i m : Nat) (h : i = m)`.

| Before | After |
|---|---|
| `h : i = m, hp : P i ⊢ P m` | `hp : P i ⊢ P i` |

**R18 · `simp only [e]`** changes the **goal**: it rewrites an array index, `xs[n - 1]` → `xs[m]`, with
`e : n - 1 = m`. `rw [e]` fails on this goal with "motive is not type correct", because the hidden bound
proof inside `xs[n - 1]` mentions `n - 1`; `simp only` rewrites index and proof together.
Placeholders: `{α : Type} (xs : Array α) (n m : Nat) (e : n - 1 = m)`.

| Before | After |
|---|---|
| `e : n - 1 = m ⊢ P xs[n - 1]` | `⊢ P xs[m]` |

### Closing the exit case

**R19 · `rw [hr k hk hlt]`** changes the **goal**: a `∀`-hypothesis applied to its arguments is an
equation `xs[k] = c` you can rewrite with. Placeholders: `{α : Type} (xs : Array α) (n k : Nat) (c : α)`,
`hr : ∀ (k : Nat) (hk : k < xs.size), k < n → xs[k] = c`.

| Before | After |
|---|---|
| `hk : k < xs.size, hlt : k < n ⊢ P xs[k]` | `⊢ P c` |

**R20 · `simp only [val]`** changes the **goal**: a function defined by pattern matching, applied to a
constructor, becomes its value. `simp [val]` goes on and closes `0 ≤ _` (`Nat.zero_le`) and numeral
comparisons such as `1 ≤ 2`. Placeholders: `val : Sign → Nat` defined by `| .neg => 0 | .zero => 1 | .pos => 2`.

| Before | After |
|---|---|
| `⊢ P (val Sign.neg)` | `⊢ P 0` |

**R21 · `Nat.le_refl`** **closes** `n ≤ n`. Statement: `Nat.le_refl (n : Nat) : n ≤ n`. `rw` does not
close a `≤` goal by itself, so after rewriting both sides to the same colour write
`exact Nat.le_refl _`. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ n ≤ n` | closed |

**R22 · `absurd h hn`** **closes** any goal. Statement: `absurd : a → ¬a → b`. In term mode,
`fun k _ h => absurd h (by omega)` proves `∀ k _, k < 0 → …`: the regions of the initial invariant at
`lo = mid = 0`, `hi = a.size` are empty, so their premises are impossible. Placeholders:
`{a : Prop} {b : Sort u} (h : a) (hn : ¬a)`; in the guide `a` is `k < 0` and `hn` is `by omega`
(`Sort u`: any type or proposition, so `b` can be the goal `G`).

| Before | After `exact absurd h (by omega)` |
|---|---|
| `h : k < 0 ⊢ G` | closed |

**W3** (in the guide): at the exit, the negated guard together with the invariant's bounds pins the
index, by R10:

```lean-goal
⊢ i = a.size
```

---

## Traps

- `a[i]` needs `i < a.size` in scope. When you state a fact about `a[i]` (in a `have`, or in an
  invariant), bind the bound: `∀ i (h : i < a.size), …`. After a swap the bound you hold is
  `i < (a.swap …).size`; turn it into `i < a.size` with `by simpa using hk` (R15).
- `rw` cannot change an array index (R18): use `simp only [e]`, or `subst` (R17) when one side is a
  variable.
- `hi - 1` is truncated subtraction. Under `mid < hi` it is the real predecessor, and `omega` uses
  that; without such a fact it is not.
- The invariant must be in the context BEFORE `fun_induction` (R6). If you `intro` it afterwards, the
  IH says nothing about it and cannot be applied to the next state.
- Prove `loop_sorted` for arbitrary `lo mid hi`; `dnf_sorted` is the instance `0 0 a.size`.
  Induction directly on `dnf a` has no IH to use.
- The red case's white region `[lo + 1, mid + 1)`: its new last cell `mid` holds the old `a[lo]`, which
  is white only when `lo < mid`; when `lo = mid` the cell `mid` lies outside that region. Let `omega`
  settle which.
- `t1 ; t2` runs `t2` on the first goal only. After `split` or `by_cases`, use `·` bullets or `next`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction over a recursive loop | `fun_induction f x y z` | R1 |
| name the cases | `case case1 a lo mid hi h hc ih => …` | R1 |
| a swap is a permutation | `Array.swap_perm _ _` | R2 |
| chain permutations | `ih.trans h` | R3 |
| `xs.Perm xs` | `.refl xs` | R4 |
| see the body of a `def` | `unfold d` | R5 |
| IH with the invariant as premise | have `hinv` in context, then `fun_induction` | R6 |
| split the invariant | `obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv` | R7 |
| reduce to the invariant at the next state | `apply ih` | R8 |
| prove the invariant, arithmetic parts inline | `refine ⟨by omega, …, ?_, ?_⟩` | R9 |
| arithmetic, impossible index cases | `omega` | R10 |
| size of a swapped array | `simp` (uses `Array.size_swap`) | R11 |
| enter a region statement | `intro i hk hlt` | R12 |
| cell of a swapped array | `rw [Array.getElem_swap]` | R13 |
| case on the `if`s | `split` (twice) | R14 |
| bound on swap → bound on original | `by simpa using hk` | R15 |
| is it the new cell? | `by_cases h : i = mid` | R16 |
| replace a variable by its value | `subst h` | R17 |
| change an array index | `simp only [e]` | R18 |
| use a region fact | `rw [hr i hi hlt]` | R19 |
| evaluate `rank` on colours | `simp [rank]` | R20 |
| `n ≤ n` | `exact Nat.le_refl _` | R21 |
| an impossible premise in term mode | `fun i _ h => absurd h (by omega)` | R22 |
| see the state | infoview | |
