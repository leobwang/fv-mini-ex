# H018 · Kadane's maximum segment sum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `List`, pairs, `intro`, `exact`, `rfl`, `rw`,
`simp`, `omega`, `cases`, `induction`, `<;>`, `·`. **New here:** core Lean only (no Mathlib): the list
relations `<:+:` (segment) and `<:+` (suffix) and their lemmas for `l ++ [a]`; `List.sum` and `List.foldl`
lemmas; loop invariants for a left fold, proved with `induction … generalizing`; `rcases` patterns with
`rfl`; `by_cases`; `simpa using`.

The problem in one paragraph. `kadane xs` runs `kadaneStep` over `xs` from the left, starting from the
state `(0, 0)`, and returns the first component. A state `(best, cur)` after reading a prefix `p` should
satisfy the invariant `Inv p (best, cur)`: `best` is the maximum sum of a segment of `p` and `cur` the
maximum sum of a suffix of `p`, each an upper bound that some segment / suffix attains (the empty list
counts, so both are `≥ 0`). The proof is the standard loop-invariant argument: the invariant holds at the
start (`inv_nil`), one step preserves it (`inv_step`), so the whole fold does (`inv_foldl`), and the two
theorems are two of its four parts at `p = xs`. The only real thinking is in `inv_step`: the new
suffixes of `p ++ [x]` are `[]` and `t ++ [x]` for old suffixes `t` (R6), and a segment of `p ++ [x]`
is either a suffix of `p ++ [x]` or a segment of `p` (R14).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G` is a goal the step does not touch. A hypothesis `h` in an example is there
  only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `Int` is `ℤ`, `Nat` is `ℕ`.
- A hypothesis that itself contains `, ` (as in `∃ t, …` or `∀ (p : …), …`) is written next to the table
  instead of inside a `⊢` cell.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ys <:+: xs` | `List.IsInfix ys xs`: `∃ s t, s ++ ys ++ t = xs`, `ys` is a contiguous segment of `xs` |
| `ys <:+ xs` | `List.IsSuffix ys xs`: `∃ t, t ++ ys = xs`, `ys` is a suffix (a segment that ends at the end) |
| `ys <:+ p ++ [x]` | `ys <:+ (p ++ [x])`: `++` binds tighter than `<:+` and `<:+:` |
| `ys.sum`, `[].sum` | `List.sum ys`, the sum of the entries; `[].sum` is `0` (R4) |
| `List.foldl f s l`, `l.foldl f s` | the same thing: start with `s`, then `s := f s x` for each `x` of `l`, left to right |
| `Int × Int`, `(a, b)` | the type of pairs of integers, and the pair with components `a`, `b` |
| `st.fst`, `st.snd` | `st.1`, `st.2`, the components of a pair `st : Int × Int` |
| `(0, 0).fst` | the first component of the pair `(0, 0)`, i.e. `0`; `simp` and `omega` reduce it |
| `max a b` | the larger of `a` and `b`; `omega` understands it (R10) |
| `p ++ x :: l` | `p ++ (x :: l)`: `::` binds tighter than `++`. `simp` writes `p ++ [x] ++ l` this way (R19) |
| `kadaneStep st x` | stays folded until you `simp only [kadaneStep]` (R13) |
| `Inv p st` | your invariant; `obtain`/`refine ⟨…⟩` see through it (R1, R5), `simp` and `omega` do not |
| `fun x x_1 => x_1` | a `fun _ x => x`, printed with generated names |
| `¬st.snd + x ≤ 0` | `¬(st.snd + x ≤ 0)`: `¬` applies to the whole comparison |
| `case refine_1`, `case refine_2` | the goals left by the `?_` holes of a `refine`, in order |
| `case inl`, `case inr` | the left / right side of an `∨` after `rcases` |
| `case pos`, `case neg` | the `c` / `¬c` goal after `by_cases` |
| `case nil`, `case cons` | goal tags made by `induction` on a list |

---

## Part 1 · `inv_nil` (MILESTONE)

Statement: `Inv [] (0, 0)`. Four parts: every segment and every suffix of `[]` has sum `≤ 0`, and some
segment and some suffix of `[]` have sum `= 0`. The witness for both `∃` is `[]`. In each bound, after
`intro ys h`, R3 and R4 leave the goal `0 ≤ (0, 0).fst`, which `omega` (R10) or `simp` closes.

**R1 · `refine ⟨?_, ⟨w, ?_, rfl⟩⟩`** changes the **goal list**: a goal that is a *defined* `∧`/`∃` becomes
only the parts you leave as `?_`. The anonymous constructor looks through the definition (in the guide,
`Both A Q y := A ∧ ∃ z, Q z ∧ z = y`). `w` is the `∃` witness; `rfl` proves `w = y` when both sides are the
same term (for `inv_nil`, `[].sum = 0` holds by `rfl`). Placeholders:
`{α : Type} (A : Prop) (Q : α → Prop) (y : α)`.

| Before | After |
|---|---|
| `⊢ Both A Q y` | `⊢ A`, `⊢ Q y` |

**R2 · `List.nil_infix`, `List.nil_suffix`** **close** `[] <:+: l` and `[] <:+ l`. Statements:
`List.nil_infix : [] <:+: l`, `List.nil_suffix : [] <:+ l` (the list `l` is implicit). Use them as the
membership proof inside a witness, `⟨[], List.nil_infix, rfl⟩`. Placeholders: `{α : Type} (l : List α)`.

| Before | After `refine ⟨List.nil_infix, ?_⟩` |
|---|---|
| `⊢ [] <:+: l ∧ [] <:+ l` | `⊢ [] <:+ l` |

**R3 · `rw [List.eq_nil_of_infix_nil h]`** changes the **goal**. Statement:
`List.eq_nil_of_infix_nil : l <:+: [] → l = []`, so from `h : l <:+: []` it rewrites `l` to `[]`.
`List.eq_nil_of_suffix_nil : l <:+ [] → l = []` is the suffix version. `simp [List.eq_nil_of_infix_nil h]`
does the rewrite and R4 in one go. Placeholders: `{α : Type} (l : List α) (h : l <:+: [])`.

| Before | After |
|---|---|
| `h : l <:+: [] ⊢ P l` | `⊢ P []` |

**R4 · `List.sum_nil`** changes the **goal**. Statement: `([] : List α).sum = 0`. `simp` applies it by
itself. Placeholders: the goal in `Int`.

| Before | After |
|---|---|
| `⊢ P [].sum` | `⊢ P 0` |

---

## Part 2 · `inv_step` (MILESTONE)

Statement: `Inv p st → Inv (p ++ [x]) (kadaneStep st x)`. With `cur := max 0 (st.2 + x)`, the new state is
`(max st.1 cur, cur)`. Prove the two suffix parts first (as `have`s about `max 0 (st.2 + x)`), then the two
segment parts, which reuse them.

**R5 · `obtain ⟨h1, h2, ⟨y, hy, hs⟩⟩ := h`** changes the **context**: `h` (here
`h : A ∧ B ∧ ∃ y, Q y ∧ R y`, or a definition such as `Inv` that unfolds to one) is replaced by its pieces.
Each `⟨y, hy, hs⟩` opens one `∃ y, _ ∧ _`. For `Inv` the pattern has four parts, the last two of them
`⟨y, hy, hs⟩`-shaped. Placeholders: `{α : Type} (A B : Prop) (Q R : α → Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : A, h2 : B, y : α, hy : Q y, hs : R y ⊢ G` |

**R6 · `List.suffix_concat_iff`** changes the **context** (with `have h' := List.suffix_concat_iff.mp h`).
Statement: `l₁ <:+ l₂ ++ [a] ↔ l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂`: a suffix of `l₂ ++ [a]` is empty or
an old suffix `t` followed by `a`. `.mp` is the `→` direction, `.mpr` the `←` direction (R12).
Placeholders: `{α : Type} (l₁ l₂ : List α) (a : α)`. After the step the context has
`h' : l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂`.

| Before | After |
|---|---|
| `h : l₁ <:+ l₂ ++ [a] ⊢ G` | `h : l₁ <:+ l₂ ++ [a] ⊢ G`, plus `h'` |

**R7 · `rcases h with rfl | ⟨t, rfl, ht⟩`** changes the **goal list and the context**: one goal per side of
the `∨`. A `rfl` in the pattern uses the equation `l = …` and replaces `l` everywhere, so `l` and `h` leave
the context. Combine with R6 as `rcases List.suffix_concat_iff.mp hys with rfl | ⟨t, rfl, ht⟩`.
Placeholders: `{α : Type} (l : List α) (a : α) (Q : List α → Prop)`, with
`h : l = [] ∨ ∃ t, l = t ++ [a] ∧ Q t`.

| Before | After |
|---|---|
| `⊢ P l` | `⊢ P []`, `t : List α, ht : Q t ⊢ P (t ++ [a])` |

**R8 · `List.sum_append`** changes the **goal**. Statement: `(l₁ ++ l₂).sum = l₁.sum + l₂.sum`.
Placeholders: `(l₁ l₂ : List Int)` (also `Nat`).

| Before | After |
|---|---|
| `⊢ P (l₁ ++ l₂).sum` | `⊢ P (l₁.sum + l₂.sum)` |

**R9 · `List.sum_cons`** changes the **goal**. Statement: `(a :: l).sum = a + l.sum`. `[x]` is `x :: []`, so
`simp` (or `simp [List.sum_append]`) turns `(t ++ [x]).sum` into `t.sum + x` with R8, R9, R4 and
`Int.add_zero`. Placeholders: `(a : Int) (l : List Int)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).sum` | `⊢ P (a + l.sum)` |

**R10 · `omega`** **closes** a goal of linear arithmetic over `Int`/`Nat`, using the hypotheses in the
context; it splits `max a b` and `min a b` into cases by itself. It sees `t.sum`, `st.snd` as unknown
numbers, so first put the facts it needs in the context (`have := hc t ht`). It does not unfold
`kadaneStep` (R13). Placeholders: `(a b c : Int)`.

| Before | After |
|---|---|
| `h : a ≤ c, h' : b ≤ c ⊢ max a b ≤ c` | ∅ |

**R11 · `by_cases h0 : c`** changes the **goal list**: the same goal twice, once with `h0 : c` and once with
`h0 : ¬c`. For the attainment part, case on `st.2 + x ≤ 0`: then the new `cur` is `0` (witness `[]`) or
`st.2 + x` (witness: the old attaining suffix plus `x`). Placeholders: `(c : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h0 : c ⊢ G`, `h0 : ¬c ⊢ G` |

**R12 · `List.suffix_concat_iff.mpr (.inr ⟨t, rfl, ?_⟩)`** changes the **goal**: to show `t ++ [a]` is a
suffix of `l ++ [a]`, show `t` is a suffix of `l`. `.mpr` is R6 right to left, `.inr` picks the right side
of the `∨` (Lean reads it as `Or.inr`), `rfl` proves `t ++ [a] = t ++ [a]`. As a term:
`List.suffix_concat_iff.mpr (.inr ⟨t, rfl, ht⟩)`. Placeholders: `{α : Type} (t l : List α) (a : α)`.

| Before | After |
|---|---|
| `⊢ t ++ [a] <:+ l ++ [a]` | `⊢ t <:+ l` |

**R13 · `simp only [f]`** changes the **goal**: it unfolds `f`, substitutes its `let`, and reduces
`(a, b).1` to `a`. In the guide, `shift q y := let d := q.1 - y; (d, q.2 + d)`. For `inv_step`, use
`simp only [kadaneStep]` on the goals about `(kadaneStep st x).1`, before `omega`. Placeholders:
`(st : Int × Int) (x : Int)`.

| Before | After |
|---|---|
| `⊢ P (shift st x).fst` | `⊢ P (st.fst - x)` |

**R14 · `List.infix_concat_iff`** changes the **goal list** (with `rcases List.infix_concat_iff.mp h with
h1 | h1`). Statement: `l₁ <:+: l₂ ++ [a] ↔ l₁ <:+ l₂ ++ [a] ∨ l₁ <:+: l₂`: a segment of `l₂ ++ [a]` either
ends at the new `a` (then it is a suffix: use your suffix bound) or lies inside `l₂` (use the old segment
bound). Right to left, `List.infix_concat_iff.mpr (.inr h)` turns an old segment into a new one.
Placeholders: `{α : Type} (l₁ l₂ : List α) (a : α)`.

| Before | After |
|---|---|
| `h : l₁ <:+: l₂ ++ [a] ⊢ G` | `h1 : l₁ <:+ l₂ ++ [a] ⊢ G`, `h1 : l₁ <:+: l₂ ⊢ G` |

**R15 · `List.IsSuffix.isInfix`** changes the **goal** (with `apply`). Statement: `l₁ <:+ l₂ → l₁ <:+: l₂`.
Dot notation: for `h : l₁ <:+ l₂`, the term `h.isInfix : l₁ <:+: l₂`. Use it when the new `best` is the new
`cur`, attained by a suffix. Placeholders: `{α : Type} (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ l₁ <:+: l₂` | `⊢ l₁ <:+ l₂` |

To assemble `inv_step`, `refine ⟨?_, hsuf, ?_, hatt⟩` with your two suffix facts. They are stated about
`max 0 (st.2 + x)`, the goal about `(kadaneStep st x).2`: `refine` accepts this because the two are equal by
unfolding (R22).

---

## Part 3 · `inv_foldl` (MILESTONE)

Statement: `Inv p st → Inv (p ++ l) (l.foldl kadaneStep st)`. Induction on `l`, with `p` and `st` changing:
after reading `x`, the prefix is `p ++ [x]` and the state `kadaneStep st x`.

**R16 · `induction l generalizing p s with | nil => … | cons x l ih => …`** changes the **goal list and
the context**. `generalizing p s` makes the induction hypothesis hold for *every* `p` and `s`, which the
step needs because the fold changes both. Placeholders: `{α β : Type} (f : β → α → β)
(I : List α → β → Prop)`, `(l p : List α) (s : β) (h : I p s)`. In the `cons` goal, the context has
`ih : ∀ (p : List α) (s : β), I p s → I (p ++ l) (List.foldl f s l)`.

| Before | After |
|---|---|
| `h : I p s ⊢ I (p ++ l) (List.foldl f s l)` | `h : I p s ⊢ I (p ++ []) (List.foldl f s [])`, `x : α, h : I p s ⊢ I (p ++ x :: l) (List.foldl f s (x :: l))` |

**R17 · `List.foldl_cons`** changes the **goal**. Statement: `List.foldl f b (a :: l) = List.foldl f (f b a) l`
(one step of the loop). `List.foldl_nil : List.foldl f b [] = b`. Both are `simp` lemmas.
Placeholders: `{α β : Type} (f : β → α → β) (b : β) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.foldl f b (a :: l))` | `⊢ P (List.foldl f (f b a) l)` |

**R18 · `List.append_nil`, `List.nil_append`** change the **goal**. Statements: `l ++ [] = l`, `[] ++ l = l`.
`simp` lemmas. Placeholders: `{α : Type} (p : List α)`.

| Before | After |
|---|---|
| `⊢ P (p ++ [])` | `⊢ P p` |

**R19 · `List.append_assoc`, `List.singleton_append`** change the **goal**. Statements:
`as ++ bs ++ cs = as ++ (bs ++ cs)` and `[x] ++ l = x :: l`. Together they turn the prefix `p ++ [x] ++ l`
that `ih (p ++ [x]) …` talks about into the goal's `p ++ x :: l`. `simp` uses `List.cons_append` and R18
for the second step. Placeholders: `{α : Type} (p l : List α) (x : α)`.

| Before | After `rw [List.append_assoc]` | After `rw [List.singleton_append]` |
|---|---|---|
| `⊢ P (p ++ [x] ++ l)` | `⊢ P (p ++ ([x] ++ l))` | `⊢ P (p ++ x :: l)` |

**R20 · `simpa using e`** **closes** the goal: `simp` simplifies both the type of `e` and the goal (here with
R17–R19), then `e` must match the goal. In the `cons` case, `e` is `ih (p ++ [x]) _ (inv_step p st x h)`;
`_` lets Lean fill in the state. Placeholders: `{α : Type} (P : List α → Prop)`.

| Before | After |
|---|---|
| `e : P (p ++ [x] ++ l) ⊢ P (p ++ x :: l)` | ∅ |

---

## Part 4 · `kadane_upper`

Statement: `ys <:+: xs → ys.sum ≤ kadane xs`. First get the invariant at the end of the loop:
`hI : Inv xs (xs.foldl kadaneStep (0, 0))`, from `inv_foldl xs [] (0, 0) inv_nil` (its type says
`[] ++ xs`: `simpa using`, R20 with R18). Then use one part of `hI`.

**R21 · `h.1`, `h.2.2.1`** **close** the goal with one part of a conjunction. `∧` nests to the right, so
`A ∧ B ∧ C ∧ D` is `A ∧ (B ∧ (C ∧ D))`: `h.1 : A`, `h.2.1 : B`, `h.2.2.1 : C`, `h.2.2.2 : D`. A part that is
a `∀ … → …` is applied to arguments: `hI.1 ys h`. Placeholders: `(A B C D : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ∧ D ⊢ C` | ∅ |

**R22 · `exact h` up to unfolding** **closes** `P (f xs)` with `h : P (body of f)`: `exact` (and `refine`,
and a term after `:=`) compares types after unfolding definitions. `kadane xs` is by definition
`(xs.foldl kadaneStep (0, 0)).1`, so a proof about that term proves the statement about `kadane xs`.
In the guide, `lastOr xs := xs.foldl (fun _ x => x) 0`. Placeholders: `(xs : List Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : P (List.foldl (fun x x_1 => x_1) 0 xs) ⊢ P (lastOr xs)` | ∅ |

The proof after the frozen `:=` may be a term: `have hI : T := by …` on one line, then the projection on the
next. Or start with `by` and use `exact`.

---

## Part 5 · `kadane_attained`

Statement: `∃ ys, ys <:+: xs ∧ ys.sum = kadane xs`. The same `hI` as in Part 4, then the third part of it
(R21), accepted by R22.

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1: a fold invariant for a running maximum.** `AllLe p m := ∀ y, y ∈ p → y ≤ m`. One step
(`allLe_step`): `intro y hy`, `simp at hy` splits `y ∈ p ++ [x]` into `y ∈ p ∨ y = x`, then R7 and R10.
The fold (`allLe_foldl`): R16 and R20, exactly the shape of `inv_foldl`. The end: R20 on the start fact,
then the `∀` applied. Goals met:

```lean-goal
⊢ AllLe (p ++ [x]) (max m x)
⊢ y ≤ max m x
⊢ AllLe (p ++ l) (List.foldl max m l)
⊢ y ≤ List.foldl max 0 xs
```

**W2: suffixes of `l ++ [a]` by cases.** `rcases List.suffix_concat_iff.mp hys with rfl | ⟨t, rfl, ht⟩`
(R6, R7) gives the two goals below; the first closes by `simp`, the second by `have := hl t ht`, `simp`,
`omega`.

```lean-goal
⊢ [].length ≤ l.length + 1
⊢ (t ++ [a]).length ≤ l.length + 1
```

---

## Traps

- `omega` treats `(kadaneStep st x).1` as an unknown number: `simp only [kadaneStep]` first (R13).
- `omega` only uses hypotheses that are in the context. A bound such as `hc : ∀ ys, ys <:+ p → …` must be
  instantiated first: `have := hc t ht`.
- `st.2` is printed `st.snd`; `rw` and `simp` treat them as the same.
- Without `generalizing p st`, the `cons` case's `ih` is about the original `p` and `st` and cannot be applied
  to `p ++ [x]` and `kadaneStep st x` (R16).
- `ih (p ++ [x]) …` is about the prefix `p ++ [x] ++ l`, the goal about `p ++ x :: l`: equal, but not the
  same text. `simpa using` puts both in the same form (R19, R20); `exact` alone fails.
- `inv_foldl xs [] (0, 0) inv_nil` is about `[] ++ xs`, not `xs`: again `simpa using` (R18).
- `Inv` is a definition: `obtain` and `refine ⟨…⟩` look through it, but `simp`, `rw` and `omega` do not.
  Take it apart first (R5).
- After `rcases … with rfl | …` the variable you case on is gone, replaced by `[]` or `t ++ [x]`: any
  hypothesis about it changes too.
- The empty segment counts: that is why the state starts at `(0, 0)` and `cur` is `max 0 (…)`. The witness
  for a sum of `0` is `[]` (R2).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove a defined `∧`/`∃` with witnesses | `refine ⟨?_, ?_, ⟨[], List.nil_infix, rfl⟩, …⟩` | R1, R2 |
| `[]` is a segment / suffix | `List.nil_infix` / `List.nil_suffix` | R2 |
| a segment / suffix of `[]` is `[]` | `List.eq_nil_of_infix_nil h` / `List.eq_nil_of_suffix_nil h` | R3 |
| sums | `simp [List.sum_append]` (`List.sum_nil`, `List.sum_cons` are automatic) | R4, R8, R9 |
| take the invariant apart | `obtain ⟨hb, hc, ⟨yb, hyb, hsb⟩, ⟨yc, hyc, hsc⟩⟩ := h` | R5 |
| suffixes of `p ++ [x]` | `rcases List.suffix_concat_iff.mp hys with rfl \| ⟨t, rfl, ht⟩` | R6, R7 |
| build a suffix of `p ++ [x]` | `List.suffix_concat_iff.mpr (.inr ⟨t, rfl, ht⟩)` | R12 |
| segments of `p ++ [x]` | `rcases List.infix_concat_iff.mp hys with h1 \| h1` | R14 |
| old segment → new segment | `List.infix_concat_iff.mpr (.inr h)` | R14 |
| suffix → segment | `h.isInfix` | R15 |
| arithmetic with `max` | `omega` | R10 |
| case on a condition | `by_cases h0 : st.2 + x ≤ 0` | R11 |
| unfold the step function | `simp only [kadaneStep]` | R13 |
| induction over a fold | `induction l generalizing p st with \| nil => … \| cons x l ih => …` | R16 |
| fold / append normal forms | `simpa using …` (uses `List.foldl_cons`, `List.append_assoc`, …) | R17–R20 |
| one part of the invariant | `hI.1 ys h`, `hI.2.2.1` | R21 |
| `kadane xs` vs. `(xs.foldl kadaneStep (0, 0)).1` | nothing: equal by unfolding | R22 |
| see the state | infoview | |
