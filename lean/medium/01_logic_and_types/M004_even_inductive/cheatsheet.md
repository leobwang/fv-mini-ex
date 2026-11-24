# M004 · Even as an inductive predicate: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `Nat`, `inductive` types, `induction`/`cases` on `Nat`,
`intro`, `exact`, `rw`, `omega`, `∃`. **New here:** an *inductive predicate* (an `inductive … : Nat → Prop`
whose constructors are inference rules), building derivations by applying rules, induction on a
derivation, and *inversion* (`cases` on a hypothesis to see which rule produced it). Core Lean only,
no Mathlib.

## The objects

- **`Ev : Nat → Prop`** (spec) has two rules: `Ev.zero : Ev 0` and
  `Ev.step : ∀ (n : Nat), Ev n → Ev (n + 2)`. `Ev n` holds exactly when there is a finite derivation
  (a chain `zero`, `step`, `step`, …) ending in `Ev n`. Nothing else produces an `Ev` proof.
- **Holes:** five theorems: `Ev 4`; `Ev (2 * n)`; `Ev n → ∃ k, n = 2 * k`; `¬ Ev 1`; `Ev (n + 2) → Ev n`.
- The guide teaches on a toy predicate `Step3 : Nat → Prop` ("multiple of 3", rules `base : Step3 0`,
  `next : ∀ n, Step3 n → Step3 (n + 3)`). It is **not** the exercise's predicate.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means no goal is left.
- `P`, `Q` are "the rest of your goal" (`P : Nat → Prop`, or `P : Prop` when no index is involved). The step
  changes only the part inside `P (…)`.
- Placeholders are written as Lean binders: `(n m k w : Nat)`, `(A G : Prop)`, `(h : Step3 n)`.
- In `guide.lean`, `exact hs _ ‹_›` uses `‹_›`: "the hypothesis whose type is the expected one". It reaches
  inaccessible names such as `a✝` (E012).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ev n`, `Step3 n` | the proposition "`n` is derivable by the rules"; a proof of it is a derivation |
| `Ev.step n h`, `.step _ h` | the derivation of `Ev (n + 2)` built from `h : Ev n`; `.step` is short for `Ev.step` when the expected type is known; `_` asks Lean to infer `n` |
| `¬A` | `A → False` (printed without a space) |
| `∃ k, n = 2 * k` | there is a `k` with `n = 2 * k`; built with `⟨k, proof⟩`, used with `obtain ⟨k, hk⟩ := h` |
| `n✝`, `a✝`, `a_ih✝` | inaccessible names made by `induction`/`cases` without `with`: the new number, the rule's premise, the induction hypothesis |
| `n n✝ : Nat` | two different numbers: your original `n` (now unused) and the rule's `n✝` |
| `n % 3` | remainder of `n` divided by `3` (W3) |
| `Nat.mul 3 n` | `3 * n` after Lean unfolded `*` to match a rule (W2); avoid by reshaping first (R5) |
| `case base`, `case next` | the goal for one rule of the predicate (`case zero`, `case step` for `Ev`) |

---

## Part 1 · `ev_four`

Statement: `Ev 4`. Build the derivation `zero → step → step`: from the goal, apply the `step` rule twice
(the index drops by 2 each time), then close with `zero`. Or write the same tree as one term.

**R1 · `exact .base`** **closes** the goal with a rule that has no premise. `.base` means `Step3.base`
(Lean looks the name up in the namespace of the expected type).

| Before | After |
|---|---|
| `⊢ Step3 0` | `∅` |

**R2 · `apply Step3.next`** changes the **goal**: it matches the goal against the rule's conclusion
`Step3 (?n + 3)` and leaves the premise `Step3 ?n`. On a literal index Lean computes `?n` (`6 = ?n + 3` gives
`?n := 3`). As a term the step is `.next _ h`. Placeholders: `(n : Nat) (h : Step3 n)`.

| Before | After |
|---|---|
| `⊢ Step3 (n + 3)` | `h : Step3 n ⊢ Step3 n` |
| `h : Step3 3 ⊢ Step3 6` | `⊢ Step3 3` |

**W1** in the guide proves `Step3 9` both ways: `.next _ (.next _ (.next _ .base))`, and R2, R2, R2, R1:

```lean-goal
⊢ Step3 9
⊢ Step3 6
⊢ Step3 3
⊢ Step3 0
```

---

## Part 2 · `ev_double`

Statement: `Ev (2 * n)` for every `n`. Induct on `n` (R3). `zero` is `Ev (2 * 0)`, which is `Ev 0` by
computation (R1). In `succ n ih`, `ih : Ev (2 * n)` and the goal is `Ev (2 * (n + 1))`: reshape the index to
`2 * n + 2` (R5, proved by R4), then apply `step` and use `ih` (R2).

**R3 · `induction n`** changes the **goal list and the context**: goals `zero` and `succ`; in `succ` the context
gains the new number and the induction hypothesis. With `induction n with | zero => … | succ n ih => …` they
are named `n` and `ih`. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n✝ : Nat, a✝ : P n✝ ⊢ P (n✝ + 1)` |

**R4 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int`: `+`, `-`, `*` by a literal, `/` and `%`
by a literal, `=`, `≤`, `<`, `¬`, `∧`, `∨`. It uses the hypotheses in the context. Placeholders: `(m k : Nat)`.

| Before | After |
|---|---|
| `hk : m = 5 * k ⊢ m + 5 = 5 * (k + 1)` | `∅` |

**R5 · `have h : a = b := by omega`, then `rw [h]`** changes the **context**, then the **goal**: the index is
rewritten into the shape a rule's conclusion has (`_ + 3`, or `_ + 2` for `Ev`). Placeholders: `(n : Nat)`.
The one-step form is `rw [show 5 * (n + 1) = 5 * n + 5 by omega]`.

| Before | After `have h …` | After `rw [h]` |
|---|---|---|
| `⊢ P (5 * (n + 1))` | `h : 5 * (n + 1) = 5 * n + 5 ⊢ P (5 * (n + 1))` | `⊢ P (5 * n + 5)` |

**W2: why reshape first.** `apply Step3.next` on `Step3 (3 * (n + 1))` succeeds only by unfolding `*`, and the
premise comes out in an unfamiliar form:

```lean-goal
⊢ Step3 (3 * (n + 1))
⊢ Step3 (Nat.mul 3 n)
```

After `rw [show 3 * (n + 1) = 3 * n + 3 by omega]` the same `apply` leaves exactly `ih`'s statement:

```lean-goal
⊢ Step3 (3 * n + 3)
⊢ Step3 (3 * n)
```

---

## Part 3 · `ev_exists`

Statement: `Ev n → ∃ k, n = 2 * k`. Induct on the **derivation** `h` (R6), not on `n`: each rule gives one
case, with the index replaced by the rule's conclusion. `zero`: the goal `∃ k, 0 = 2 * k` takes witness `0`
(R7). `step m _ ih`: unpack `ih : ∃ k, m = 2 * k` (R8), give witness `k + 1` (R7), and prove
`m + 2 = 2 * (k + 1)` from `hk` (R4).

**R6 · `induction h`** (`h : Step3 n`) changes the **goal list and the context**: one goal per rule. In `next` the
context gains the rule's number `n✝`, its premise `a✝ : Step3 n✝`, and the induction hypothesis
`a_ih✝ : Q n✝`. `induction h with | base => … | next m hm ih => …` names them `m`, `hm`, `ih`.
Placeholders: `(Q : Nat → Prop) (n : Nat) (h : Step3 n)`.

| Before | After |
|---|---|
| `h : Step3 n ⊢ Q n` | `⊢ Q 0`, `a✝ : Step3 n✝, a_ih✝ : Q n✝ ⊢ Q (n✝ + 3)` |

**R7 · `refine ⟨w, ?_⟩`** changes the **goal**: it supplies the witness of `∃` and leaves the property.
`exact ⟨w, proof⟩` does it in one step; `exact ⟨0, rfl⟩` closes `∃ k, 0 = 5 * k` because `0 = 5 * 0` holds by
computation. Placeholders: `(P : Nat → Prop) (w : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ k, P k` | `h : P w ⊢ P w` |
| `⊢ ∃ k, 0 = 5 * k` | `∅` |

**R8 · `obtain ⟨k, hk⟩ := h`** changes the **context**: `h : ∃ k, P k` is replaced by a witness and its property.
Placeholders: `(P : Nat → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G`, with `h : ∃ k, P k` | `k : Nat, hk : P k ⊢ G` (`h` is gone) |

**W3** proves `Step3 n → n % 3 = 0` by R6, then `rfl` and R4:

```lean-goal
⊢ n % 3 = 0
⊢ 0 % 3 = 0
⊢ (n✝ + 3) % 3 = 0
```

---

## Part 4 · `not_ev_one`

Statement: `¬ Ev 1`. Introduce the hypothesis (R9), then invert it (R10): no rule concludes `Ev 1`
(`zero` gives `0`, `step m` gives `m + 2 ≥ 2`), so the goal `False` disappears.

**R9 · `intro h`** on a negation changes the **goal and the context**: `¬A` is `A → False`. Placeholders:
`(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R10 · `cases h`** with no rule able to produce `h`'s index **closes** the goal, whatever it is. Lean checks
each rule: `base` needs `1 = 0`, `next m` needs `1 = m + 3`; both fail on `Nat` constructors. Placeholders:
`(G : Prop) (h : Step3 1)`.

| Before | After |
|---|---|
| `h : Step3 1 ⊢ G` | `∅` |

**W4** proves `¬ Step3 4` by R9, R11, R10: `intro h`, then `cases h with | next _ h' => cases h'`. The first
`cases` leaves `h' : Step3 (0 + 1)` (only `next 1` concludes `4`), the second finds no rule for it.

```lean-goal
⊢ ¬Step3 4
⊢ False
```

---

## Part 5 · `ev_minus_two`

Statement: `Ev (n + 2) → Ev n`. Invert `h` (R11): only `step` concludes `_ + 2`, and its premise is the
derivation of `Ev n` you need.

**R11 · `cases h`** with exactly one possible rule changes the **context**: `h` is replaced by that rule's premise.
For `h : Step3 (n + 3)`: `base` would need `n + 3 = 0` (impossible), `next m` needs `m + 3 = n + 3`, so `m = n`
and the premise is `Step3 n`. `cases h with | next _ h' => …` names it `h'`. Placeholders:
`(n : Nat) (P : Prop) (h : Step3 (n + 3))`.

| Before | After |
|---|---|
| `h : Step3 (n + 3) ⊢ P` | `a✝ : Step3 n ⊢ P` |

---

## Traps

- `induction n` on `Ev (2 * n)` works, but `induction n` on `Ev n → ∃ k, …` does not: from `Ev (n + 1)` you
  learn nothing about `Ev n`. Induct on the derivation `h` (R6).
- `induction h` is for an index that is a variable (`h : Ev n`, goal `Q n`). On `h : Ev (n + 2)` it fails with
  "Index in target's type is not a variable". To peel one rule off it you need no induction hypothesis: use
  `cases h` (R11).
- `apply Ev.step` on `Ev (2 * (n + 1))` "works" by unfolding `*` and leaves `Ev (Nat.mul 2 n)` (W2). Reshape the
  index to `2 * n + 2` first (R5) so the premise is literally `ih`'s statement.
- `cases h` with `with` must name the rule's arguments in order: `| step _ h' => …` (the number, then the
  premise). The `zero` alternative is omitted because Lean already ruled it out.
- `¬A` is `A → False`: to use it, `intro h`, then derive `False` (here by `cases h`).
- `t1 ; t2` runs `t2` on the first goal only. After `induction`, use `with | … => …` or `·` per goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| close with a premise-free rule | `exact .zero` | R1 |
| use a rule backwards | `apply Ev.step` / term `.step _ h` | R2 |
| a concrete derivation | `.step _ (.step _ .zero)` | R1, R2, W1 |
| induct on a number | `induction n with \| zero => … \| succ n ih => …` | R3 |
| linear `Nat` arithmetic | `omega` | R4 |
| reshape an index | `have h : a = b := by omega; rw [h]` | R5 |
| induct on a derivation | `induction h with \| zero => … \| step m hm ih => …` | R6 |
| prove `∃ k, …` | `exact ⟨w, proof⟩` / `refine ⟨w, ?_⟩` | R7 |
| use `∃ k, …` | `obtain ⟨k, hk⟩ := h` | R8 |
| prove `¬A` | `intro h` | R9 |
| no rule fits the index | `cases h` | R10 |
| peel the last rule | `cases h with \| step _ h' => …` | R11 |
| see the state | infoview | |
