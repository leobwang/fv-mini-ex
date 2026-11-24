# E049 · Naming goals: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact`, `rfl`, `rw`, `Or.inl`/`Or.inr`,
`cases`/`induction` *with* a `with` clause, and the anonymous-hypothesis brackets `‹T›` (E046). **New
here:** what `cases`, `induction` and `intros` produce when you give them **no names** (tagged goals and
inaccessible hypotheses `x✝`), and the three ways to name them afterwards: `case tag x y => …`,
`next x y => …` and `rename_i x y`. Also `nomatch` for an impossible hypothesis and the lemmas
`Nat.le_add_left`, `Nat.add_succ`. No Mathlib.

`with`, `intro`, `rintro`, `fun`, `simp`, `decide`, `omega` and `assumption` are banned: every name you use
must come from `case`, `next` or `rename_i`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : Bool → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- Several states in one cell (`⊢ P 0`, `⊢ P (n✝ + 1)`) are several goals, worked on in order.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `case zero`, `case succ` | the **tag** of a goal: the name of the constructor (`Nat.zero`, `Nat.succ`) that `cases`/`induction` used for it. `case`/`next` select goals by it |
| `case false`, `case true` | the tags after `cases` on a `Bool` |
| `n✝ : Nat` | an **inaccessible** variable: Lean invented the name; you cannot type `n✝`. Give it a name with `case`, `next` or `rename_i` |
| `a✝ : P n✝` | an inaccessible hypothesis (from `intros`, or the induction hypothesis from `induction`) |
| `a✝¹`, `a✝²` | older inaccessible hypotheses: `a✝` is the most recent, `a✝¹` the one before it, and so on |
| `n✝ + 1` | what `cases`/`induction` put for `Nat.succ n✝`: Lean prints the successor as `+ 1` |
| `A ∨ B`, `a ≤ b` | "A or B" (prove one side, R3); "a is at most b" on `Nat` |
| `b && c` | Boolean and. It computes on its first argument: `false && c` is `false`, `true && c` is `c` |
| `!x` | Boolean not: `!false` is `true`, `!true` is `false` (R7, R9) |
| `(b && c) = true` | the `Bool` value `b && c` equals `true`; a `Prop`, so it can be a hypothesis `h` |
| `(a + b).succ` | `Nat.succ (a + b)`, i.e. `a + b + 1` (definitionally equal; `exact` and `rfl` accept either) |
| `‹T›` | "the hypothesis of type `T`, whatever its name": works on `a✝` too (E046) |

---

## Part 1 · `zero_or_pos`

Statement: every `n : Nat` is `0` or at least `1`. Split `n` with `cases n` and prove one side of the `∨` in
each case.

**R1 · `cases n`** (no `with`) changes the **goal list**: one goal becomes a goal tagged `zero` (with `n`
replaced by `0`) and one tagged `succ` (with `n` replaced by `n✝ + 1`, `n✝` inaccessible). Placeholders:
`(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n✝ : Nat ⊢ P (n✝ + 1)` |

**R2 · `case tag x => tac`** changes the **goal list**: it focuses the goal tagged `tag`, renames that goal's
inaccessible variables to `x` (in the order they were made), and runs `tac`, which must close it. The other
goals stay as they were; tags can be taken in any order. Placeholders: `(P : Nat → Prop)`,
`(h : ∀ m, P (m + 1))`.

| Before | After `case succ m => exact h m` |
|---|---|
| `⊢ P 0`, `n✝ : Nat ⊢ P (n✝ + 1)` | `⊢ P 0` |

Inside the block, before `exact h m`, the state is the `succ` goal with `n✝` renamed (W1 shows it at top
level with `rename_i m`):

| Before (the `succ` goal) | Inside `case succ m =>` |
|---|---|
| `n✝ : Nat ⊢ P (n✝ + 1)` | `m : Nat ⊢ P (m + 1)` |

**R3 · `Or.inl`, `Or.inr`** **close** a disjunction: `Or.inl : A → A ∨ B` proves it from the left side,
`Or.inr : B → A ∨ B` from the right. Placeholders: `(A B : Prop) (a : A) (b : B)`.

| Before | After |
|---|---|
| `a : A ⊢ A ∨ B` (`exact Or.inl a`) | no goals |
| `b : B ⊢ A ∨ B` (`exact Or.inr b`) | no goals |

**R4 · `Nat.le_add_left`** **closes** the goal. The lemma is `Nat.le_add_left (n m : Nat) : n ≤ m + n`; both
arguments are explicit, so `Nat.le_add_left a k : a ≤ k + a` (with `a := 3`, W3 gets `3 ≤ k + 3`).
Placeholders: `(a k : Nat)`.

| Before | After `exact Nat.le_add_left a k` |
|---|---|
| `⊢ a ≤ k + a` | no goals |

**W3** chains R1, R2, R3, R4 on `n = 0 ∨ 3 ≤ n + 2`. After `cases n` the two goals are

```lean-goal
⊢ 0 = 0 ∨ 3 ≤ 0 + 2
⊢ n✝ + 1 = 0 ∨ 3 ≤ n✝ + 1 + 2
```

and `case zero => exact Or.inl rfl`, `case succ k => exact Or.inr (Nat.le_add_left 3 k)` close them
(`k + 1 + 2` and `k + 3` are equal by computation, so `exact` accepts the lemma's `3 ≤ k + 3`).

---

## Part 2 · `intros_rename`

Statement: `P → (P → Q) → Q`. Introduce both premises without naming them, name them, apply one to the other.

**R5 · `intros`** changes the **context and the goal**: every leading premise of the goal moves into the
context as an inaccessible hypothesis, and the goal keeps only the conclusion. The most recent one is `a✝`.
Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A → B → C` | `a✝¹ : A, a✝ : B ⊢ C` |

**R6 · `rename_i x y`** changes the **context**: the last two inaccessible hypotheses get the names `x`, `y`,
oldest first, so the names read in the same order as the premises they came from. With fewer names, only the
most recent hypotheses are renamed. Placeholders: `(A B C : Prop)`.

| Before | After `rename_i x y` | After `rename_i y` instead |
|---|---|---|
| `a✝¹ : A, a✝ : B ⊢ C` | `x : A, y : B ⊢ C` | `a✝ : A, y : B ⊢ C` |

**W4:** with three premises `A → B → (A → B → C) → C`, `intros` gives

| After `intros` | After `rename_i a b f` |
|---|---|
| `a✝² : A, a✝¹ : B, a✝ : A → B → C ⊢ C` | `a : A, b : B, f : A → B → C ⊢ C` |

and `exact f a b` closes it.

---

## Part 3 · `next_bool`

Statement: from `h : (b && c) = true`, conclude `b = true`. Split `b`. In the `false` branch `h` is impossible;
in the `true` branch the goal is `true = true`.

**R7 · `cases b`** on `b : Bool` changes the **goal list and the context**: goals tagged `false` and `true`,
and every hypothesis that mentions `b` is rewritten with the value. Placeholders: `(P : Bool → Prop)`
`(x : Bool) (h : (!x) = true)` (`!x` is Boolean not).

| Before | After |
|---|---|
| `x : Bool, h : (!x) = true ⊢ P x` | `h : (!false) = true ⊢ P false`, `h : (!true) = true ⊢ P true` |

**R8 · `next => tac`** changes the **goal list**: it focuses the **first** remaining goal, whatever its tag,
and `tac` must close it. `next x y => tac` also names that goal's inaccessible variables, like `case`. After
`cases b` the first goal is `false` (constructor order). Placeholders: `(P : Bool → Prop)`.

| Before | After `next => exact h0` |
|---|---|
| `⊢ P false`, `⊢ P true` | `⊢ P true` |

**R9 · `nomatch h`** **closes** any goal when `h : false = true`. `nomatch h` does case analysis on `h`; an
equation has one constructor, `rfl : a = a`, which cannot have type `false = true`, so there are zero cases.
Lean computes `h`'s type first, so it also works when `h` only reduces to `false = true`. Placeholders:
`(P : Prop)`.

| Before | After |
|---|---|
| `h : false = true ⊢ P` | no goals |
| `h : (!true) = true ⊢ P` | no goals |

**W5:** `(x : Bool) (h : (x && false) = true) : x = false` by `cases x`, `next => rfl`, `next => nomatch h`.
The second `next` sees

```lean-goal
⊢ true = false
```

with `h : (true && false) = true`, which computes to `false = true`.

---

## Part 4 · `zero_add'`

Statement: `0 + n = n`. Lean's `+` recurses on its **second** argument (`a + 0 = a`, `a + (b + 1) = (a + b) + 1`
by definition), so `0 + n` does not compute: you need induction on `n`.

**R10 · `induction n`** (no `with`) changes the **goal list**: goals tagged `zero` and `succ`. The `succ`
goal gets an inaccessible variable `n✝` and the induction hypothesis as an inaccessible `a✝`. Placeholders:
`(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n✝ : Nat, a✝ : P n✝ ⊢ P (n✝ + 1)` |

**R11 · `case succ m ih => tac`** is R2 with two names: the variable first, then the induction hypothesis
(the order in which `induction` made them). W2 shows the state at top level with `rename_i m ih`.
Placeholders: `(P : Nat → Prop) (s : ∀ m, P m → P (m + 1))`.

| Before (the `succ` goal) | Inside `case succ m ih =>` |
|---|---|
| `n✝ : Nat, a✝ : P n✝ ⊢ P (n✝ + 1)` | `m : Nat, ih : P m ⊢ P (m + 1)` |

**R12 · `rw [Nat.add_succ]`** changes the **goal**. The lemma is
`Nat.add_succ (n m : Nat) : n + m.succ = (n + m).succ`, i.e. `n + (m + 1) = (n + m) + 1`; `rw` matches
`m + 1` as `m.succ`. It pulls the `+ 1` out of the right summand, so an IH about `n + m` can apply.
Placeholders: `(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a + (b + 1))` | `⊢ P (a + b).succ` |

**W6** chains R10, R11 (as `rename_i`), R12 and `rw [ih]` on `2 + n = n + 2`:

| After `rename_i k ih` | After `rw [Nat.add_succ]` |
|---|---|
| `k : Nat, ih : 2 + k = k + 2 ⊢ 2 + (k + 1) = k + 1 + 2` | `ih : 2 + k = k + 2 ⊢ (2 + k).succ = k + 1 + 2` |

`rw [ih]` gives `(k + 2).succ = k + 1 + 2`, both sides compute to the same number, and `rw` closes it with
`rfl`. **W7** is the same proof as `case succ k ih => rw [Nat.add_succ, ih]`.

---

## Traps

- **Honor system:** `intros x y` would name the hypotheses directly; here write plain `intros` and name them
  with `rename_i` (or refer to them as `‹T›`, E046). Likewise no `cases … with` / `induction … with`.
- `n✝` and `a✝` cannot be typed: `exact h n✝` fails with `expected token`; name the variable first, or let Lean fill it
  with `_` (`exact h _`, `exact s _ ‹_›`).
- `rename_i` renames the **most recent** inaccessible hypotheses, and it acts on the main (first) goal only.
- `case tag => tac` and `next => tac` must **close** the goal. If `tac` leaves goals, `case` fails with an
  error.
- After `cases b`, `next` takes `false` first (constructor order: `Bool.false`, then `Bool.true`).
- `nomatch h` needs `h`'s type to compute to an impossible equation such as `false = true`; it does not help
  with `h : x = true` for a variable `x`. Split `x` first.
- `rw [Nat.add_succ]` fixes `n`, `m` at the first match it finds and rewrites that instance only (with its
  identical copies). Then `rw [ih]` needs the left side of `ih` to appear literally in the goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `n : Nat`, names later | `cases n` | R1 |
| prove the goal tagged `t`, naming its new variables | `case t x y => tac` | R2, R11 |
| prove `A ∨ B` | `exact Or.inl a` / `exact Or.inr b` | R3 |
| `n ≤ m + n` | `Nat.le_add_left n m` | R4 |
| introduce all premises without names | `intros` | R5 |
| name the last `k` inaccessible hypotheses | `rename_i x₁ … x_k` | R6 |
| split `b : Bool` | `cases b` (tags `false`, `true`) | R7 |
| prove the first remaining goal | `next => tac` / `next x => tac` | R8 |
| close a goal from `h : false = true` | `nomatch h` | R9 |
| induction, names later | `induction n` | R10 |
| `n + (m + 1) → (n + m).succ` | `rw [Nat.add_succ]` | R12 |
| use a hypothesis by its type | `‹T›` | E046 |
| see the state | infoview | |
