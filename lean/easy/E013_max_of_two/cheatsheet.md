# E013 · Max of two: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E012: `def` (E002), `exact` (E003), `∧`, `∨` (E005), `simp [f]` (E010),
`omega` (E011), `if c then x else y` (E012).
**New here:** the tactic `by_cases`, which splits a proof on whether a condition holds, and removing an
`if` with `simp [h]` once a fact `h` about its condition is in the context.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change or matter.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- `c : Prop` is a condition. `[Decidable c]` is a requirement on `c` (a *type class*): Lean can compute
  whether `c` is true, which `if c` needs. Comparisons `≤ < =` on `Int` and `Nat` meet it.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `a b : Int` | integers, negatives included |
| `if c then x else y` | `x` when `c` holds, `y` otherwise |
| `myMax a b` | the exercise's function, still folded; `simp [myMax]` unfolds it (R3) |
| `case pos`, `case neg` | after `by_cases h : c`: the goal with `h : c`, the goal with `h : ¬c` (R2) |
| `h : ¬a ≤ b` | "not `a ≤ b`", i.e. `b < a` on `Int` |
| `A ∧ B ∧ C` | `A ∧ (B ∧ C)`: `∧` nests to the right |
| `(a ≤ if c then x else y)` | `a ≤ (if c then x else y)`; Lean prints the parentheses around the whole comparison |
| `inst✝ : Decidable c` | the unnamed `[Decidable c]` argument; ignore it |

---

## Part 1 · `myMax`

Statement: write the body of `myMax (a b : Int) : Int`, the larger of `a` and `b`. Any body type-checks;
the theorem in Part 2 forces it to be the maximum. One `if` on a comparison of `a` and `b` does it.

**R1 · `if c then x else y`** **closes** a `⊢ α` goal: it is a term of type `α`, built from two terms of
type `α`. In a `def` you write it directly after `:=`. Placeholders: `{α : Type} (c : Prop) [Decidable c]
(x y : α)`.

| Before | After |
|---|---|
| `⊢ α` | no goals |

---

## Part 2 · `myMax_spec`

Statement: for all `a b : Int`, `a ≤ myMax a b`, `b ≤ myMax a b`, and `myMax a b` is `a` or `b`. Split on
the condition of your `if` (R2); in each case `simp [myMax, h]` unfolds `myMax` (R3), picks the branch
(R4 or R5) and removes the parts that became trivially true (R6). What is left, if anything, is linear
arithmetic (R7).

**R2 · `by_cases h : c`** changes the **goal list and the context**: one goal becomes two copies of it,
`case pos` with `h : c` and `case neg` with `h : ¬c`. Pick `c` to be exactly the condition of the `if`
you want to remove. Placeholders: `(c G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : c ⊢ G`, `h : ¬c ⊢ G` |

**R3 · `simp only [f]`** changes the **goal**: the defined name is replaced by its body. `simp [f]` does
this and then simplifies further; without a fact about the condition the `if` stays (W2). Placeholders:
`(x : Int)` and the guide's `lowCap x = if x ≤ 10 then x else 10`.

| Before | After |
|---|---|
| `⊢ P (lowCap x)` | `⊢ P (if x ≤ 10 then x else 10)` |

**R4 · `simp [hc]` with `hc : c`** changes the **goal**: `if c then x else y` becomes `x`. `simp` turns `c`
into `True` with `hc`, then applies `if_pos`. Placeholders: `{α : Type} (c : Prop) [Decidable c] (x y : α)`.

| Before | After |
|---|---|
| `hc : c ⊢ P (if c then x else y)` | `⊢ P x` |

**R5 · `simp [hc]` with `hc : ¬c`** changes the **goal**: `if c then x else y` becomes `y` (`c` turns into
`False`, then `if_neg`). Same placeholders as R4.

| Before | After |
|---|---|
| `hc : ¬c ⊢ P (if c then x else y)` | `⊢ P y` |

**R6 · `simp [hc]` on a conjunction** changes the **goal**: every part that is true is removed. `x ≤ x`
and `x = x` become `True`, a disjunction with a `True` side becomes `True`, `c` becomes `True` via `hc`, and
`True ∧ Q` becomes `Q`. If every part is true, `simp` **closes** the goal. Placeholders: `(c P : Prop)
(x y : Int) (hc : c)`.

| Before | After |
|---|---|
| `hc : c ⊢ P ∧ c ∧ x ≤ x ∧ (y = x ∨ x = x)` | `⊢ P` |

**R7 · `omega` with `h : ¬a ≤ b`** **closes** a linear goal that follows from a negated comparison. On
`Int`, `¬a ≤ b` is `b < a`, so `b ≤ a` follows. Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `h : ¬a ≤ b ⊢ b ≤ a` | no goals |

### Worked combinations (on the guide's `lowCap`, not the exercise's function)

**W1 · `by_cases`, then `simp [lowCap, h]` in each case.** Goal `lowCap x ≤ x`:

| Step | State after |
|---|---|
| start | `⊢ lowCap x ≤ x` |
| `by_cases h : x ≤ 10` | `h : x ≤ 10 ⊢ lowCap x ≤ x`, `h : ¬x ≤ 10 ⊢ lowCap x ≤ x` |
| `simp [lowCap, h]` | `case pos` closed (it became `x ≤ x`); `h : ¬x ≤ 10 ⊢ lowCap x ≤ x` is left |
| `simp [lowCap, h]` | `h : ¬x ≤ 10 ⊢ 10 ≤ x` |
| `omega` | no goals |

**W2 · no fact about the condition.** `simp [lowCap]` alone unfolds `lowCap` but leaves the `if`:

```lean-goal
⊢ lowCap x ≤ x
⊢ (if x ≤ 10 then x else 10) ≤ x
```

---

## Traps

- `by_cases h : c` must use the `if`'s condition literally (`a ≤ b` if the body says `if a ≤ b`). With
  `h : x < 11` or `h : 10 < x`, `simp [lowCap, h]` does not see that the condition `x ≤ 10` is decided: the
  `if` stays, as in W2, and Lean warns that `h` was unused.
- `simp [myMax, h]` needs both names: `myMax` to unfold the definition, `h` to choose the branch. Leaving
  out `h` gives W2.
- After `by_cases` there are two goals. A tactic on the next line works on `case pos` only; use `·` to focus
  each case, or `<;>` to run one tactic on both (TACTIC_STATES, "Structure").
- `simp` may leave a goal such as `b ≤ a` that is true only because of `h : ¬a ≤ b`. `simp` does not do
  arithmetic with `h`; `omega` does (R7). With `if a ≤ b` this happens in `case neg` only; with `if a < b`
  both cases leave one (`a ≤ b` from `h : a < b`, `b ≤ a` from `h : ¬a < b`).
- Do not add `omega` after a `simp` that already closed its case: Lean reports `No goals to be solved`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a function with two cases | `if c then x else y` | R1 |
| split a proof on a condition | `by_cases h : c` | R2 |
| focus one of the two cases | `· tac` | TACTIC_STATES |
| unfold a definition | `simp [f]` / `simp only [f]` | R3 |
| `if c then x else y` → `x` with `h : c` | `simp [h]` | R4 |
| `if c then x else y` → `y` with `h : ¬c` | `simp [h]` | R5 |
| unfold, pick the branch, drop trivial parts | `simp [f, h]` | R3–R6, W1 |
| linear goal from `h : ¬a ≤ b` | `omega` | R7 |
| see the state | infoview (cursor after a tactic) | |
