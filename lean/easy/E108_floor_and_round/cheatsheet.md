# E108 · Floor and round: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's floor `⌊x⌋` (`Int.floor`) and
`round` on the reals, the cast `↑` from `ℤ` back into `ℝ`, the lemmas `Int.floor_le`,
`Int.lt_floor_add_one`, `abs_sub_round`, `round_eq`, `Int.floor_eq_iff`, and `norm_num` on decimals.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`/`rw`/`norm_num`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℤ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket is a requirement on `α`
  (a *type class*). `[Ring α] [LinearOrder α] [FloorRing α]`: `α` has `+ - *`, a total order `≤`, and a
  floor function. `round` and `1 / 2` also need division and an order compatible with arithmetic:
  `[Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]`. `ℝ` and `ℚ` meet both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℤ` | Mathlib's real numbers and the integers. `x : ℝ` is a real; `⌊x⌋` and `round x` are in `ℤ` |
| `⌊x⌋` | `Int.floor x : ℤ`, the largest integer `≤ x`. Rounds toward −∞: `⌊-2.5⌋ = -3` |
| `round x` | the nearest integer, of type `ℤ`; ties go **up**: `round x = ⌊x + 1/2⌋`, so `round 0.5 = 1`, `round (-0.5) = 0` |
| `↑⌊x⌋`, `↑(round x)`, `↑z` | an integer cast into `ℝ` (`Int.cast`). Written `(⌊x⌋ : ℝ)` in source; Lean inserts it when an integer meets a real |
| `↑(-3)` | the integer `-3` cast into `ℝ`; `norm_num` turns it into the real `-3` |
| `2.6`, `-2.5` | decimal literals in `ℝ`: exact rationals (`26/10`), not floating point |
| `\|x - ↑(round x)\|` | absolute value of the rounding error, in `ℝ` |
| `case left`, `case right` | the two goals after splitting an `∧` |
| `case refine_1`, `refine_2`, `refine_3` | the three goals after `refine ⟨?_, ?_, ?_⟩`, in the order of the `∧` |
| `1 / 2` | real division: the exact real `0.5` (not integer division, since the type is `ℝ`) |

---

## Part 1 · `floor_bounds`

Statement: for every real `x`, `↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1`: the floor brackets `x` from below, within 1.
Split the `∧` (`constructor`, or the term `⟨_, _⟩`; TACTIC_STATES, "Structure"), then close each side with
one library lemma.

**R1 · `Int.floor_le`** **closes** the goal. Lemma: `Int.floor_le (a : α) : ↑⌊a⌋ ≤ a`. Placeholders:
`{α : Type} [Ring α] [LinearOrder α] [FloorRing α] (a : α)`. Use as `exact Int.floor_le a`.

| Before | After |
|---|---|
| `⊢ ↑⌊a⌋ ≤ a` | no goals |

**R2 · `Int.lt_floor_add_one`** **closes** the goal. Lemma: `Int.lt_floor_add_one (a : α) : a < ↑⌊a⌋ + 1`.
Same placeholders.

| Before | After |
|---|---|
| `⊢ a < ↑⌊a⌋ + 1` | no goals |

---

## Part 2 · `round_error`

Statement: `|x - ↑(round x)| ≤ 1 / 2`: rounding moves a real by at most one half. This is one library lemma.

**R3 · `abs_sub_round`** **closes** the goal. Lemma: `abs_sub_round (a : α) : |a - ↑(round a)| ≤ 1 / 2`.
Placeholders: `{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (a : α)`.

| Before | After |
|---|---|
| the goal below (a table cell cannot hold the bars `\|·\|`) | no goals |

```lean-goal
⊢ |a - ↑(round a)| ≤ 1 / 2
```

---

## Part 3 · `rounding_examples`

Statement: `⌊-2.5⌋ = -3`, `round 2.6 = 3`, `round (1/2) = 1`, as one `∧` of three equations in `ℤ`. Split it
into three goals (`refine ⟨?_, ?_, ?_⟩`), then on every goal (`<;>`): turn `round` into a floor (R4), turn
the floor equation into two inequalities (R5), and check them numerically (R6). R7 does all three in one
call.

**R4 · `rw [round_eq]`** changes the **goal**. Lemma: `round_eq (a : α) : round a = ⌊a + 1 / 2⌋`.
Placeholders: `{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] (a : α)`,
`P : ℤ → Prop`.

| Before | After |
|---|---|
| `⊢ P (round a)` | `⊢ P ⌊a + 1 / 2⌋` |

**R5 · `rw [Int.floor_eq_iff]`** changes the **goal**. Lemma: `Int.floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1`
(`z : ℤ`, `a : α`): `z` is the floor exactly when `z ≤ a < z + 1`. `rw` with an `↔` replaces the left side
by the right. The floor must be on the left of `=`. Placeholders:
`{α : Type} [Ring α] [LinearOrder α] [FloorRing α] (a : α) (z : ℤ)`.

| Before | After |
|---|---|
| `⊢ ⌊a⌋ = z` | `⊢ ↑z ≤ a ∧ a < ↑z + 1` |

**R6 · `norm_num`** **closes** a numeric goal: it evaluates integer casts of numerals (`↑(-4)` → `-4`), reads
decimals as exact rationals, and decides `≤`, `<`, `∧` between them.

| Before | After |
|---|---|
| `⊢ ↑(-4) ≤ -3.2 ∧ -3.2 < ↑(-4) + 1` | no goals |

**R7 · `norm_num [round_eq, Int.floor_eq_iff]`** **closes** the goal: the listed lemmas are added to the
rewrite set, so it does R4, R5 and R6 in one call.

| Before | After |
|---|---|
| `⊢ round 0.7 = 1` | no goals |

**W1: a floor of a negative decimal, step by step** (R5, then R6). `⌊·⌋` rounds toward −∞:

```lean-goal
⊢ ⌊-0.3⌋ = -1
⊢ ↑(-1) ≤ -0.3 ∧ -0.3 < ↑(-1) + 1
```

**W2: a round, step by step** (R4, R5, R6):

```lean-goal
⊢ round 3.2 = 3
⊢ ⌊3.2 + 1 / 2⌋ = 3
⊢ ↑3 ≤ 3.2 + 1 / 2 ∧ 3.2 + 1 / 2 < ↑3 + 1
```

**W3: ties go up, also below zero.** `round (-1/2) = ⌊-1/2 + 1/2⌋ = ⌊0⌋ = 0`, closed by R7.

**W4: several values at once.** `refine ⟨?_, ?_⟩ <;> norm_num [round_eq, Int.floor_eq_iff]` splits

```lean-goal
⊢ ⌊0.5⌋ = 0 ∧ round 0.4 = 0
```

into two goals and closes both with R7.

**W5: `simp` stops, `norm_num` finishes.** `simp [Int.floor_eq_iff]` applies R5 and simplifies the casts,
but cannot compare decimals:

```lean-goal
⊢ ⌊3.7⌋ = 3
⊢ 3 ≤ 3.7 ∧ 3.7 < 3 + 1
```

---

## Traps

- `⌊·⌋` rounds toward −∞, not toward 0: `⌊-2.5⌋ = -3`. C's `(int)x` truncates toward 0 and would give
  `-2`; Lean's `⌊·⌋` is the mathematical floor.
- Mathlib's `round` sends ties **up** (`round 0.5 = 1`, `round (-0.5) = 0`, `round 2.5 = 3`), unlike IEEE
  754 round-half-to-even (`2.5 → 2`).
- `rw [Int.floor_eq_iff]` fails on `round x = n`: there is no `⌊·⌋` yet. Apply `round_eq` (R4) first.
- `simp` cannot decide `3 ≤ 3.7` on decimals; use `norm_num` (W5).
- In this Mathlib version `norm_num` also evaluates `⌊q⌋` and `round q` for a numeral `q` by itself, so
  plain `norm_num` closes Part 3 too. The R4 → R5 → R6 route explains why the values are right and works
  for any lemma set.
- The cast matters: `(⌊x⌋ : ℝ) ≤ x` compares reals. Without the `↑`, `⌊x⌋ ≤ x` would not type-check
  (`ℤ` vs `ℝ`); Lean inserts the cast because the statement mentions `x : ℝ`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B` / `A ∧ B ∧ C` | `constructor`, `⟨_, _⟩` / `refine ⟨?_, ?_, ?_⟩` | TACTIC_STATES |
| `↑⌊a⌋ ≤ a` | `exact Int.floor_le a` | R1 |
| `a < ↑⌊a⌋ + 1` | `exact Int.lt_floor_add_one a` | R2 |
| `\|a - ↑(round a)\| ≤ 1 / 2` | `exact abs_sub_round a` | R3 |
| `round a → ⌊a + 1 / 2⌋` | `rw [round_eq]` | R4 |
| `⌊a⌋ = z → ↑z ≤ a ∧ a < ↑z + 1` | `rw [Int.floor_eq_iff]` | R5 |
| decimals and integer casts | `norm_num` | R6 |
| a concrete floor or round value | `norm_num [round_eq, Int.floor_eq_iff]` | R7 |
| same tactic on every goal | `t <;> u` | TACTIC_STATES |
| see the state | infoview | |
