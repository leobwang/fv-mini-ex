# E094 · interval_cases: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular E031, which split `n` into its values by hand:
`have : n = 0 ∨ n = 1 := by omega; rcases this with rfl | rfl`.
**New here:** Mathlib's tactic `interval_cases`, which does that split for any bounded integer variable, and
the closers `simp_all` and `norm_num` for the concrete goals it leaves.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P`, `Q` are "the rest of your goal / hypothesis" (`P Q : ℕ → Prop`). The step changes only what sits
  inside `P (…)`, wherever that is in a larger goal.
- A hypothesis `g` in an example only finishes it: it shows what the goal became.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | natural numbers `0, 1, 2, …`; every `n : ℕ` satisfies `0 ≤ n` |
| `ℤ` | integers, negative ones included; no built-in lower bound |
| `n ^ 2` | `n` squared (`^` with a natural-number exponent) |
| `(-2) ^ 3 - -2` | $(-2)^3 - (-2)$ in `ℤ`. The parentheses in `(-2) ^ 3` are kept because `-2 ^ 3` would mean $-(2^3)$; `- -2` subtracts $-2$ |
| `-1 * -1` | $(-1)\cdot(-1)$: `*` binds looser than the minus sign of a literal, so no parentheses are printed (W2) |
| `case «2»`, `case «-1»` | the goal `interval_cases` made for the value `2`, resp. `-1` |
| `n : ℕ` still in the context after the split | the variable is left over but appears nowhere else: ignore it |
| `h1 : 1 ≤ 3` | a bound hypothesis after substitution: true, and useless from now on |
| `h : 3 ^ 2 = 16` | a hypothesis after substitution that is false: this branch is impossible |

---

## Part 1 · `ic_sq`

Statement: for `n : ℕ` with `2 ≤ n ≤ 5` and `n ^ 2 = 16`, `n = 4`. Split `n` into `2, 3, 4, 5`. In branches
`2, 3, 5` the hypothesis `n ^ 2 = 16` became a false numeral equation; in branch `4` the goal is `4 = 4`.

**R1 · `interval_cases n`** changes the **goal list and the context**. It finds a lower bound (`c ≤ n`, `c < n`)
and an upper bound (`n ≤ d`, `n < d`) on `n` among the hypotheses, and makes one goal per value in between. In
each goal `n` is replaced by that literal in the goal and in every hypothesis. Placeholders:
`(P Q : ℕ → Prop) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 3) (hq : Q n)`.

| Before | After |
|---|---|
| `h1 : 1 ≤ n, h2 : n ≤ 3, hq : Q n ⊢ P n` | `h1 : 1 ≤ 1, h2 : 1 ≤ 3, hq : Q 1 ⊢ P 1` |
| | `h1 : 1 ≤ 2, h2 : 2 ≤ 3, hq : Q 2 ⊢ P 2` |
| | `h1 : 1 ≤ 3, h2 : 3 ≤ 3, hq : Q 3 ⊢ P 3` |

**R2 · `t <;> u`** changes the **goal list**: it runs `t`, then `u` on every goal `t` produced (TACTIC_STATES,
"Structure"). After `interval_cases` that is one finishing tactic for all branches. If `u` fails on any branch,
the whole line fails.

| Before | After |
|---|---|
| `⊢ P n` | no goals (`interval_cases n <;> exact g _ hq`) |

**R3 · `simp_all`, false hypothesis** **closes** the goal. `simp_all` simplifies every hypothesis and the goal,
using each to simplify the others. A hypothesis that evaluates to `False` proves any goal. Placeholders:
`(G : Prop)`, a numeral hypothesis `h`.

| Before | After |
|---|---|
| `h : 3 ^ 2 = 16 ⊢ G` | no goals |
| `h : 2 ^ 3 - 2 = 0 ⊢ G` (in `ℤ`) | no goals |

**R4 · `simp_all`, true goal** **closes** a goal of literal equations once evaluated: `0 = -1` becomes
`False`, `0 = 0` becomes `True`, so the disjunction is `True`. True hypotheses like `1 ≤ 3` are simplified to
`True` and dropped, so the same call works whatever else the branch holds.

| Before | After |
|---|---|
| `⊢ 0 = -1 ∨ 0 = 0 ∨ 0 = 1` | no goals |

So every branch of `ic_sq` closes with R3 or R4: one `simp_all` after R2.

---

## Part 2 · `ic_cube`

Statement: for `n : ℕ` with `n < 4`, `n ^ 3 < 30`. Only an upper bound is given. Every branch has a true,
concrete goal (`0 ^ 3 < 30`, …, `3 ^ 3 = 27 < 30`) and no hypothesis to kill.

**R5 · `interval_cases n` with only an upper bound** changes the **goal list and the context**. On `ℕ` the
lower bound `0` is built in. Placeholders: `(P : ℕ → Prop) (n : ℕ) (h : n < 3)`.

| Before | After |
|---|---|
| `h : n < 3 ⊢ P n` | `h : 0 < 3 ⊢ P 0` |
| | `h : 1 < 3 ⊢ P 1` |
| | `h : 2 < 3 ⊢ P 2` |

**R6 · `norm_num`** **closes** a numeric equality or inequality between literals (`^`, `*`, `+`, `-`, `<`,
`≤`, `≠`). It fails if the statement is false.

| Before | After |
|---|---|
| `⊢ 2 ^ 3 < 30` | no goals |

**W1.** `n * n ≤ 9` with `1 ≤ n ≤ 3`: R1 leaves three concrete goals, `all_goals norm_num` (R6) closes them:

```lean-goal
⊢ 1 * 1 ≤ 9
⊢ 2 * 2 ≤ 9
⊢ 3 * 3 ≤ 9
```

**W3.** A bound not of the form `n < d` (here `2 * n < 7`) is not found: R1 fails with "could not find upper
bound on n". Derive the plain bound first, `have hn : n < 4 := by omega`, then `interval_cases n <;> norm_num`.

---

## Part 3 · `ic_int`

Statement: for `x : ℤ` with `-2 ≤ x < 3` and `x ^ 3 - x = 0`, `x = -1 ∨ x = 0 ∨ x = 1`. Five branches
`-2, -1, 0, 1, 2`: in `-2` and `2` the hypothesis is false (`h : (-2) ^ 3 - -2 = 0` evaluates to `-6 = 0`, `h : 2 ^ 3 - 2 = 0` to `6 = 0`; R3); in the other three the
disjunction is true (R4).

**R7 · `interval_cases x` on `ℤ`** changes the **goal list and the context**. It needs both bounds from the
context: `ℤ` has no smallest element. Placeholders: `(P : ℤ → Prop) (x : ℤ) (h1 : -1 ≤ x) (h2 : x < 2)`.

| Before | After |
|---|---|
| `h1 : -1 ≤ x, h2 : x < 2 ⊢ P x` | `h1 : -1 ≤ -1, h2 : -1 < 2 ⊢ P (-1)` |
| | `h1 : -1 ≤ 0, h2 : 0 < 2 ⊢ P 0` |
| | `h1 : -1 ≤ 1, h2 : 1 < 2 ⊢ P 1` |

**W2.** `x ≠ 0` from `-1 ≤ x < 2` and `h : x * x = 1`: after R7 the middle branch is impossible, and
`all_goals simp_all` (R3, R4) closes all three:

```lean-goal
⊢ -1 ≠ 0
⊢ 0 ≠ 0
⊢ 1 ≠ 0
```

In the middle one `⊢ 0 ≠ 0` is false; it closes only because `h : 0 * 0 = 1` is false too.

---

## Traps

- `ℤ` without a lower bound: `interval_cases x` fails with "could not find lower bound on x". On `ℕ` only the
  upper bound is needed.
- The bounds must be hypotheses about the variable itself (`n < 4`, `2 ≤ n`). From `2 * n < 7` derive `n < 4`
  with `omega` first (W3).
- `norm_num` does not look at hypotheses unless told to, so it cannot close a branch whose only problem is a
  false hypothesis: use `simp_all` there.
- Do not write `norm_num at h ⊢`: on a branch where simplifying `h` to `False` already closed the goal, the
  `⊢` part fails with "No goals to be solved".
- `t ; u` runs `u` on the first goal only. After `interval_cases`, use `<;>` or `all_goals`.
- `decide` (and its lemma forms), `nlinarith`, `grind` are banned: `revert h; revert n; decide` would check all
  values without `interval_cases`, which is the point of the exercise.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per value of a bounded `n : ℕ` | `interval_cases n` | R1, R5 |
| the same for `x : ℤ` (both bounds required) | `interval_cases x` | R7 |
| finish every branch the same way | `interval_cases n <;> tac` | R2 |
| branch with a false hypothesis | `simp_all` | R3 |
| branch whose goal is a true literal (dis)equation | `simp_all` or `norm_num` | R4, R6 |
| numeric inequality between literals | `norm_num` | R6 |
| bound in the wrong shape | `have hn : n < d := by omega` | W3 |
| see the branches | infoview after `interval_cases` | |
