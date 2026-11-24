# E063 · Casts: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact` (E003), `have` (E021) and
`omega` (E011). **New here:** Mathlib's real numbers `ℝ`, the cast `Nat.cast : ℕ → ℝ` (printed `↑`),
and the cast tactics `push_cast`, `norm_cast`, `exact_mod_cast`. `ring` (also met in E034) on real numbers.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Casts in one paragraph

`ℕ` and `ℝ` are different types, and `ℕ` is not a subset of `ℝ` in Lean. Writing `(m : ℝ)` for
`m : ℕ` inserts the function `Nat.cast m`, printed `↑m`. Lean inserts it by itself whenever an `ℕ` stands
where an `ℝ` is expected (a *coercion*). Where the cast sits
matters: `((a - b : ℕ) : ℝ)` first subtracts in `ℕ` (the inner `: ℕ`), then casts the result, printed
`↑(a - b)`; `(a : ℝ) - (b : ℝ)` casts first and subtracts in `ℝ`, printed `↑a - ↑b`. Mathlib has a
family of *cast lemmas*, each saying that `↑` commutes with one operation: `↑(m + n) = ↑m + ↑n`,
`↑(m * n) = ↑m * ↑n`, `↑(m ^ k) = ↑m ^ k`, `↑(1 : ℕ) = 1`, and that it preserves and reflects order and
equality (`↑m < ↑n ↔ m < n`, `↑m = ↑n ↔ m = n`). The three cast tactics apply this family for you:
`push_cast` uses it left to right (casts move inward), `norm_cast` right to left (casts move outward
and disappear), `exact_mod_cast h` normalises both `h` and the goal with `norm_cast` and then does
`exact`. The same works for casts into `ℤ`, `ℚ`, `ℂ`.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `↑m` with `m : ℕ` | `Nat.cast m : ℝ`, the number `m` as a real (written `(m : ℝ)` in source) |
| `↑(m * (n + 1))` | the ℕ product computed first, then cast once |
| `↑m * (↑n + 1)` | the casts multiplied and added in ℝ |
| `↑(a - b)` | ℕ subtraction, then cast: it is `0` when `a < b` |
| `↑a - ↑b` | ℝ subtraction of the casts: negative when `a < b` |
| `3 < ↑n` | `(3 : ℝ) < ↑n`: the numeral `3` is a real number, printed without `↑`; the cast tactics still match it with `(3 : ℕ)` (R5) |
| `↑n ^ 2` | `(↑n) ^ 2`: `↑` binds tighter than `^` |

---

## Part 1 · `cast_poly`

Statement: `↑(n * (n + 1)) = ↑n ^ 2 + ↑n`. The left side is one cast of a ℕ expression, the right side
ℝ arithmetic on `↑n`. Push the cast down to `n` (R1); what is left is an identity of real-number
algebra in the unknown `↑n` (R2).

**R1 · `push_cast`** changes the **goal**: every `↑` of a sum, product, power or numeral is pushed
down to the variables, `↑((m + 1) * n)` → `(↑m + 1) * ↑n`. It rewrites with the cast lemmas left to right;
`push_cast at h` does the same to `h`. Placeholders: `(m n : ℕ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ↑((m + 1) * n)` | `⊢ P ((↑m + 1) * ↑n)` |

**R2 · `ring`** **closes** an equation that holds in every commutative ring. After R1 each `↑n` is an
atom (an unknown real number) to `ring`, so `↑n * (↑n + 1) = ↑n ^ 2 + ↑n` is ordinary algebra.
Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ (↑m + 1) * ↑n = ↑m * ↑n + ↑n` | no goals |

**W1:** push, then `ring`:

```lean-goal
⊢ ↑(m + n * m) = ↑m * (1 + ↑n)
⊢ ↑m + ↑n * ↑m = ↑m * (1 + ↑n)
```

## Part 2 · `lt_of_real_lt`

Statement: from `h : ↑m < ↑n` (in ℝ) prove `m < n` (in ℕ). The order on ℕ is the order on its casts,
so `h` is the goal "up to casts" (R3). Alternatively strip the casts off `h` (R4): `h` becomes `m < n`,
which is the goal, and `norm_cast at h` then closes the goal by itself.

**R3 · `exact_mod_cast h`** **closes** a ℕ goal from a hypothesis about the casts: it removes the casts
from `h` (and the goal) with the cast lemmas right to left, then does `exact`. Placeholders:
`(m n : ℕ) (h : ↑m + 1 ≤ ↑n)`.

| Before | After |
|---|---|
| `h : ↑m + 1 ≤ ↑n ⊢ m + 1 ≤ n` | no goals |

**R4 · `norm_cast at h`** changes the **context**: the casts in `h` are pulled outward and dropped.
`↑m + 1 ≤ ↑n` becomes `↑(m + 1) ≤ ↑n`, then `m + 1 ≤ n`. Plain `norm_cast` does the same to the goal.
If the cleaned `h` is exactly the goal, `norm_cast at h` also closes the goal (it tries `assumption`), and
a following `exact h` fails with "No goals to be solved". Placeholders: `(m n : ℕ) (G : Prop)`.

| Before | After |
|---|---|
| `h : ↑m + 1 ≤ ↑n ⊢ G` | `h : m + 1 ≤ n ⊢ G` |

**W4:** bring a real hypothesis down to ℕ with R3 inside a `have`, then `omega` (which works on ℕ, not ℝ):

```lean-goal
⊢ False
```

## Part 3 · `real_le_of_le`

Statement: from `h : a ≤ b` (in ℕ) prove `↑a ≤ ↑b` (in ℝ). The opposite direction of Part 2, with the
same tactic (R5).

**R5 · `exact_mod_cast h`** **closes** a goal about casts from a ℕ hypothesis: it normalises the goal to
`m = n + 1` and finds `h`. Numerals count: `(1 : ℝ)` in the goal is matched with `(1 : ℕ)`.
Placeholders: `(m n : ℕ) (h : m = n + 1)`.

| Before | After |
|---|---|
| `h : m = n + 1 ⊢ ↑m = ↑n + 1` | no goals |

## Part 4 · `real_sub_of_le`

Statement: from `h : b ≤ a` prove `↑(a - b) = ↑a - ↑b`. In ℕ, `a - b` truncates at 0 (`2 - 5 = 0`), in
ℝ it does not, so the cast does not commute with `-` in general. With `h` it does: hand `h` to
`push_cast` (R6). It leaves `↑a - ↑b = ↑a - ↑b` open (`push_cast` does not try `rfl` on what it
produces), which R2 closes.

**R6 · `push_cast [hb]`** changes the **goal**: as R1, and it may also use `hb`. The subtraction cast
lemma has the side condition `b ≤ a`; `push_cast` uses it only when it can prove that condition, and
`[hb]` supplies the proof. Placeholders: `(a b : ℕ) (hb : b ≤ a) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `hb : b ≤ a ⊢ P ↑(a - b)` | `⊢ P (↑a - ↑b)` |

**W2:** a subtraction inside a sum, with `hcb : c ≤ b`; then `ring`:

```lean-goal
⊢ ↑(a + (b - c)) = ↑a + ↑b - ↑c
⊢ ↑a + (↑b - ↑c) = ↑a + ↑b - ↑c
```

## Part 5 · `real_pos_of_pos`

Statement: from `h : 0 < n` (in ℕ) prove `(0 : ℝ) < ↑n`. Same as Part 3: the real `0` is read as the cast
of the natural `0`, so R5 applies.

**W3:** a numeral other than `0`, `h : 3 < n`:

```lean-goal
⊢ 3 < ↑n
```

---

## Traps

- `↑(a - b) = ↑a - ↑b` needs `b ≤ a`: ℕ subtraction truncates at 0 (`2 - 5 = 0`), ℝ subtraction does not.
  Plain `push_cast` leaves `↑(a - b)` unchanged (only a linter warning "'push_cast' tactic does nothing");
  pass the hypothesis, `push_cast [h]`.
- `((n * (n + 1) : ℕ) : ℝ)` and `((n : ℝ) * (n + 1))` print differently (`↑(n * (n + 1))` vs `↑n * (↑n + 1)`)
  and are different terms. `rw` and `exact` see the difference; `push_cast` removes it.
- `ring` and `omega` do not move casts. `ring` treats `↑(n * (n + 1))` as one unknown, so call `push_cast`
  first. `omega` does not work in ℝ at all: bring the fact down to ℕ first (W4).
- `push_cast` can leave a goal whose two sides are identical; it does not close it. Follow it with `ring`
  or `rfl`. When it does close the goal, a tactic after it fails with "No goals to be solved".
- `norm_cast at h` and `norm_cast` close the goal themselves when the cleaned-up `h` (or any hypothesis)
  matches it, e.g. `norm_cast at h` with `h : ↑m < ↑n` and goal `m < n`. Do not add `exact h` after it.
- `exact_mod_cast h` closes the goal or fails; it never leaves a partial goal. If it fails, compare the
  shapes: `norm_cast at h` and `norm_cast` on the goal show what each side normalises to.
- The cast lemmas for `<`, `≤`, `-` and positivity are BANNED here: the point is to let the tactics find them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `↑(ℕ expression)` → ℝ expression in `↑variables` | `push_cast` | R1 |
| real algebra after pushing | `ring` | R2 |
| ℕ goal from a hypothesis about casts | `exact_mod_cast h` | R3 |
| strip casts from a hypothesis | `norm_cast at h` | R4 |
| strip casts from the goal | `norm_cast` | R4 |
| goal about casts from a ℕ hypothesis (numerals too) | `exact_mod_cast h` | R5 |
| `↑(a - b)` → `↑a - ↑b` | `push_cast [h]` with `h : b ≤ a` | R6 |
| ℕ arithmetic on a real fact | `have h' : … := by exact_mod_cast h`, then `omega` | W4 |
| see the state | infoview | |
