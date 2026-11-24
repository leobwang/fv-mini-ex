# E080 · Mutual recursion: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl`, `exact`, `simp`, `rw`, `induction`, and
recursive theorems (E048: a theorem that calls itself on a smaller argument from a `match` arm). **New here:**
functions defined by mutual recursion (`mutual … end`), unfolding them one step at a time, Boolean negation
`!` and Boolean equality `==`, and the core lemmas `Bool.not_not`, `Nat.add_mod_right`, `Nat.mul_mod_right`,
`BEq.rfl`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, `P : Bool → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `!b` | Boolean negation of `b : Bool` (`!true = false`). Not `¬`, which negates a `Prop` |
| `!!b` | `!(!b)`; the infoview prints `P !!b` without parentheses |
| `a == b` | the `Bool` test "is `a` equal to `b`" (type class `BEq`); `true` or `false`, not a `Prop` |
| `isEven n = (n % 2 == 0)` | an equation between two `Bool`s; the parentheses group the `==` |
| `x % z` | remainder of `x` divided by `z` on `Nat` |
| `2 * n % 2` | `(2 * n) % 2`: `*` and `%` have the same precedence and group to the left |
| `true`, `false` | the two values of `Bool`; `b = true` is a `Prop` saying the test `b` succeeds (not `True`, the proposition) |
| `case zero`, `case succ` | the two goals after `induction n with` (R1) |
| `n✝ n : Nat` | after `match n with … \| n + 2 => …` the arm's new `n` shadows the old one, which is printed `n✝` and unusable |
| `case refine_3` | the label of the third `?_` goal after `refine match …` |

## Mutual recursion in one paragraph

A `mutual … end` block defines several functions at once, and each body may call any of them. Lean accepts
the block when every call is on a structurally smaller argument: `isEven (n + 1)` calls `isOdd n`, and `n` is
smaller than `n + 1`. Each function still gets one equation per pattern, which `simp only [f]` and `rw [f]`
use: `isEven 0 = true`, `isEven (n + 1) = isOdd n`, `isOdd 0 = false`, `isOdd (n + 1) = isEven n`. An
equation applies only where the argument literally has the pattern's shape (`0` or `_ + 1`).

---

## Part 1 · `isEven_not_odd`

Statement: `isEven n = !isOdd n` for all `n`. Ordinary induction: in the step, one unfolding of each function
turns `isEven (k + 1) = !isOdd (k + 1)` into `isOdd k = !isEven k`, and `ih : isEven k = !isOdd k` turns the
right side into `!!isOdd k`.

**R1 · `induction n with | zero => … | succ k ih => …`** changes the **goal list and the context**: two goals,
`n` replaced by `0` and by `k + 1`, with `ih : P k` in the second. In the exercise the arms hold their proofs
(`| zero => rfl`). Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `k : Nat, ih : P k ⊢ P (k + 1)` |

**R2 · `rfl`** **closes** an equation whose two sides compute to the same value. At a literal argument every
mutual function evaluates, and so do `%` and `==` on numerals: `r1 0` is `false`, and `0 % 3 == 1` is `false`.
It closes `isEven 0 = !isOdd 0`, `isEven 0 = (0 % 2 == 0)` and `isEven 1 = (1 % 2 == 0)`.

| Before | After |
|---|---|
| `⊢ r1 0 = (0 % 3 == 1)` | no goals |

**R3 · `simp only [f, g]`** changes the **goal**: every `f (k + 1)` and `g (k + 1)` becomes the right side of its
equation. Name every function you want unfolded; `simp only [r0]` leaves `r1 (k + 1)` alone. Placeholders:
`(k : Nat) (P : Bool → Bool → Prop)`, the guide's mutual triple `r0, r1, r2 : Nat → Bool`.

| Before | After |
|---|---|
| `⊢ P (r0 (k + 1)) (r1 (k + 1))` | `⊢ P (r2 k) (r0 k)` |

**R4 · `Bool.not_not`** changes the **goal**. The lemma is `Bool.not_not (b : Bool) : (!!b) = b`. `simp` uses
it by itself. Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `⊢ P !!b` | `⊢ P b` |

**W1 (on `up, dn : Nat → Nat`, `up (n + 1) = dn n + 1`, `dn (n + 1) = up n + 1`):** `up n = n ∧ dn n = n` by
R1; the `zero` case is `⟨rfl, rfl⟩` (R2 twice); the `succ` case is `simp [up, dn, ih]`: R3, then `rw` with
`ih`, then arithmetic. The same `simp [f, g, ih]` with R4 among `simp`'s own lemmas is Part 1's step.

---

## Part 2 · `isEven_mod`

Statement: `isEven n = (n % 2 == 0)`. Unfolding `isEven` then `isOdd` takes `n + 2` back to `n`, so the
theorem recurses on `n` with the cases `0`, `1`, `n + 2` (as in E048) and calls itself at `n`. On the right,
`(n + 2) % 2` equals `n % 2`.

**R5 · `match n with | 0 => … | 1 => … | m + 2 => …`** changes the **goal list**: one goal per pattern. In the
guide it is written `refine match n with … => ?_` so the cases appear as goals; after `:=` you may write the
`match` in term mode, with `rfl` or `by …` in each arm. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `⊢ P 1`, `n m : Nat ⊢ P (m + 2)` |

**R6 · `rw [f]`** changes the **goal**: it uses one equation of `f` once, at the first match. `m + 2` is
`(m + 1) + 1`, so `rw [r0]` gives `r2 (m + 1)` and stops; list the next function to keep going
(`rw [r0, r2]` reaches `r1 m`). Placeholders: `(m : Nat) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (r0 (m + 2))` | `⊢ P (r2 (m + 1))` |

**R7 · `rw [thm m]`** changes the **goal**: the theorem's own statement at the smaller `m`, `f m = v m`, used as
a rewrite rule from inside the case `m + 2`. Placeholders: `(f : Nat → Nat)`, theorem
`viaSelf … (n : Nat) : f n = n % 2`; the step is `rw [viaSelf f h0 h1 hs m]`.

| Before | After |
|---|---|
| `n m : Nat ⊢ f m = (m + 2) % 2` | `⊢ m % 2 = (m + 2) % 2` |

**R8 · `Nat.add_mod_right`** changes the **goal**. The lemma is `Nat.add_mod_right (x z : Nat) : (x + z) % z = x % z`.
After it the two sides of an equation are often identical, and `rw` closes the goal by `rfl` on its own.
Placeholders: `(x : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((x + 2) % 2)` | `⊢ P (x % 2)` |

**W2 (on the triple `r0 → r2 → r1 → r0`, three steps back):** `r0 n = (n % 3 == 0)` by R5 with a third base
case `2`, R2 for `0, 1, 2`, then in the case `m + 3`:

```lean-goal
⊢ r0 (m + 3) = ((m + 3) % 3 == 0)
⊢ r0 m = ((m + 3) % 3 == 0)
⊢ (m % 3 == 0) = ((m + 3) % 3 == 0)
```

after `rw [r0, r2, r1]` (R6 three times) and `rw [r0_mod m]` (R7); `rw [Nat.add_mod_right]` (R8) makes both
sides equal and closes it.

---

## Part 3 · `isOdd_double_add_one`

Statement: `isOdd (2 * n + 1) = true`. `2 * n + 1` has the shape `_ + 1`, so one unfolding gives
`isEven (2 * n)`. That does not unfold further (`2 * n` is not `0` or `_ + 1`), so use Part 2's theorem,
then `2 * n % 2 = 0` and `(0 == 0) = true`.

The first step is R3 (`simp only [isOdd]`), the second `rw` with a proved theorem (TACTIC_STATES `rw [h]`;
no argument is needed, `rw` finds it).

**R9 · `Nat.mul_mod_right`** changes the **goal**. The lemma is `Nat.mul_mod_right (m n : Nat) : m * n % m = 0`:
the multiplier `m` is on the left of `*`. Placeholders: `(m n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (m * n % m)` | `⊢ P 0` |

**R10 · `BEq.rfl`** changes the **goal**. The lemma is `BEq.rfl {a : α} : (a == a) = true`, for any type `α`
with a `BEq` test that is reflexive (`[ReflBEq α]`; `Nat` and `Bool` qualify). Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a == a)` | `⊢ P true` |

**W3 (on `r1 (3 * n + 1) = true`):** `simp only [r1]`, `rw [r0_mod]`, R9, R10 pass through

```lean-goal
⊢ r1 (3 * n + 1) = true
⊢ r0 (3 * n) = true
⊢ (3 * n % 3 == 0) = true
⊢ (0 == 0) = true
```

and `simp [r1, r0_mod]` does all four steps at once: R9 and R10 are `simp` lemmas.

---

## Traps

- `rw [isEven]` or `simp only [isEven]` on `isEven n` with a bare variable `n` fails ("Failed to rewrite using
  equation theorems", "simp made no progress"): no equation matches until `n` is split.
- `isEven (2 * n)` does not unfold: `2 * n` is not literally `_ + 1`. Use a theorem about `isEven` instead.
- Plain `induction` on `isEven_mod` gives `ih` at `k`, but `isEven (k + 1)` unfolds to `isOdd k`, which `ih`
  does not mention. Two unfoldings are needed to get back to `isEven`, hence cases `0, 1, n + 2` (R5).
- `rw [isEven]` unfolds one step only; `simp only [isEven, isOdd]` unfolds as far as the shapes allow. Either
  works in Part 2.
- In a term-mode `match n with | n + 2 => …`, the old `n` becomes `n✝`. Call the theorem on the new `n`.
- `!` is Boolean, `¬` is propositional: `isEven n = !isOdd n` is an equation in `Bool`, not `isEven n ↔ ¬ …`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `n` | `induction n with \| zero => … \| succ k ih => …` | R1 |
| base case at a literal | `rfl` | R2 |
| unfold `f (k + 1)`, `g (k + 1)` | `simp only [f, g]` | R3 |
| `!!b → b` | `Bool.not_not` (a `simp` lemma) | R4 |
| step case of Part 1 | `simp [isEven, isOdd, ih]` | R3, R4 |
| cases `0`, `1`, `n + 2` | `match n with \| 0 => … \| 1 => … \| n + 2 => …` | R5 |
| unfold exactly one step | `rw [f]` | R6 |
| use the statement at a smaller `n` | `rw [thm n]` | R7 |
| `(x + z) % z → x % z` | `rw [Nat.add_mod_right]` | R8 |
| `m * n % m → 0` | `rw [Nat.mul_mod_right]` | R9 |
| `(a == a) → true` | `rw [BEq.rfl]` | R10 |
| unfold, then a proved theorem, then finish | `simp [f, thm]` | R3, R9, R10 |
| see the state | infoview | |
