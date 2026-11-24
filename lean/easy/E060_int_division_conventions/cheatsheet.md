# E060 · Int division conventions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide` (E001), `rw` (E009), `simp` (E010),
`omega` (E011). **New here:** core Lean's integer division and remainder (`Int.ediv`, `Int.emod`), C-style
truncating division (`Int.tdiv`, `Int.tmod`), the two `Int → Nat` maps `Int.toNat` and `Int.natAbs`, and the
cast `↑` from `Nat` back to `Int`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Int → Prop` or `P : Nat → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `-9 / 4` | `(-9) / 4`, i.e. `Int.ediv (-9) 4`: prefix `-` binds tighter than `/` |
| `-9 % 4` | `Int.emod (-9) 4` |
| `-(2 * k + 1) / 2` | `(-(2 * k + 1)) / 2`: negate first, then divide |
| `-7` where the source says `(-7 : Int)` | the type ascription `( : Int)` is not printed; the literal is still an `Int` |
| `(-9).tdiv 4` | `Int.tdiv (-9) 4`, dot notation for a function in the `Int` namespace |
| `(-2).toNat`, `(-3).natAbs` | `Int.toNat (-2)`, `Int.natAbs (-3)`, both of type `Nat` |
| `↑n` | a `Nat` `n` cast into `Int` (`Int.ofNat n`, written `(n : Int)` in source) |
| `↑a.toNat` | `↑(a.toNat)`: first `toNat`, then cast back into `Int` |
| `↑(weekday d)` | the `Nat` result of `weekday d` cast into `Int`, so it can be compared with `d % 7` |

### The three conventions behind `/`, `%`, `tdiv`, `tmod`

For integers `a` and `b ≠ 0`, every division pairs a quotient `q` and a remainder `r` with `a = b * q + r`.
The conventions differ in which `(q, r)` they pick:

| Operation | Lean name | Rule for `r` | `-9`, `4` | `-7`, `2` | `7`, `-2` |
|---|---|---|---|---|---|
| `a / b`, `a % b` | `Int.ediv`, `Int.emod` (Euclidean) | `0 ≤ r < \|b\|` always | `-3`, `3` | `-4`, `1` | `-3`, `1` |
| `a.tdiv b`, `a.tmod b` | `Int.tdiv`, `Int.tmod` (truncation, C/Rust/Java) | `r` has the sign of `a` | `-2`, `-1` | `-3`, `-1` | `-3`, `1` |

For `b > 0`, Euclidean `/` is the floor `⌊a / b⌋`; for `b < 0` it rounds up. Division by `0` is defined, not
an error: `a / 0 = 0` and `a % 0 = a`, so `a = 0 * (a / 0) + a % 0` still holds.

| Map `Int → Nat` | Meaning | `-5` | `5` |
|---|---|---|---|
| `x.toNat` (`Int.toNat x`) | `max x 0`: negatives clamp to `0` | `0` | `5` |
| `x.natAbs` (`Int.natAbs x`) | `\|x\|` | `5` | `5` |

---

## Part 1 · `div_floor`

Statement: `(-7 : Int) / 2 = -4`. Euclidean division rounds `-3.5` down to `-4`, not toward `0`.

**R1 · `decide`** **closes** a goal about concrete integers. `Int.ediv` is computable, so `decide` evaluates
both sides and checks they are equal.

| Before | After |
|---|---|
| `⊢ -9 / 4 = -3` | no goals |

## Part 2 · `mod_nonneg_lit`

Statement: `(-7 : Int) % 2 = 1`. The Euclidean remainder is never negative: `-7 = 2 * (-4) + 1`.

**R2 · `decide`** **closes** a literal `%` fact the same way.

| Before | After |
|---|---|
| `⊢ -9 % 4 = 3` | no goals |

## Part 3 · `tdiv_trunc`

Statement: `(-7 : Int).tdiv 2 = -3`. Truncation drops the fractional part of `-3.5`, rounding toward `0`.

**R3 · `decide`** on `Int.tdiv` / `Int.tmod` **closes** the goal. `Int.tmod a b` takes the sign of `a`.

| Before | After |
|---|---|
| `⊢ (-9).tdiv 4 = -2 ∧ (-9).tmod 4 = -1` | no goals |

## Part 4 · `div_by_zero`

Statement: `x / 0 + x % 0 = x` for every `x : Int`. `decide` cannot help: `x` is a variable. Rewrite each
operation with its by-zero lemma, then close `0 + x = x`.

**R4 · `rw [Int.ediv_zero]`** changes the **goal**. The lemma is `Int.ediv_zero (a : Int) : a / 0 = 0`.
Placeholders: `(a : Int) (P : Int → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a / 0)` | `⊢ P 0` |

**R5 · `rw [Int.emod_zero]`** changes the **goal**. The lemma is `Int.emod_zero (a : Int) : a % 0 = a`.
Placeholders: `(a : Int) (P : Int → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a % 0)` | `⊢ P a` |

**R6 · `simp`** **closes** `0 + a = a` with the simp lemma `Int.zero_add`. Placeholders: `(a : Int)`.

| Before | After |
|---|---|
| `⊢ 0 + a = a` | no goals |

## Part 5 · `toNat_natAbs`

Statement: `(-5 : Int).toNat = 0 ∧ (-5 : Int).natAbs = 5`. Both maps are computable, so `decide` closes the
whole conjunction at once (no need to split it).

**R7 · `Int.toNat`** with `decide` **closes** the goal. `toNat` returns `x` for `x ≥ 0` and `0` otherwise.

| Before | After |
|---|---|
| `⊢ (-2).toNat = 0` | no goals |

**R8 · `Int.natAbs`** with `decide` **closes** the goal. `natAbs` returns `|x|` as a `Nat`.

| Before | After |
|---|---|
| `⊢ (-3).natAbs = 3` | no goals |

## Part 6 · `neg_odd_div_two`

Statement: `(-(2 * k + 1)) / 2 = -k - 1` for every `k : Int`. The value `-(2k+1) / 2 = -k - 1/2` lies
between `-k - 1` and `-k`; floor picks `-k - 1` for every `k`. Truncation would give `-k` when `k ≥ 0`.

**R9 · `omega`** **closes** a linear goal over `Int` and `Nat`, including `/` and `%` by a numeral. It replaces
`e / 2` by an unknown `q` with `2 * q ≤ e < 2 * q + 2`, the Euclidean rule of R1. Placeholders: `(k : Int)`.

| Before | After |
|---|---|
| `k : Int ⊢ (2 * k + 1) / 2 = k` | no goals |

**W2.** The same shape with divisor 3, `-(3 * k + 1) / 3 = -k - 1`, is also one `omega`:

```lean-goal
⊢ -(3 * k + 1) / 3 = -k - 1
```

## Part 7 · `weekday` (a definition)

Statement: `weekday (d : Int) : Nat`, the day of the week of day `d` (Monday = 0 … Sunday = 6), correct for
negative `d`. You write the body. Take the Euclidean remainder by 7 (R2: it is in `0..6` even for negative
`d`) and turn it into a `Nat` with `Int.toNat` (R7). Since the remainder is never negative, `toNat` loses
nothing. `natAbs` would also type-check here, but `toNat` is the map that the lemma of R11 is about.

**W3** builds a function of the same kind, `lastDigit (n : Int) : Nat := (n % 10).toNat`.

## Part 8 · `weekday_spec`

Statement: `(weekday d : Int) = d % 7`: cast back into `Int`, `weekday d` is the Euclidean remainder. Unfold
`weekday`, establish `0 ≤ d % 7`, then rewrite the `toNat` away. Or unfold and hand it all to `omega`.

**R12 · `unfold f`** changes the **goal**: `f x` is replaced by `f`'s body with `x` substituted. Placeholders:
`sqNat (n : Int) : Nat := (n * n).toNat`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (sqNat n)` | `⊢ P (n * n).toNat` |

**R10 · `have h := Int.emod_nonneg a hb`** changes the **context**: it adds `h : 0 ≤ a % b`. The lemma is
`Int.emod_nonneg (a : Int) {b : Int} : b ≠ 0 → 0 ≤ a % b`; `b` is implicit (read off `hb`). For a literal
divisor, prove the side condition on the spot with `(by decide)`, since `decide` closes `(7 : Int) ≠ 0`. Then
Lean must know `b` before `decide` runs: write the fact's type, `have h : 0 ≤ a % 7 := Int.emod_nonneg a (by decide)`,
or use it where the expected type fixes `b` (as the argument of R11). Placeholders: `(a b : Int) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ a % b ⊢ G` |

**R11 · `rw [Int.toNat_of_nonneg ha]`** changes the **goal**. The lemma is
`Int.toNat_of_nonneg {a : Int} : 0 ≤ a → (a.toNat : Int) = a`: for a non-negative `a`, `toNat` followed by the
cast is the identity. Placeholders: `(a : Int) (ha : 0 ≤ a) (P : Int → Prop)`. Its conclusion
`↑a.toNat = a` can also close a goal directly (`exact Int.toNat_of_nonneg ha`), and Lean unfolds a definition
such as `weekday` by itself when it checks an `exact`.

| Before | After |
|---|---|
| `⊢ P ↑a.toNat` | `⊢ P a` |

**R13 · `omega`** also understands `toNat` and the `↑` cast, so it **closes** such goals without R10 or R11. It
does not unfold your definitions: `unfold` first (R12). Placeholders: `(a : Int) (h : 0 ≤ a)`.

| Before | After |
|---|---|
| `h : 0 ≤ a ⊢ ↑a.toNat = a` | no goals |

**W4: R10 then R11 on `a % 10`.**

```lean-goal
⊢ P ↑(a % 10).toNat
⊢ P (a % 10)
```

**W3: `unfold` then `omega`** on `(lastDigit n : Int) < 10`:

```lean-goal
⊢ ↑(lastDigit n) < 10
⊢ ↑(n % 10).toNat < 10
```

## Part 9 · `weekday_neg_one`

Statement: `weekday (-1) = 6`: the day before a Monday is a Sunday. `-1 % 7 = 6`.

**R14 · `decide`** **closes** a goal that applies a defined, computable function to literals: it evaluates
your `weekday` body. This works only once the body is written (a `sorry` body does not evaluate).

| Before | After |
|---|---|
| `⊢ sqNat (-3) = 9` | no goals |

---

## Traps

- `/` and `%` on `Int` are NOT C's. `-7 / 2 = -4` and `-7 % 2 = 1` in Lean; C, Rust and Java give `-3` and `-1`
  (that is `Int.tdiv`, `Int.tmod`).
- The Euclidean quotient is the floor only for a positive divisor: `7 / -2 = -3` and `7 % -2 = 1`.
- `-7 / 2` parses as `(-7) / 2`. `-(7 / 2)` is `-3`, a different number.
- Division by zero is not an error: `x / 0 = 0`, `x % 0 = x`. `decide` will not prove a statement with a free
  variable `x`; use the lemmas R4, R5.
- `weekday d` is a `Nat` and `d % 7` is an `Int`: the spec compares them via the cast `(weekday d : Int)`,
  printed `↑(weekday d)`. Without the cast the equation does not type-check.
- `have h := Int.emod_nonneg d (by decide)` fails with "Expected type must not contain metavariables": the
  divisor `b` is implicit and nothing fixes it yet. State the type: `have h : 0 ≤ d % 7 := …`.
- `omega` does not unfold definitions: a goal with `weekday` in it needs `unfold weekday` first.
- `decide` on `weekday (-1)` evaluates your definition: it fails while the body is `sorry`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a fact about literal `/`, `%`, `tdiv`, `toNat`, `natAbs` | `decide` | R1–R3, R7, R8 |
| `a / 0` → `0` | `rw [Int.ediv_zero]` | R4 |
| `a % 0` → `a` | `rw [Int.emod_zero]` | R5 |
| close `0 + a = a` | `simp` | R6 |
| linear goal with `/ n`, `% n`, `toNat`, `↑` | `omega` | R9, R13 |
| `0 ≤ a % n` for a literal `n ≠ 0` | `have h : 0 ≤ a % n := Int.emod_nonneg a (by decide)` | R10 |
| `↑a.toNat` → `a` given `0 ≤ a` | `rw [Int.toNat_of_nonneg ha]` | R11 |
| expose a definition's body | `unfold f` | R12 |
| a defined function on literals | `decide` | R14 |
| see the state | infoview | |
