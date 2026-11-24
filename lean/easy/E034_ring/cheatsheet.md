# E034 · ring: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular tactic mode, `rw [h]` (E009) and the `rfl`
pattern that substitutes a variable (E025, E030).
**New here:** the tactic `subst` (R3), and Mathlib. `import Mathlib` (the first line after the header) loads the number types `ℕ ℤ ℚ ℝ`
and Mathlib's tactics, among them `ring`. `ring` proves an equation that holds in **every** commutative
(semi)ring, i.e. one that follows from associativity, commutativity, distributivity and the laws of `0`, `1`
and `^` alone. It normalizes both sides to a sum of monomials with numeral coefficients and compares them.
It either closes the goal or fails; it never uses hypotheses from the context.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change. "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*); Lean shows it in the context as `inst✝ : CommRing α`. Each entry says
  which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means | Type it as |
|---|---|---|
| `ℕ` | Mathlib's name for `Nat`: `0, 1, 2, …`; a commutative **semiring** (no true `-`) | `\N` |
| `ℤ` | `Int`, the integers: a commutative ring | `\Z` |
| `ℚ` | the rationals: a commutative ring (in fact a field) | `\Q` |
| `ℝ` | the real numbers: a commutative ring (a field) | `\R` |
| `a ^ 2` | `a * a`; the exponent is a natural-number numeral | `^` |
| `2 * a * b` | `(2 * a) * b`: `*` groups to the left, `^` binds tighter than `*` | |
| `2` in `ℚ` | the numeral `2` of type `ℚ`, not a cast of the natural number `2` | |
| `x - y` in `ℤ ℚ ℝ` | true subtraction; `a ^ 2 - 2 * b * c` is `(a ^ 2) - ((2 * b) * c)` | |
| `inst✝ : CommRing α` | the instance from a bracket such as `[CommRing α]` or `[Add α]` in the guide's examples | |

---

## Part 1 · `square_sum`

Statement: for `a b : ℤ`, `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`. A pure identity of commutative rings:
expand the left side and collect terms. One `ring` (R1).

**R1 · `ring` in a commutative ring** **closes** the goal. Placeholders: `{α : Type} [CommRing α] (a b : α)`.
`[CommRing α]`: `α` has `0 1 + - *` and `^` by a natural number, `*` is commutative, and the ring laws hold;
`ℤ`, `ℚ`, `ℝ`, `ℂ` qualify.

| Before | After |
|---|---|
| `⊢ (a - b) * (a + b) = a ^ 2 - b ^ 2` | no goals |

## Part 2 · `cube_succ`

Statement: for `n : ℕ`, `(n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1`, the binomial expansion of the cube.
It uses only `+`, `*`, `^`, so it holds in every commutative semiring and `ring` closes it (R2).

**R2 · `ring` in a commutative semiring** **closes** the goal. Placeholders:
`{α : Type} [CommSemiring α] (n : α)`. `[CommSemiring α]`: like `CommRing` without subtraction; `ℕ`
qualifies (and every commutative ring does too).

| Before | After |
|---|---|
| `⊢ (n + 2) ^ 2 = n ^ 2 + 4 * n + 4` | no goals |

**W3.** The same tactic on `ℕ` and `ℚ`: `(n + 1) * (n + 1) = n * n + 2 * n + 1` for `n : ℕ` and
`(x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2` for `x y : ℚ` are each one `ring`.

## Part 3 · `with_hyp`

Statement: for `a b c : ℚ` with `h : a = b + c`, `a ^ 2 - 2 * b * c = b ^ 2 + c ^ 2`. This is **not** an
identity in `a, b, c` (try `a = b = c = 1`), so `ring` alone fails: it never reads `h`. First replace `a` by
`b + c` (R3, or R4), then the goal is an identity in `b, c` and `ring` closes it (R1).

**R3 · `subst h`** changes the **context and the goal**: for `h : a = e` with `a` a local variable not
occurring in `e`, it replaces `a` by `e` everywhere and removes both `a` and `h`. It works the same for
`h : e = a`; it is the tactic form of the `rfl` pattern (E025, E030). Placeholders:
`{α : Type} [Add α] (a b c : α) (P : α → Prop) (hP : P (b + c)) (h : a = b + c)`; `[Add α]` (`α` has a `+`)
only makes `b + c` well typed, and `ℕ ℤ ℚ ℝ` all qualify. `hP` only finishes the example.

| Before | After |
|---|---|
| `a b c : α, h : a = b + c ⊢ P a` | `b c : α ⊢ P (b + c)` |

**R4 · `rw [h]`** changes the **goal**: every `a` in the goal becomes `b + c`; `a` and `h` stay in the
context (E009). Use it when the left side of `h` is not a variable. Same placeholders as R3.

| Before | After |
|---|---|
| `h : a = b + c ⊢ P a` | `h : a = b + c ⊢ P (b + c)` |

**W1 · `subst`, then `ring`** on `x y : ℤ`, `h : x = y + 1`:

| Before | After `subst h` | After `ring` |
|---|---|---|
| `h : x = y + 1 ⊢ x ^ 2 = y ^ 2 + 2 * y + 1` | `y : ℤ ⊢ (y + 1) ^ 2 = y ^ 2 + 2 * y + 1` | no goals |

**W2 · `rw [h]` with a numeral, then `ring`** on `x : ℝ`, `h : x = 2`. `ring` also evaluates numerals:

| Before | After `rw [h]` | After `ring` |
|---|---|---|
| `h : x = 2 ⊢ x ^ 2 + x = 6` | `h : x = 2 ⊢ 2 ^ 2 + 2 = 6` | no goals |

## Part 4 · `four_squares`

Statement: for `x y : ℝ`, `(x + y) ^ 2 + (x - y) ^ 2 = 2 * (x ^ 2 + y ^ 2)` (the parallelogram law in one
dimension). A pure identity of commutative rings; `ℝ` is one, so one `ring` (R1). Nothing about `ℝ` beyond the
ring laws is needed.

---

## Traps

- `ring` ignores hypotheses. If the equation is only true given `h`, use `h` first (`subst h` or `rw [h]`),
  then `ring`. When `ring` fails, it prints "Try this: ring_nf" (a tactic that only normalizes) and an
  `unsolved goals` error whose goal is the normalized form, with factors reordered (`2 * b * c` shows as
  `b * c * 2`). That is the sign the goal is not an identity yet.
- `ring` proves equalities only, not `≤` or `<` (that is `linarith`, E035, or `positivity`, E037).
- On `ℕ`, `-` truncates (`3 - 5 = 0`), so it is not ring subtraction: `ring` cannot prove `n - 1 + 1 = n`
  (false at `n = 0`). Use `omega` (E011) for linear `ℕ` facts with `-`.
- `subst h` needs one side of `h` to be a local variable that does not occur on the other side. For
  `h : a + 1 = b + c`, use `rw` instead.
- `ring` treats anything that is not `+ - * ^` or a numeral as an opaque unknown: it knows no facts about
  `√`, `⁻¹` of a variable, or functions.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| identity in `ℤ`, `ℚ`, `ℝ` (commutative ring) | `ring` | R1 |
| identity in `ℕ` with `+ * ^` only (commutative semiring) | `ring` | R2 |
| use `h : a = e` with `a` a variable, then forget `a` | `subst h` | R3 |
| use `h : a = e` by rewriting the goal | `rw [h]` | R4 |
| equation true only given `h` | `subst h` (or `rw [h]`), then `ring` | W1, W2 |
| `ℕ` subtraction, linear facts | `omega` (E011) | |
| see the state | infoview (cursor after a tactic) | |
