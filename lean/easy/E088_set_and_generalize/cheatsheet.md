# E088 · set and generalize: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have` and `exact`, `rcases` on `∨`, `omega`, `decide`,
the combinator `t <;> u`.
**New here:** `generalize` (replace a compound term by a fresh variable), Mathlib's `set` (abbreviate a term
and keep its definition), the `rfl` pattern of `rcases`, the library lemma `Nat.mod_lt`, Mathlib's `linarith`
and its real numbers `ℝ`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P : Prop` or `P : ℕ → Prop` is "the rest of your goal". A hypothesis `g` in an example only finishes it: it
  shows what the goal or context became.
- Placeholders are written as Lean binders: `(a b : ℕ)` natural numbers, `(a b : ℝ)` real numbers,
  `(hb : b > 0)` a proof that `b > 0`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ`, `ℝ` | natural numbers `0, 1, 2, …`; Mathlib's real numbers |
| `n % 3` | remainder of `n` divided by `3` (`Nat.mod`); `n % 0 = n` |
| `n % 3 * (n % 3) % 3` | `((n % 3) * (n % 3)) % 3`: `*` and `%` have the same precedence and group to the left, so Lean drops the first pair of parentheses |
| `x ^ 2` | `x` to the natural-number power `2` (`Monoid.npow`), a real number |
| `a ≠ b` | `a = b → False` |
| `b > 0` | notation for `0 < b` |
| `∀ m < b, Q m` | `∀ m, m < b → Q m` (bounded-quantifier notation) |
| `y : ℝ := a ^ 2 + b` | a local definition made by `set`: `y` is a name for that value (a `let` in the context) |
| `case inl`, `case inr.inl`, `case inr.inr` | the goals of `rcases` on `A ∨ B ∨ C`: `∨` nests to the right, so these are `A`, `B`, `C` |

---

## Part 1 · `gen_ex`

Statement: for every `n : ℕ`, `(n % 3) * (n % 3) % 3 ≠ 2` (2 is not a square mod 3). `omega` cannot do it
directly: it handles only linear arithmetic and `n % 3 * (n % 3)` is a product of two unknowns. But `n % 3` is
one of `0, 1, 2`: bound it (R1), give it a variable name (R2), split into the three values (R3, R4) and compute
(R5).

**R1 · `Nat.mod_lt`** changes the **context** (used with `have`). Statement:
`Nat.mod_lt (x : ℕ) {y : ℕ} : 0 < y → x % y < y` (`#check` prints `0 < y`; `y > 0` is the same proposition). The divisor `y` is implicit: Lean reads it off the proof of
`y > 0`. With a numeral divisor, write the proof inline as `(by omega : 5 > 0)`: a `by` block with its type
written after `:`. Placeholders: `(a b : ℕ) (hb : b > 0) (P : Prop)`.

| Before | After `have h := Nat.mod_lt a hb` |
|---|---|
| `hb : b > 0 ⊢ P` | `h : a % b < b ⊢ P` |

| Before | After `have h := Nat.mod_lt a (by omega : 5 > 0)` |
|---|---|
| `a : ℕ ⊢ P` | `h : a % 5 < 5 ⊢ P` |

**R2 · `generalize e = m at h ⊢`** changes the **goal and the context**: every occurrence of the term `e` in the
goal (`⊢`) and in `h` becomes a fresh variable `m : ℕ`. Lean forgets that `m` was `e`, so the only facts left
about `m` are the hypotheses listed after `at`. Write `generalize hm : e = m at h ⊢` to keep `hm : e = m` as well.
Placeholders: `(a b : ℕ) (Q : ℕ → Prop) (h : a % b < b)`.

| Before | After |
|---|---|
| `h : a % b < b ⊢ Q (a % b)` | `m : ℕ, h : m < b ⊢ Q m` |

**R3 · `omega`** **closes** a disjunction of values from a bound: from `h : m < 2` it proves `m = 0 ∨ m = 1`.
Used inline, `(by omega : m = 0 ∨ m = 1 ∨ m = 2)` is a proof term of the three-way disjunction, which `rcases`
takes directly (no `have` needed). Placeholders: `(m : ℕ) (h : m < 2)`.

| Before | After |
|---|---|
| `h : m < 2 ⊢ m = 0 ∨ m = 1` | no goals |

**R4 · `rcases hm with rfl | rfl | rfl`** changes the **goal list and the context**: one goal per side of
`hm : m = 0 ∨ m = 1 ∨ m = 2`. The pattern `rfl` substitutes the value for `m` everywhere (goal and hypotheses)
and removes `m` and the equation. It needs `m` to be a variable: on `n % 3 = 0` it fails, which is why R2 comes
first. Placeholders: `(P : ℕ → Prop) (m : ℕ) (hm : m = 0 ∨ m = 1 ∨ m = 2)`.

| Before | After |
|---|---|
| `hm : m = 0 ∨ m = 1 ∨ m = 2 ⊢ P m` | `⊢ P 0`, `⊢ P 1`, `⊢ P 2` |

**R5 · `decide`** **closes** a decidable statement about concrete numbers by evaluating it; `≠` on `ℕ` is
decidable. It fails as soon as a free variable such as `m` or `n` is left in the goal.

| Before | After |
|---|---|
| `⊢ 2 * 2 % 5 ≠ 3` | no goals |

**W1: the whole chain on `n % 2`** (`(n % 2) * (n % 2) % 2 = n % 2`). R1 adds the bound, R2 renames, then
`rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> decide` (R3, R4, R5) closes both cases:

```lean-goal
⊢ n % 2 * (n % 2) % 2 = n % 2
⊢ m * m % 2 = m
```

---

## Part 2 · `set_ex`

Statement: for `x : ℝ` with `h : (x ^ 2 + 1) * 2 = 10`, prove `x ^ 2 + 1 = 5`. The exercise is to abbreviate
`x ^ 2 + 1` with `set` (R6) and read the simpler state; then the goal is a linear fact about the new name (R7).

**R6 · `set y := e with hy`** changes the **context and the goal**: it adds the local definition `y : ℝ := e`
and the equation `hy : y = e`, and replaces `e` by `y` in the goal and in every hypothesis. Unlike R2 it keeps
the link to `e`. It never changes what is provable: it only renames. Placeholders:
`(a b : ℝ) (P : ℝ → Prop) (h : P (a ^ 2 + b))`.

| Before | After `set y := a ^ 2 + b with hy` |
|---|---|
| `h : P (a ^ 2 + b) ⊢ P (a ^ 2 + b)` | `y : ℝ := a ^ 2 + b, h : P y, hy : y = a ^ 2 + b ⊢ P y` |

**R7 · `linarith`** **closes** a linear equality or inequality over an ordered field (`ℝ`, `ℚ`) or `ℕ`, `ℤ`,
by adding up hypotheses times constants. `y * 3` is linear (a numeral times an unknown). A nonlinear piece such as
`a ^ 2` counts as one unknown, so `set` is only for readability here.

| Before | After |
|---|---|
| `h : y * 3 = 12 ⊢ y = 4` | no goals |

**W2: R6 then R7, and R7 alone.** On `h : 3 * (a ^ 2 - 1) = 6`, `set t := a ^ 2 - 1 with ht` leaves

```lean-goal
⊢ a ^ 2 - 1 = 2
⊢ t = 2
```

and `linarith` closes it; `linarith` also closes the original goal without the `set`.

---

## Traps

- `generalize n % 3 = m` without `at h` changes only the goal: `h` still says `n % 3 < 3`, nothing ties it to
  `m`, and `omega` cannot prove `m = 0 ∨ m = 1 ∨ m = 2`. Add the bound first (R1), then `generalize … at h ⊢`.
- Order matters: generalize **after** the `have` from R1. If you generalize first, `Nat.mod_lt n …` produces a
  fresh `n % 3 < 3` that mentions `n % 3`, not `m`.
- `rcases … with rfl | …` needs one side of each equation to be a variable. `n % 3 = 0` is not substitutable.
- `decide` needs a goal without free variables: run it only after the `rfl` substitutions, on all goals
  (`<;> decide`, not `; decide`, which reaches only the first goal).
- `set` is not `generalize`: after `set`, `y` is still known to equal `x ^ 2 + 1` (`hy`, and the `:=` in the
  context). It never makes a goal provable that was not before.
- Here `simp`, `rw`, `norm_num`, `interval_cases`, `subst` and friends are banned: the point is to do the case
  split by hand with `generalize` and `rcases`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a % b < b` | `have h := Nat.mod_lt a hb` | R1 |
| the side fact `3 > 0` inline | `(by omega : 3 > 0)` | R1 |
| replace term `e` by a fresh variable in `h` and the goal | `generalize e = m at h` ⊢ (one command, ending in the goal symbol) | R2 |
| same, keeping `hm : e = m` | `generalize hm : e = m at h` ⊢ | R2 |
| `m < 3 → m = 0 ∨ m = 1 ∨ m = 2` | `(by omega : m = 0 ∨ m = 1 ∨ m = 2)` | R3 |
| one goal per value, substituted | `rcases hm with rfl \| rfl \| rfl` | R4 |
| close a goal on concrete numbers | `decide` (after `<;>`) | R5 |
| abbreviate `e`, keep `hy : y = e` | `set y := e with hy` | R6 |
| linear goal over `ℝ` from hypotheses | `linarith` | R7 |
| see the state | infoview | |
