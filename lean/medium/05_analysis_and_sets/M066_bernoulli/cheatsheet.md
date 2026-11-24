# M066 · Bernoulli's inequality: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014) and `omega`
(E011). **New here:** Mathlib's real numbers `ℝ`, the cast `ℕ → ℝ`, powers `a ^ n`, and the arithmetic
deciders `linarith` and `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw` or `have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- `G : Prop` with `g : T → G` is an arbitrary goal; it is there only so that an entry that adds
  `h : T` to the context can close.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is
  a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

Type classes met below:

| Bracket | Meaning | Met by |
|---|---|---|
| `[Monoid M]` | an associative `*` with a `1`; enough for `a ^ n` with `n : ℕ` | `ℕ`, `ℤ`, `ℝ`, `ℂ` |
| `[AddMonoidWithOne α]` | `+`, `0`, `1`, hence a cast `ℕ → α` | `ℕ`, `ℤ`, `ℝ`, `ℂ` |
| `[Semiring α] [PartialOrder α] [IsOrderedRing α]` | `+`, `*` and an order `≤` compatible with both | `ℕ`, `ℤ`, `ℚ`, `ℝ` |
| `[CommRing α] [LinearOrder α] [IsStrictOrderedRing α]` | the same with `-` and a total order | `ℤ`, `ℚ`, `ℝ` |

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | the real numbers; the natural numbers `0, 1, 2, …` |
| `↑n` | the natural number `n : ℕ` cast into `ℝ` (`Nat.cast n`); `1 + n * x` in the statement is `1 + ↑n * x` |
| `↑(n + 1)` | the cast of the natural `n + 1` (add in `ℕ`, then cast); `↑n + 1` is cast first, then add in `ℝ` |
| `↑0` | the natural `0` cast into `ℝ` (R3 turns it into the real `0`) |
| `a ^ n` | `a * a * … * a` (`n` factors), `n : ℕ`; `a ^ 0 = 1` |
| `n + 1` in case `succ` | the successor of `n` (Mathlib prints `Nat.succ n` as `n + 1`) |
| `case zero`, `case succ` | the two goals made by `induction` |
| `inst✝ : Monoid M` | an unnamed type-class assumption; ignore it |

---

## Part 1 · `succ_le_two_pow`

Statement: for every natural `n`, `n + 1 ≤ 2 ^ n`, an inequality in `ℕ`. Induct on `n`: the base is
`0 + 1 ≤ 2 ^ 0`; the step multiplies the induction hypothesis by `2`.

**R1 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list** and the
**context**: one goal becomes two. In `zero`, `n` is replaced by `0`; in `succ`, by `n + 1`, and the
context gains `ih`, the goal for `n`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `pow_zero`** changes the **goal**. The lemma is `pow_zero : a ^ 0 = 1`. Placeholders:
`{M : Type} [Monoid M] (a : M)`. `simp` applies it by itself; together with `zero_add`
(`0 + a = a`) it closes the base case `0 + 1 ≤ 2 ^ 0`.

| Before | After `rw [pow_zero]` |
|---|---|
| `⊢ P (a ^ 0)` | `⊢ P 1` |

**R4 · `pow_succ`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`: it
peels one factor off, so the goal now contains `a ^ n`, the power in `ih`. Placeholders:
`{M : Type} [Monoid M] (a : M) (n : ℕ)`.

| Before | After `rw [pow_succ]` |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R5 · `omega`** **closes** a linear (in)equality over `ℕ` or `ℤ` that follows from the hypotheses.
A non-linear subterm such as `3 ^ k` or `2 ^ n` is one opaque number (an *atom*), so
`ih : k + 2 ≤ 3 ^ k ⊢ k + 3 ≤ 3 ^ k * 3` is linear in the atom `3 ^ k`.

| Before | After `omega` |
|---|---|
| `k : ℕ, ih : k + 2 ≤ 3 ^ k ⊢ k + 3 ≤ 3 ^ k * 3` | no goals |

**W1** (guide): `1 ≤ 3 ^ n` by R1; `simp` in `zero`; R4, then R5 in `succ`:

```lean-goal
⊢ 1 ≤ 3 ^ 0
⊢ 1 ≤ 3 ^ (n + 1)
```

---

## Part 2 · `bernoulli`

Statement: for real `x ≥ -1` and natural `n`, `1 + n·x ≤ (1 + x)^n`. Induct on `n` (R1; `hx` stays in
the context). The base is `1 + ↑0 * x ≤ (1 + x) ^ 0`. In the step, with `ih : 1 + n x ≤ (1 + x)^n`:
since `1 + x ≥ 0`, multiply `ih` by `1 + x`:

$$(1 + x)^{n+1} = (1+x)^n(1+x) \;\ge\; (1 + nx)(1 + x) = 1 + (n+1)x + nx^2 \;\ge\; 1 + (n+1)x,$$

where the last step uses $n x^2 \ge 0$.

**R3 · `Nat.cast_zero`** changes the **goal**. The lemma is `Nat.cast_zero : ((0 : ℕ) : α) = 0`: the
natural `0` cast into `α` is `α`'s own `0`. Placeholders: `{α : Type} [AddMonoidWithOne α]`. `simp`
applies it by itself, then `zero_mul` (`0 * a = 0`), `add_zero` and R2, and closes the base case.

| Before | After `rw [Nat.cast_zero]` |
|---|---|
| `⊢ P ↑0` | `⊢ P 0` |

**R6 · `linarith`** **closes** a linear (in)equality over an ordered field such as `ℝ` or `ℚ` that
follows from the hypotheses by adding them with non-negative coefficients. Use it to prove
`0 ≤ 1 + x` from `hx : -1 ≤ x`, inside a `have` (`TACTIC_STATES.md`, "Adding facts").

| Before | After `linarith` |
|---|---|
| `hx : -c ≤ x ⊢ 0 ≤ c + x` | no goals |

**R7 · `mul_le_mul_of_nonneg_right`** changes the **context** when used in `have`. The lemma is
`b ≤ c → 0 ≤ a → b * a ≤ c * a`: multiply an inequality on the right by a non-negative `a`.
Placeholders: `{α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (a b c : α)`,
`(hbc : b ≤ c) (ha : 0 ≤ a)`. Here `hbc` is `ih` and `a` is `1 + x`.

| Before | After `have h := mul_le_mul_of_nonneg_right hbc ha` |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ G` | `h : b * a ≤ c * a ⊢ G` |

**R8 · `push_cast`** changes the **goal**: it moves casts inward (`Nat.cast_add`, `Nat.cast_one`,
`Nat.cast_mul`, …), so `↑(n + 1)` becomes `↑n + 1`. Afterwards the goal and `ih` share the atom `↑n`.
Placeholders: `{α : Type} [AddMonoidWithOne α] (n : ℕ)`.

| Before | After `push_cast` |
|---|---|
| `⊢ P ↑(n + 1)` | `⊢ P (↑n + 1)` |

Then R4 turns `(1 + x) ^ (n + 1)` into `(1 + x) ^ n * (1 + x)`, the right side of the `have` from R7.

**W2** (guide): R8, then R7 on a fact proved by R6, then R6:

```lean-goal
⊢ ↑n * y ≤ ↑(n + 1) * y + y
⊢ ↑n * y ≤ (↑n + 1) * y + y
```

| Before | After `have h2 := mul_le_mul_of_nonneg_right h1 hy` |
|---|---|
| `h1 : ↑n ≤ ↑n + 1 ⊢ ↑n * y ≤ (↑n + 1) * y + y` | `h2 : ↑n * y ≤ (↑n + 1) * y ⊢ ↑n * y ≤ (↑n + 1) * y + y` |

### Facts to hand to `nlinarith`

The last step needs `0 ≤ ↑n * x ^ 2`. Build it from three lemmas; each, used in `have`, adds one fact
to the **context**.

**R9 · `Nat.cast_nonneg`**: `0 ≤ (↑n : α)`, a cast natural is non-negative. Placeholders:
`{α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ)`. Write the target type,
`(Nat.cast_nonneg n : (0 : ℝ) ≤ n)`; see Traps.

| Before | After `have h := (Nat.cast_nonneg n : (0 : α) ≤ n)` |
|---|---|
| `⊢ G` | `h : 0 ≤ ↑n ⊢ G` |

**R10 · `sq_nonneg`**: `0 ≤ a ^ 2`. Placeholders:
`{α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (a : α)`.

| Before | After `have h := sq_nonneg a` |
|---|---|
| `⊢ G` | `h : 0 ≤ a ^ 2 ⊢ G` |

**R11 · `mul_nonneg`**: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. Placeholders:
`{α : Type} [Semiring α] [PartialOrder α] [IsOrderedRing α] (a b : α) (ha : 0 ≤ a) (hb : 0 ≤ b)`.
The arguments may be proof terms themselves: `mul_nonneg (R9 …) (R10 …)`.

| Before | After `have h := mul_nonneg ha hb` |
|---|---|
| `ha : 0 ≤ a, hb : 0 ≤ b ⊢ G` | `h : 0 ≤ a * b ⊢ G` |

**W3** (guide): R11 applied to R10 and R9 in one term:

| Before | After `have h := mul_nonneg (sq_nonneg y) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)` |
|---|---|
| `⊢ 0 ≤ y ^ 2 * ↑m` | `h : 0 ≤ y ^ 2 * ↑m ⊢ 0 ≤ y ^ 2 * ↑m` |

**R12 · `nlinarith [t₁, t₂]`** **closes** a polynomial (in)equality over `ℝ`. It multiplies out every
product in the goal and the hypotheses, then reasons like R6 with each monomial (`↑n * x ^ 2`,
`↑n * x`, …) as an atom; it also tries products of pairs of hypotheses. The terms `tᵢ` are proofs
added as extra hypotheses first: pass the non-negative quantity it cannot find by itself.

| Before | After `nlinarith [mul_nonneg ha (sq_nonneg b)]` |
|---|---|
| `ha : 0 ≤ a ⊢ a ≤ a + a * b ^ 2` | no goals |

In the exercise, after R8 and R4 the goal is `1 + (↑n + 1) * x ≤ (1 + x) ^ n * (1 + x)`, and `h2` has
exactly the atoms `↑n`, `x`, `(1 + x) ^ n`: expanding both sides, the gap is `↑n * x ^ 2`, the hint.

---

## Traps

- `nlinarith` with no hint fails on the final step: it does not invent `0 ≤ ↑n * x ^ 2`. Pass it in
  the brackets (R12 with R9–R11).
- Without R8 the goal has the atom `↑(n + 1)` and `ih` has `↑n`; the arithmetic tactics treat them as
  unrelated numbers. Without R4, `(1 + x) ^ (n + 1)` and `(1 + x) ^ n` are unrelated atoms too.
- `Nat.cast_nonneg n` alone does not say which type `n` is cast into: `have h := Nat.cast_nonneg n`
  stops with "typeclass instance problem is stuck". Write `(Nat.cast_nonneg n : (0 : ℝ) ≤ n)`.
- R7 needs `0 ≤ 1 + x` as a proof term: prove it first with `have h1 : 0 ≤ 1 + x := by linarith`.
- The banned lemmas (`one_add_mul_le_pow`, …) are Bernoulli's inequality itself; the checker rejects
  them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on `n : ℕ` | `induction n with \| zero => … \| succ n ih => …` | R1 |
| base case `… ^ 0`, `↑0` | `simp` | R2, R3 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R4 |
| linear goal over `ℕ` | `omega` | R5 |
| linear goal over `ℝ` | `linarith` | R6 |
| multiply `b ≤ c` by `0 ≤ a` | `have h := mul_le_mul_of_nonneg_right hbc ha` | R7 |
| `↑(n + 1) → ↑n + 1` | `push_cast` | R8 |
| `0 ≤ ↑n` in `ℝ` | `(Nat.cast_nonneg n : (0 : ℝ) ≤ n)` | R9 |
| `0 ≤ a ^ 2` | `sq_nonneg a` | R10 |
| `0 ≤ a * b` | `mul_nonneg ha hb` | R11 |
| polynomial goal over `ℝ` | `nlinarith [fact₁, fact₂]` | R12 |
| see the state | infoview | |
