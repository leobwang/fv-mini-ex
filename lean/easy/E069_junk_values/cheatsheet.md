# E069 · Junk values: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `exact`, `intro`, `have`, lemmas as proof terms (E004).
**New here:** Mathlib's real numbers `ℝ`, `Real.sqrt`, `Real.log`, and the convention that partial operations
are **total**: on inputs where the math is undefined they return a fixed "junk" value (`x / 0 = 0`,
`√x = 0` for `x ≤ 0`, `log 0 = 0`). The price: honest identities such as `x / x = 1` need a side condition.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[GroupWithZero α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`). Numerals such as `(-4 : ℝ)` are real numbers |
| `x / y` | division; in `ℝ` it is `x * y⁻¹`, and `y⁻¹` (the inverse) is defined with `0⁻¹ = 0` |
| `√x` | `Real.sqrt x`, the nonnegative square root; `√x = 0` whenever `x ≤ 0` |
| `Real.log x` | the natural logarithm; `Real.log 0 = 0`, and `Real.log (-x) = Real.log x` |
| `x ≠ 0` | `¬ (x = 0)`, i.e. `x = 0 → False` |
| `¬A` | `A → False`: a proof of `¬A` turns a proof of `A` into `False` |
| `∀ (x : ℝ), …` | the same as `∀ x : ℝ, …`; Lean prints the binder in parentheses |
| `inst✝ : GroupWithZero α` | an anonymous type-class hypothesis from a `[…]` binder |
| (empty infoview) / no goals | the proof is complete |

---

## Part 1 · `real_div_zero`

Statement: for every `x : ℝ`, `x / 0 = 0`. Division by zero is defined, and its value is `0`.

**R1 · `div_zero`** changes the **goal**: `a / 0` becomes `0`. The lemma is
`div_zero (a : G₀) : a / 0 = 0` with `[GroupWithZero G₀]` (`*` with `1`, an inverse `⁻¹` on nonzero elements and
the convention `0⁻¹ = 0`; `ℝ`, `ℚ`, `ℂ` qualify). Applied to its argument it is a proof term: `div_zero a`
proves `a / 0 = 0` (E004), so it can be the whole proof of a goal of exactly that shape.
Placeholders: `{α : Type} [GroupWithZero α] (a : α)`.

| Before | After `rw [div_zero]` |
|---|---|
| `⊢ P (a / 0)` | `⊢ P 0` |

**W3.** `ℕ` and `ℤ` use the same convention, with their own lemmas: `Nat.div_zero n : n / 0 = 0` and
`Int.ediv_zero m : m / 0 = 0` (`ℕ`, `ℤ` are not a `GroupWithZero`, so `div_zero` does not apply to them).

---

## Part 2 · `sqrt_neg`

Statement: `√(-4) = 0`. The real square root of a negative number is junk `0`.

**R2 · `apply Real.sqrt_eq_zero_of_nonpos`** changes the **goal**. The lemma is
`Real.sqrt_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : √x = 0`. `apply` matches its conclusion `√x = 0` with the
goal (finding `x`), and the premise `x ≤ 0` becomes the new goal. As a term, write
`Real.sqrt_eq_zero_of_nonpos (by tac)`, where `tac` proves the premise. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ √x = 0` | `⊢ x ≤ 0` |

**R3 · `linarith`** **closes** a goal that is a linear equality or inequality (`=`, `≤`, `<`, `≥`, `>`) over an
ordered field such as `ℝ`, when it follows linearly from the hypotheses and numeral facts. It proves
numeral comparisons like `-9 ≤ 0` with no hypotheses at all. Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ -a ≤ 0` | no goals |

**W1.** `√(-9) = 0`: R2, then R3 on the side goal.

```lean-goal
⊢ √(-9) = 0
⊢ -9 ≤ 0
```

---

## Part 3 · `log_zero'`

Statement: `Real.log 0 = 0`. The logarithm is undefined at `0` in math; in Mathlib its value is `0`.

**R4 · `Real.log_zero`** changes the **goal**: `Real.log 0` becomes `0`. The lemma has no arguments:
`Real.log_zero : Real.log 0 = 0`, so the constant itself is a proof term of that statement.

| Before | After `rw [Real.log_zero]` |
|---|---|
| `⊢ P (Real.log 0)` | `⊢ P 0` |

---

## Part 4 · `div_self'`

Statement: for `x : ℝ` with `hx : x ≠ 0`, `x / x = 1`. Because `0 / 0 = 0`, the identity is false at `0`, so
the library lemma demands `x ≠ 0`.

**R5 · `div_self`** changes the **goal list**. The lemma is
`div_self {a : G₀} (h : a ≠ 0) : a / a = 1` with `[GroupWithZero G₀]` (as in R1). With `rw [div_self]` and no
argument, the goal is rewritten and the premise `a ≠ 0` is added as a second goal; `rw [div_self ha]` or the
term `div_self ha` supplies it at once. Placeholders: `{α : Type} [GroupWithZero α] (a : α) (ha : a ≠ 0)`.

| Before | After `rw [div_self]` |
|---|---|
| `⊢ P (a / a)` | `⊢ P 1`, `⊢ a ≠ 0` |

---

## Part 5 · `not_div_self`

Statement: `¬ ∀ x : ℝ, x / x = 1`: the identity without side condition is false, and `x = 0` is the
counterexample. Assume the `∀`, use it at `0`, compute the junk value, reach `0 = 1`.

**R6 · `intro h`** on a negation changes the **goal and the context**. `¬A` unfolds to `A → False`, so `intro`
works as on any implication. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R7 · `have h0 := h a`** changes the **context**: `h : ∀ x, P x` applied to `a` is a proof of `P a`, and `have`
names it (the type is inferred, so no `: T` is needed). Placeholders: `{α : Type} (P : α → Prop) (a : α)`. When
`h : ∀ x : ℝ, …`, the numeral in `h 0` is read as `(0 : ℝ)`.

| Before | After |
|---|---|
| `⊢ P a` | `h0 : P a ⊢ P a` |

**R8 · `rw [lemma] at h0`** changes the **context**: it rewrites the hypothesis `h0` instead of the goal. Here
with R1's `div_zero`. Placeholders: `{α : Type} [GroupWithZero α] (a : α) (Q : α → Prop)`.

| Before | After `rw [div_zero] at h0` |
|---|---|
| `h0 : Q (a / 0) ⊢ Q 0` | `h0 : Q 0 ⊢ Q 0` |

**R9 · `zero_ne_one`** **closes** a goal `False` from `h0 : 0 = 1`. The lemma is `zero_ne_one : (0 : α) ≠ 1`
with `[Zero α] [One α] [NeZero (1 : α)]` (`α` has `0` and `1`, and `1 ≠ 0` is registered; `ℕ`, `ℤ`, `ℝ`, `ℂ`
qualify). Since `b ≠ c` is `b = c → False`, the application `zero_ne_one h0` is a proof of `False`.

| Before | After `exact zero_ne_one h0` |
|---|---|
| `h0 : 0 = 1 ⊢ False` | no goals |

**W2.** `¬ ∀ x : ℝ, x * x⁻¹ = 1`, the same pattern with `inv_zero : 0⁻¹ = 0` and `mul_zero : a * 0 = 0`:
R6, R7 at `0`, R8 with `inv_zero`, R8 with `mul_zero`, R9. The goal stays `False`; the hypothesis `h0` changes:

| Step | State |
|---|---|
| start | `⊢ ¬∀ (x : ℝ), x * x⁻¹ = 1` |
| `intro h` | `⊢ False` (and `h` is the `∀`) |
| `have h0 := h 0` | `h0 : 0 * 0⁻¹ = 1 ⊢ False` |
| `rw [inv_zero] at h0` | `h0 : 0 * 0 = 1 ⊢ False` |
| `rw [mul_zero] at h0` | `h0 : 0 = 1 ⊢ False` |
| `exact zero_ne_one h0` | no goals |

---

## Traps

- Side conditions such as `(-4 : ℝ) ≤ 0` close with `linarith` (R3); `norm_num` and `simp` are banned here.
- `field_simp` is banned because it uses `hx : x ≠ 0` silently; the point is to see which lemma needs it
  (R5).
- `x / x = 1`, `x * x⁻¹ = 1`, `√x * √x = x`, `Real.exp (Real.log x) = x` are all false at junk inputs; every
  library version has a hypothesis (`x ≠ 0`, `0 ≤ x`, `0 < x`). Look for it in the lemma's statement.
- `rw [div_self]` without an argument leaves a second goal `a ≠ 0` (R5); prove it, or pass `div_self hx`.
- `rw` tries `rfl` after rewriting. On `x / x = 1`, `rw [div_self]` turns the main goal into `1 = 1` and
  closes it at once, so the only goal left is `x ≠ 0` (close it with `exact hx`). Likewise `rw [div_zero]`
  on `x / 0 = 0` and `rw [Real.log_zero]` on `Real.log 0 = 0` finish the proof with no goals left.
- `rw [div_zero] at h0` changes `h0`, not the goal (R8). Without `at h0` it would try to rewrite the goal
  `False` and fail.
- `Real.sqrt x` prints as `√x`; search for the lemma by `Real.sqrt`, not by the symbol.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a / 0` → `0` | `rw [div_zero]` or the term `div_zero a` | R1 |
| `√x = 0` from `x ≤ 0` | `apply Real.sqrt_eq_zero_of_nonpos` or `Real.sqrt_eq_zero_of_nonpos (by linarith)` | R2 |
| close a linear (in)equality over `ℝ` | `linarith` | R3 |
| `Real.log 0` → `0` | `rw [Real.log_zero]` or the term `Real.log_zero` | R4 |
| `a / a` → `1` given `ha : a ≠ 0` | `rw [div_self ha]` or the term `div_self ha` | R5 |
| prove `¬A` | `intro h` (goal becomes `False`) | R6 |
| use `h : ∀ x, P x` at `a` | `have h0 := h a` | R7 |
| rewrite a hypothesis | `rw [lemma] at h0` | R8 |
| `False` from `h0 : 0 = 1` | `exact zero_ne_one h0` | R9 |
| `n / 0` in `ℕ` / `ℤ` | `Nat.div_zero n` / `Int.ediv_zero m` | W3 |
| see the state | infoview | |
