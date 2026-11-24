# E066 · ε–δ binders and abs: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, binder
predicates `∀ ε > 0` / `∃ δ > 0`, the absolute value `|x|`, closed intervals `Set.Icc a b`, and the
closing tactics `positivity` and `linarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{G : Type}` is any type. A bracket such as `[LinearOrder G]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (typed `\R`) |
| `∀ ε > 0, P ε` | `∀ ε, ε > 0 → P ε`: two binders, an `ε` and a proof that it is positive |
| `∃ δ > 0, Q δ` | `∃ δ, δ > 0 ∧ Q δ`: a witness `δ`, a proof of `δ > 0`, a proof of `Q δ` |
| `ε > 0` | `0 < ε` (`a > b` is notation for `b < a`) |
| `\|x\|` | `abs x`, the absolute value (typed `\|`); `\|(-2)\|` is the absolute value of the numeral `-2` |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}` (`Icc`: interval, closed at both ends) |
| `x ∈ Set.Icc a b` | `a ≤ x ∧ x ≤ b`, by definition |
| `h.1`, `h.2` | for `h : A ∧ B`: the proofs of `A` and of `B` |
| `∀ (x : ℝ), f x = 3 * x` | how Lean prints `∀ x, f x = 3 * x`: the binder's type is shown |
| `x ^ 2` | `x` to the natural-number power `2` (the exponent is a `ℕ`) |
| `ε / 3` | real division: `(ε / 3) * 3 = ε` exactly (unlike `/` on `ℕ`, which rounds down) |
| `\|3\|` | the absolute value of the numeral `3`; `norm_num` evaluates it (R13) |
| `case mp`, `case mpr` | the `→` and `←` directions of an `↔` after `constructor` |
| `case mp.left`, `case mp.right` | the two halves of an `∧` goal inside case `mp`, after a second `constructor` |
| `case ha₀`, `case ha₁` | the premises `0 ≤ a` and `a ≤ 1` left by `apply pow_le_one₀` (R9) |
| `case refine_1`, `case refine_2` | the goals left by the `?_` holes of a `refine`, in order |

---

## Part 1 · `eps_half`

Statement: `∀ ε > (0 : ℝ), ∃ δ > 0, δ < ε`: below every positive real there is a smaller positive real.

**R1 · `intro ε hε`** changes the **context**. `∀ ε > 0, P ε` hides two binders, so `intro` takes two names:
the number and the proof that it is positive. Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ ε > 0, P ε` | `ε : ℝ, hε : ε > 0 ⊢ P ε` |

**R2 · `refine ⟨d, ?_, ?_⟩`** changes the **goal list**. `∃ δ > 0, Q δ` is `∃ δ, δ > 0 ∧ Q δ`, and the
anonymous constructor `⟨d, p, q⟩` flattens the `∃` and the `∧`: you name the witness `d` now and get one goal
per `?_`. Instead of `?_` you may write the proof in place (`by positivity`), or give all three parts at once
with `exact ⟨d, by …, by …⟩`. Placeholders: `(Q : ℝ → Prop) (d : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∃ δ > 0, Q δ` | `⊢ d > 0`, `⊢ Q d` |

**R3 · `positivity`** **closes** a goal `0 < e`, `e > 0` or `0 ≤ e` when `e` is built with `+`, `*`, `/`, `^`,
`|·|` from numerals and variables that a hypothesis (`hε : ε > 0`) says are positive. It does not prove
`e < c` for other `c`; that is R4.

| Before | After |
|---|---|
| `hε : ε > 0 ⊢ ε / 5 > 0` | no goals |

**R4 · `linarith`** **closes** a goal `t < s`, `t ≤ s`, `t = s` (or derives `False`) that follows from the
hypotheses by adding them up with nonnegative constant coefficients. Terms must be linear: constants times
atoms, where an atom is any term it cannot see inside (`ε`, `x`, `|x|`, `f x`). It knows `ε / 2 = (1/2) * ε`,
but not `|a * b| = |a| * |b|` (R12).

| Before | After |
|---|---|
| `h₁ : a < b, h₂ : b ≤ 2 * c ⊢ a / 2 < c` | no goals |

**W1.** `∀ ε > (0 : ℝ), ∃ δ > 0, 2 * δ < ε` with `δ = ε / 4`: R1, R2, then R3 on the first goal and R4 on the
second.

```lean-goal
⊢ ∀ ε > 0, ∃ δ > 0, 2 * δ < ε
⊢ ∃ δ > 0, 2 * δ < ε
⊢ ε / 4 > 0
⊢ 2 * (ε / 4) < ε
```

---

## Part 2 · `abs_sub_lt`

Statement: for `x : ℝ`, `|x - 1| < 2 ↔ -1 < x ∧ x < 3`: distance less than `2` from `1` means lying in the open
interval `(-1, 3)`.

**R5 · `rw [abs_sub_lt_iff]`** changes the **goal** (or, with `at h`, the hypothesis `h`). The lemma is
`abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c`. `rw` with an `↔` replaces one proposition by the other.
Placeholders: `{G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b c : G)` (`G` has `+`,
`-`, a total order, and adding preserves `≤`; `ℤ`, `ℚ`, `ℝ` qualify).

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ |a - b| < c
⊢ a - b < c ∧ b - a < c
```

**R6 · `constructor`** on an `↔` changes the **goal list**: `A ↔ B` becomes two implications, case `mp`
(`A → B`) and case `mpr` (`B → A`). Each implication then opens with `intro h` and its `∧` goal splits with
`constructor` again (TACTIC_STATES, "Structure"). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R7 · `linarith [t₁, t₂]`** **closes** the goal like R4, with the terms `tᵢ` added as extra hypotheses. For
`h : A ∧ B`, pass `h.1 : A` and `h.2 : B`: the halves of the conjunction become usable inequalities. (This
Mathlib's `linarith` also splits an `∧` hypothesis by itself, so plain `linarith` works too; naming the halves
makes the step explicit and costs nothing.) Placeholders: `(a b x : ℝ)`.

| Before | After |
|---|---|
| `h : a < x ∧ x < b ⊢ a < b` | no goals |

**W2.** `h : |x - 5| < 1` gives `4 < x`: R5 with `at h` turns the hypothesis into two inequalities, then R7
closes the goal.

| Step | State after it |
|---|---|
| `rw [abs_sub_lt_iff] at h` | `h : x - 5 < 1 ∧ 5 - x < 1 ⊢ 4 < x` |
| `linarith [h.1, h.2]` | no goals |

---

## Part 3 · `Icc_sq`

Statement: for `x : ℝ` with `h : x ∈ Set.Icc (0 : ℝ) 1` (i.e. `0 ≤ x ≤ 1`), `x ^ 2 ≤ 1`.

**R8 · `Set.mem_Icc`** changes the **context** when used as `rw [Set.mem_Icc] at h`. The lemma is
`Set.mem_Icc : x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b`. The rewrite is optional: membership in `Set.Icc` *is* that
`∧` by definition, so `h.1 : a ≤ x` and `h.2 : x ≤ b` work on the original `h`. Placeholders:
`{α : Type} [Preorder α] (a b x : α)` (`α` has `≤`; `ℕ`, `ℤ`, `ℝ` qualify).

| Before | After |
|---|---|
| `h : x ∈ Set.Icc a b ⊢ P` | `h : a ≤ x ∧ x ≤ b ⊢ P` |

**R9 · `pow_le_one₀`** changes the **goal list** when used with `apply`. The lemma is
`pow_le_one₀ : 0 ≤ a → a ≤ 1 → a ^ n ≤ 1`: `apply` matches the conclusion and leaves the two premises as goals
(cases `ha₀`, `ha₁`). As a term, `pow_le_one₀ h₀ h₁` is already a proof of `a ^ n ≤ 1` (a lemma applied to
proofs of its premises proves its conclusion). Placeholders:
`{M₀ : Type} [MonoidWithZero M₀] [Preorder M₀] [PosMulMono M₀] (a : M₀) (n : ℕ)` (`M₀` has `*`, `0`, `1`, `≤`,
and multiplying by a nonnegative number preserves `≤`; `ℕ`, `ℚ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ a ^ n ≤ 1` | `⊢ 0 ≤ a`, `⊢ a ≤ 1` |

**W3.** `h : x ∈ Set.Icc (1 : ℝ) 2` gives `1 ≤ x ^ 3` with the companion lemma `one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n`,
fed `h.1` directly (R8 without the rewrite):

```lean-goal
⊢ 1 ≤ x ^ 3
```

---

## Part 4 · `linear_cont`

Statement: if `f x = 3 * x` for all `x`, then `∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε`: `f` is continuous
at `0`, in ε–δ form. The witness is `δ = ε / 3`.

R1 opens `ε`, R2 names `δ`, R3 closes `δ > 0`, R10 opens `x` and `hx : |x| < ε / 3`. From there the goal
goes `|f x| < ε`, then by R11 `|3 * x| < ε`, by R12 `|3| * |x| < ε`, by R13 `3 * |x| < ε`, which R4 closes.
The new pieces:

**R10 · `refine fun x hx => ?_`** changes the **context**: a goal `∀ x, A x → B x` is proved by a function, and
the `?_` in its body becomes the goal with `x` and `hx` in scope (like `intro x hx`). The same term can fill the
last slot of R2: `refine ⟨d, ?_, fun x hx => ?_⟩`. Placeholders: `{α : Type} (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (x : α), A x → B x` | `x : α, hx : A x ⊢ B x` |

**R11 · `rw [hf]`** with `hf : ∀ x, f x = g x` changes the **goal**: `rw` instantiates `x` with the first
match it finds (`x := y`) and rewrites. Placeholders: `(f g : ℝ → ℝ) (y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (f y)` | `⊢ P (g y)` |

**R12 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul (a b : α) : |a * b| = |a| * |b|`.
Placeholders: `{α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α] (a b : α)` (an ordered ring: `ℤ`, `ℚ`,
`ℝ` qualify).

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R13 · `norm_num`** changes the **goal**: it evaluates the numeric parts, here the absolute value of a numeral,
`|(-2)| = 2`. It leaves `|y|`, `|x|` and other non-numeral parts alone. Placeholders: `(y ε : ℝ)`.

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ |(-2)| * y < ε
⊢ 2 * y < ε
```

Then R4 finishes: `|x|` is an atom, so `hx : |x| < ε / 3` and the goal `3 * |x| < ε` are linear in it.

**W4.** `hx : |x| < 1` gives `|(-2) * x| < 3`: R12, R13, R4.

```lean-goal
⊢ |-2 * x| < 3
⊢ |(-2)| * |x| < 3
⊢ 2 * |x| < 3
```

---

## Traps

- `∀ ε > 0, P ε` needs **two** names in `intro`. `intro ε` alone leaves `⊢ ε > 0 → P ε`.
- `∃ δ > 0, Q δ` needs **three** components, `⟨δ, proof of δ > 0, proof of Q δ⟩`, not a pair.
- Write the type of `0` when nothing else fixes it: `∀ ε > (0 : ℝ), …`. A bare `0` with no other hint is a
  natural number.
- `positivity` proves only `0 < e` / `0 ≤ e` / `e ≠ 0`. For `ε / 2 < ε` use `linarith` (R4).
- `linarith` does no nonlinear algebra: it will not turn `|3 * x|` into `3 * |x|`. Rewrite first (R12, R13).
- `x ∈ Set.Icc 0 1` is the **closed** interval; `Set.Ioo` is open, `Set.Ico` / `Set.Ioc` are half-open.
- In `|x - a| < r ↔ …`, `rw [abs_sub_lt_iff]` gives `x - a < r ∧ a - x < r`, not `a - r < x ∧ x < a + r`; the
  last step is `linarith`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` | `intro ε hε` | R1 |
| prove `∃ δ > 0, Q δ` | `refine ⟨d, ?_, ?_⟩` or `exact ⟨d, by …, by …⟩` | R2 |
| `0 < e`, `e > 0` from positive pieces | `positivity` | R3 |
| linear (in)equality from hypotheses | `linarith` / `linarith [h.1, h.2]` | R4, R7 |
| `\|a - b\| < c` → `a - b < c ∧ b - a < c` | `rw [abs_sub_lt_iff]` (`at h` for a hypothesis) | R5 |
| split `A ↔ B` | `constructor` (cases `mp`, `mpr`) | R6 |
| `x ∈ Set.Icc a b` as `a ≤ x ∧ x ≤ b` | `h.1`, `h.2` (or `rw [Set.mem_Icc] at h`) | R8 |
| `a ^ n ≤ 1` from `0 ≤ a`, `a ≤ 1` | `pow_le_one₀ h₀ h₁` | R9 |
| open `∀ x, A x → B x` inside a `refine` | `fun x hx => ?_` | R10 |
| use `hf : ∀ x, f x = g x` | `rw [hf]` | R11 |
| `\|a * b\|` → `\|a\| * \|b\|` | `rw [abs_mul]` | R12 |
| `\|(-2)\|` → `2` | `norm_num` | R13 |
| see the state | infoview | |
