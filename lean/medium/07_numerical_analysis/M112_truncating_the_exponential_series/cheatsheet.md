# M112 · Truncating the exponential series: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` and `Real.exp`,
absolute value `|·|`, finite sums `∑ m ∈ Finset.range n, f m`, factorials `Nat.factorial`, the casts
`ℕ → ℝ`, decimal literals, and the tactics `norm_num` and `linarith`.

The mathematics: Taylor's theorem with remainder for `exp`. For `|x| ≤ 1` and `n > 0`,

$$\Bigl|e^x - \sum_{m=0}^{n-1} \frac{x^m}{m!}\Bigr| \le |x|^n \cdot \frac{n+1}{n!\, n}.$$

At `x = 1/2`, `n = 3` the partial sum is `1 + 1/2 + 1/8 = 13/8` and the bound is `(1/8) · 4/(6·3) = 1/36`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal the step does not touch.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell in backticks, and every line of a `lean-goal` block, is a state Lean reaches in the
  companion file; `tools/guide_sync.py` checks that. Cells containing `|` (absolute values) cannot sit in
  backticks inside a Markdown table; they are written as plain text with `\|`, and the same goals are
  repeated in a `lean-goal` block underneath, which is checked.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`). `1 / 2 : ℝ` is the real number one half, not integer division |
| `Real.exp x` | $e^x$ |
| `\|x\|` | absolute value of `x` (`abs x`) |
| `Finset.range n` | the finite set `{0, 1, …, n-1}` of natural numbers |
| `∑ m ∈ Finset.range n, f m` | $f(0) + f(1) + \dots + f(n-1)$; `m` is a bound variable (Lean may rename it `x`) |
| `m.factorial`, `Nat.factorial m` | $m!$, a natural number. `m !` after `open Nat` |
| `n.succ`, `Nat.succ n` | `n + 1` |
| `↑k` | the natural number `k` cast into `ℝ` (needed because `m!` is in `ℕ` and the sum is in `ℝ`) |
| `1.59` | a decimal literal; in `ℝ` it is exactly `159 / 100` (no floating point) |
| `case left`, `case right` | the two goals `constructor` makes from `A ∧ B` |

---

## Part 1 · `exp_half_approx`

Statement: `|Real.exp (1 / 2) - 13 / 8| ≤ 1 / 36`, i.e. $|e^{1/2} - 13/8| \le 1/36$. Plan: get the remainder
bound as a hypothesis (R1–R3), evaluate the 3-term sum and the constant in it (R4–R8), close by linear
arithmetic (R9).

### The remainder bound as a hypothesis

**R1 · `have h := Real.exp_bound hx hn`** changes the **context**: it adds `h` with the type of the term. The
lemma is

`Real.exp_bound : |x| ≤ 1 → 0 < n → |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / ↑m.factorial| ≤ |x| ^ n * (↑n.succ / (↑n.factorial * ↑n))`

with `x : ℝ` and `n : ℕ` implicit (Lean infers them from `hx` and `hn`). Placeholders:
`(x : ℝ) (n : ℕ) (hx : |x| ≤ 1) (hn : 0 < n) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | h : \|Real.exp x - ∑ m ∈ Finset.range n, x ^ m / ↑m.factorial\| ≤ \|x\| ^ n * (↑n.succ / (↑n.factorial * ↑n)) ⊢ G |

**R2 · named arguments `(x := a)`, `(n := k)`** change the **context** the same way, but you choose the
implicit arguments by name. `n` cannot be inferred from a proof of `0 < 3` written as `(by norm_num)`
(the `by` block needs to know its statement first), so write `(n := 3)` before it. The side conditions
are passed as `(by norm_num)`. Placeholders: `(a : ℝ) (ha : |a| ≤ 1) (G : Prop)`.

| Before | After `have h := Real.exp_bound (x := a) ha (n := 4) (by norm_num)` |
|---|---|
| `⊢ G` | h : \|Real.exp a - ∑ m ∈ Finset.range 4, a ^ m / ↑m.factorial\| ≤ \|a\| ^ 4 * (↑(Nat.succ 4) / (↑(Nat.factorial 4) * ↑4)) ⊢ G |

**R3 · `rw [abs_of_pos ha]`** changes the **goal**. The lemma is `abs_of_pos : 0 < a → |a| = a`.
Placeholders: `(a : ℝ) (ha : 0 < a)`. You need it for the side condition `|1 / 2| ≤ 1` of R1:
`(by norm_num [abs_of_pos])` proves it in one go (`norm_num` proves `0 < 1 / 2` for the lemma's hypothesis;
plain `norm_num` also knows `|1 / 2| = 1 / 2`).

| Before | After |
|---|---|
| ⊢ P \|a\| | `⊢ P a` |

```lean-goal
⊢ P |a|
⊢ P a
```

### Expanding a finite sum

`norm_num [Finset.sum_range_succ]` applies R4 until the range is `0`, then R5 by itself.

**R4 · `rw [Finset.sum_range_succ]`** changes the **goal**: the last term comes out of the sum. The lemma is
`∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f n`. It also matches a numeral range such as
`range 3` (Lean reads `3` as `2 + 1`). Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ)`;
`M` needs `+` and `0` (`ℝ`, `ℕ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ m ∈ Finset.range (n + 1), f m)` | `⊢ P (∑ x ∈ Finset.range n, f x + f n)` |

**R5 · `rw [Finset.sum_range_zero]`** changes the **goal**: the empty sum is `0`. The lemma is
`∑ k ∈ Finset.range 0, f k = 0`. Same placeholders as R4.

| Before | After |
|---|---|
| `⊢ P (∑ m ∈ Finset.range 0, f m)` | `⊢ P 0` |

### Evaluating the numbers

**R6 · `norm_num [Nat.factorial]`** changes the **goal**: giving `norm_num` the definition `Nat.factorial`
lets it unfold `3! = 3 · 2!` down to `0! = 1` and compute the value. (Current Mathlib's `norm_num` also
evaluates factorials of numerals without the hint; naming `Nat.factorial` does no harm.)
Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ↑(Nat.factorial 3)` | `⊢ P 6` |

**R7 · `norm_num`** changes the **goal**: `Nat.succ 3` becomes `4`, a cast `↑3` of a numeral becomes the real
numeral `3`, and fractions are reduced. Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (↑(Nat.succ 3) / ↑3)` | `⊢ P (4 / 3)` |

**R8 · `norm_num [lemmas] at h ⊢`** changes the **context and the goal**: it simplifies hypothesis `h` and the
goal with the same rules (here `Nat.factorial`, R6), so both end up in the same normal form, often with terms
moved across `≤`. In the exercise the lemmas are R4 and R6. Placeholders: `(x : ℝ)`.

| Before | After R8 |
|---|---|
| `h : x - ↑(Nat.factorial 3) ≤ 2 * 3 ⊢ x - 6 ≤ 6` | `h : x ≤ 12 ⊢ x ≤ 12` |

**R9 · `linarith`** **closes** a goal `t ≤ c`, `t < c` or `t = c` that is a linear consequence of the
hypotheses (a nonnegative combination of them). Any subterm that is not built from `+`, `-` and numeral
multiples is treated as an opaque atom: `|x - y|`, `Real.exp (1 / 2)`. Example: from
`h : |x - y| ≤ 1 / 4` it proves `|x - y| < 1 / 2`.

### Worked combination W1 (two terms at `x = 1/4`)

Goal `|Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64`. After R2 with `(x := 1 / 4)`, `(n := 2)`, the goal is unchanged and
`h` holds the raw bound; after R8 with `[Finset.sum_range_succ, Nat.factorial]`, `h` *is* the goal, and R9 closes it:

```lean-goal
⊢ |Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64
```

The hypothesis before and after R8:

```lean
h : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 2, (1 / 4) ^ m / ↑m.factorial| ≤
    |1 / 4| ^ 2 * (↑(Nat.succ 2) / (↑(Nat.factorial 2) * ↑2))
h : |Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64
```

---

## Part 2 · `exp_half_bounds`

Statement: `1.59 < Real.exp (1 / 2) ∧ Real.exp (1 / 2) < 1.66`. Part 1's theorem `exp_half_approx` is a proof
term you can pass to lemmas. Open the absolute value (R10), split the `∧` (`constructor`), turn the decimals into
fractions (R11), and close each side with `linarith` given the two halves of `h` (R12, R13).

**R10 · `have h := abs_le.mp hab`** changes the **context**. The lemma is `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`;
`.mp` is its left-to-right direction (`.mpr` the other). Placeholders: `(a b : ℝ) (hab : |a| ≤ b) (G : Prop)`
(any ordered additive group works; `ℝ`, `ℤ`, `ℚ` qualify).

| Before | After |
|---|---|
| `⊢ G` | `h : -b ≤ a ∧ a ≤ b ⊢ G` |

**`constructor`** (TACTIC_STATES, "Structure") splits `⊢ A ∧ B` into `case left ⊢ A` and `case right ⊢ B`.

**R11 · `norm_num` on decimals** changes the **goal**: a decimal literal becomes an exact fraction in lowest
terms, `1.59 → 159 / 100`, `1.66 → 83 / 50`. `linarith` handles either form, but `norm_num` first makes the
numbers plain fractions. Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P 1.59` | `⊢ P (159 / 100)` |

**R12 · `h.1`, `h.2`** are the two halves of `h : A ∧ B` (`And.left h : A`, `And.right h : B`). `have h2 := h.2`
changes the **context**. Placeholders: `(A B : Prop) (h : A ∧ B) (G : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `h2 : B ⊢ G` |

**R13 · `linarith [t₁, t₂]`** **closes** the goal like R9, after adding the proof terms `tᵢ` as extra
hypotheses. Use it for facts that are not in the context yet: `h.1`, an instance `f x` of a `∀`-lemma, or a
lemma such as `exp_half_approx`. Example: with `f : ∀ y : ℝ, y ≤ y ^ 2 + 1` in context, `linarith [f x]`
proves `x ≤ x ^ 2 + 2`.

### Worked combination W2

From `h0 : |Real.exp (1 / 4) - 5 / 4| ≤ 3 / 64`, prove `1.2 < Real.exp (1 / 4) ∧ Real.exp (1 / 4) < 1.3`.
R10 gives `h`; `constructor` and R11 give the two goals; R13 with `h.1, h.2` closes both.

| Step | Goals |
|---|---|
| R10 | `h : -(3 / 64) ≤ Real.exp (1 / 4) - 5 / 4 ∧ Real.exp (1 / 4) - 5 / 4 ≤ 3 / 64 ⊢ 1.2 < Real.exp (1 / 4) ∧ Real.exp (1 / 4) < 1.3` |
| `constructor` | `⊢ 1.2 < Real.exp (1 / 4)`, `⊢ Real.exp (1 / 4) < 1.3` |
| `all_goals norm_num` (R11) | `⊢ 6 / 5 < Real.exp (1 / 4)`, `⊢ Real.exp (1 / 4) < 13 / 10` |

---

## Traps

- `Real.exp_bound` needs `n` fixed before its side goal `0 < n` can be proved: write `(n := 3)` before
  `(by norm_num)`. Without it, `norm_num` faces `⊢ 0 < ?m.45` (`?m.45` is an unknown, a *metavariable*; the number varies) and fails: `h` is a new
  hypothesis, so nothing else determines `n`.
- Which `n`? The sum over `Finset.range n` has the `n` terms `m = 0, …, n-1`. For `13/8 = 1 + 1/2 + 1/8` you need
  three terms, so `n = 3`, not `2`.
- `linarith` does not unfold `|·|`: from `h : |e - c| ≤ d` it cannot prove `c - d ≤ e`. Open the absolute value
  with `abs_le.mp` first (R10).
- `exp_half_approx` is the name of Part 1's theorem inside `namespace M112`; Part 2 may use it (it is proved
  above), e.g. `abs_le.mp exp_half_approx`.
- `t1 ; t2` runs `t2` on the first goal only. After `constructor`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| Taylor remainder for `exp` as a hypothesis | `have h := Real.exp_bound (x := a) hx (n := k) (by norm_num)` | R1, R2 |
| prove `\|1 / 2\| ≤ 1` | `by norm_num [abs_of_pos]` | R3 |
| expand `∑ m ∈ Finset.range 3, f m` | `norm_num [Finset.sum_range_succ]` | R4, R5 |
| evaluate `k !`, `Nat.succ k`, `↑k` | `norm_num [Nat.factorial]` | R6, R7 |
| simplify a hypothesis and the goal | norm_num [lemmas] at h ⊢ | R8 |
| linear arithmetic over atoms like `Real.exp (1 / 2)` | `linarith` | R9 |
| `\|a\| ≤ b` → two inequalities | `have h := abs_le.mp hab` | R10 |
| split `A ∧ B` | `constructor` | TACTIC_STATES |
| decimals → fractions | `norm_num` | R11 |
| one half of `h : A ∧ B` | `h.1`, `h.2` | R12 |
| linear arithmetic with extra facts | `linarith [h.1, h.2]` | R13 |
| see the state | infoview | |
