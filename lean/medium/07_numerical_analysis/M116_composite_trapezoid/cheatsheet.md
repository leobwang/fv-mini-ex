# M116 · Composite trapezoid from the panel bound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's interval integral
`∫ x in a..b, f x`, finite sums `∑ k ∈ Finset.range n, …`, absolute value `|·|`, the cast `ℕ → ℝ`,
`calc` chains and the `gcongr` tactic.

The mathematics: with nodes $x_k = a + k h$ ($k = 0, \dots, n$), the integral over $[a, a + n h]$ is the sum
of the $n$ panel integrals $\int_{x_k}^{x_{k+1}} f$. Let $e_k = \int_{x_k}^{x_{k+1}} f - \tfrac h2 (f(x_k) + f(x_{k+1}))$
be the error of panel $k$. Then
$\left|\sum_k e_k\right| \le \sum_k |e_k| \le \sum_k \tfrac{M h^3}{12} = n \cdot \tfrac{M h^3}{12}$,
where $M$ is the constant of the panel bound `hpanel` (in practice $M = \max |f''|$).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" or of a hypothesis (`P : ℝ → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger expression.
- `G : Prop` with `g : … → G` is a stand-in goal for entries that only change the context.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[AddCommGroup G]` is a
  requirement on `G` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`) |
| `∫ (x : ℝ) in a..b, f x` | the oriented integral $\int_a^b f(x)\,dx$ (Lebesgue measure; equals $-\int_b^a$ when $b < a$) |
| `∫ x in a..b, f x ∂μ` | the same with respect to a measure `μ`; no `∂μ` means `μ = volume` |
| `MeasureTheory.volume` | Lebesgue measure on `ℝ` |
| `IntervalIntegrable f μ a b` | `f` is integrable on the interval between `a` and `b` (needed to add integrals) |
| `Continuous f` | `f : ℝ → ℝ` is continuous |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` of naturals (a `Finset` is a finite set) |
| `∑ k ∈ s, g k` | $\sum_{k \in s} g(k)$; `∑ _k ∈ s, c` sums a term that does not depend on `k` |
| `s.card` | the number of elements of the finite set `s` |
| `n • c` | `n : ℕ` copies of `c` added up (`nsmul`); equals `↑n * c` |
| `\|x\|` | absolute value |
| `↑k` | the natural number `k` cast into `ℝ`. `↑(k + 1)` (cast of a sum) and `↑k + 1` are different terms |
| `∑ x ∈ …, ∫ (x : ℝ) in ↑x..` | two unrelated bound variables that happen to print as `x`; a rewrite renamed the sum's `k` |
| `case calc_1`, `case h` | goal names produced by `calc` and `gcongr` |
| `a✝ : k ∈ s` | a hypothesis you did not name (inaccessible); name it with `gcongr with k hk` |

---

## Part 1 · `composite_trapezoid`

Statement: given `hpanel : ∀ x, |∫ t in x..x + h, f t - h / 2 * (f x + f (x + h))| ≤ M * h ^ 3 / 12` (one
panel's error), the error of the composite rule with `n` panels on `[a, a + ↑n * h]` is `≤ ↑n * (M * h ^ 3 / 12)`.

### Splitting the integral

**R1 · `intervalIntegral.sum_integral_adjacent_intervals`** changes the **context**: `have hsum := …` adds the
equation "sum of panel integrals = whole integral". The lemma:
`(∀ k < n, IntervalIntegrable f μ (a k) (a (k + 1))) → ∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), f x ∂μ = ∫ x in a 0..a n, f x ∂μ`.
The nodes `a : ℕ → ℝ` cannot be guessed from the integrability proof, so pass them by name:
`(μ := MeasureTheory.volume) (f := f) (a := u) (n := n)`. Placeholders: `(f : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ)`
and `hu` the integrability hypothesis (R2 builds it).

| Before | After |
|---|---|
| `⊢ G` | goal unchanged; context gains `hsum` (below) |

```text
hsum : ∑ k ∈ Finset.range n, ∫ (x : ℝ) in u k..u (k + 1), f x = ∫ (x : ℝ) in u 0..u n, f x
```

**R2 · `Continuous.intervalIntegrable`** **closes** the integrability goal: for `hf : Continuous f`,
`hf.intervalIntegrable x y : IntervalIntegrable f volume x y` for any `x y : ℝ`. The hypothesis R1 wants is
`∀ k < n, …`, which unfolds to `∀ k, k < n → …`, so the proof is the function `fun k _ => hf.intervalIntegrable _ _`
(the `_` after `k` ignores the proof of `k < n`; the two last `_` are the endpoints, found by unification).
Placeholders: `(f : ℝ → ℝ) (hf : Continuous f) (u : ℕ → ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∀ k < n, IntervalIntegrable f MeasureTheory.volume (u k) (u (k + 1))` | closed |

With the problem's nodes `(a := fun k : ℕ => a + k * h)`, `hsum`'s endpoints come out as `a + ↑k * h`,
`a + ↑(k + 1) * h` and, for `k = 0`, `a + ↑0 * h`. R3 and R4 tidy them.

**R3 · `simp only [Nat.cast_zero, zero_mul, add_zero] at hp`** changes the **context**: inside `hp`,
`a + ↑0 * h` becomes `a`. The lemmas: `Nat.cast_zero : ((0 : ℕ) : ℝ) = 0`, `zero_mul : 0 * x = 0`,
`add_zero : x + 0 = x`. Placeholders: `(a h : ℝ)`, `hp` any hypothesis containing the term.

| Before | After |
|---|---|
| `hp : P (a + ↑0 * h) ⊢ G` | `hp : P a ⊢ G` |

**R4 · `Nat.cast_succ`** changes the **context** (used `at hp`, or added to R3's list): `↑(k + 1) = ↑k + 1`.
Placeholders: `(k : ℕ)`; the lemma holds in any `[AddMonoidWithOne R]`, such as `ℝ`, `ℤ`, `ℂ`.

| Before | After |
|---|---|
| `hp : P ↑(k + 1) ⊢ G` | `hp : P (↑k + 1) ⊢ G` |

After R3 and R4 the right side of `hsum` is literally the goal's integral `∫ t in a..a + ↑n * h, f t` (bound
variable names do not matter), so `rw [← hsum]` replaces it by the panel sum.

### One sum of panel errors

**R5 · `rw [← Finset.sum_sub_distrib]`** changes the **goal**. The lemma is
`Finset.sum_sub_distrib : ∑ i ∈ s, (u i - v i) = ∑ i ∈ s, u i - ∑ i ∈ s, v i`; right to left it merges a
difference of two sums over the same `s` into one sum of differences. Placeholders:
`{ι G : Type} [AddCommGroup G] (s : Finset ι) (u v : ι → G)` (`G` has `+`, `-`, `0`, commutative: `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, u i - ∑ i ∈ s, v i)` | `⊢ P (∑ x ∈ s, (u x - v x))` |

### The chain of inequalities

**R6 · `calc`** changes the **goal list**: a goal `a ≤ d` becomes one goal per step. `_` as the first term
stands for the goal's left side, and a last step `_ = _` ends at the goal's right side. `≤` and `=` steps
compose to `≤`. Each step is `term := proof`; with `:= ?_` the step is left as a goal, as below. Every
intermediate term (`b`, `c` here) must be typed out in full; only the first `_` and the final `_` are filled in
from the goal.
Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ d` | `⊢ a ≤ b`, `⊢ b ≤ c`, `⊢ c = d` |

**R7 · `Finset.abs_sum_le_sum_abs`** **closes** the triangle inequality for finite sums:
`|∑ i ∈ s, u i| ≤ ∑ i ∈ s, |u i|`. Explicit arguments `(u) (s)`, usually `_ _`. Placeholders:
`{ι : Type} (s : Finset ι) (u : ι → ℝ)` (any linearly ordered additive group works).

Before (after it: no goal left):

```lean-goal
⊢ |∑ i ∈ s, u i| ≤ ∑ i ∈ s, |u i|
```

**R8 · `gcongr with k hk`** changes the **goal and the context**: an inequality between two sums over the
same `s` reduces to the inequality between their terms. `k` names the index, `hk : k ∈ s` its membership
(omit `hk` and it appears as `a✝`). Placeholders: `{ι : Type} (s : Finset ι) (u v : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, u i ≤ ∑ i ∈ s, v i` | `k : ι, hk : k ∈ s ⊢ u k ≤ v k` |

### Using the panel bound on panel `k`

**R9 · `have := hall x`** changes the **context**: it instantiates a `∀` hypothesis at a term and calls the
result `this`. Placeholders: `(Q : ℝ → Prop) (hall : ∀ y, Q y) (x : ℝ)`. In the problem, `hpanel` at the left
node `a + ↑k * h` gives a bound whose right node reads `a + ↑k * h + h`, while the goal says `a + (↑k + 1) * h`.

| Before | After |
|---|---|
| `⊢ G` | `this : Q x ⊢ G` |

**R10 · `rw [show e₁ = e₂ by ring] at hp`** changes the **context**: `show e₁ = e₂ by ring` is a term, an
equation proved on the spot by `ring`, and `rw … at hp` rewrites with it inside `hp`. Placeholders:
`(x c y : ℝ)`.

| Before | After |
|---|---|
| `hp : P (x + c * y + y) ⊢ G` | `hp : P (x + (c + 1) * y) ⊢ G` |

**R11 · `rwa [e] at hp`** **closes** the goal: it is `rw [e] at hp` followed by `assumption` (the rewritten `hp`
must be exactly the goal). Placeholders: `(x z : ℝ) (e : x = z)`.

| Before | After |
|---|---|
| `hp : P x ⊢ P z` | closed |

### Summing the constant

**R12 · `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`** change the **goal**: a sum of a constant
becomes `↑n * c`. The lemmas: `Finset.sum_const : ∑ _x ∈ s, c = s.card • c`,
`Finset.card_range : (Finset.range n).card = n`, `nsmul_eq_mul : n • c = ↑n * c`. `simp` applies all three
by itself, so `_ = _ := by simp` finishes a `calc`. Placeholders: `(n : ℕ) (c : ℝ)`.

| Before | After `rw [Finset.sum_const]` | After `rw [Finset.card_range]` | After `rw [nsmul_eq_mul]` |
|---|---|---|---|
| `⊢ P (∑ _i ∈ Finset.range n, c)` | `⊢ P ((Finset.range n).card • c)` | `⊢ P (n • c)` | `⊢ P (↑n * c)` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: unit panels on `[0, n]`.** The goal is

```lean-goal
⊢ ∑ k ∈ Finset.range n, ∫ (x : ℝ) in ↑k..↑k + 1, f x = ∫ (x : ℝ) in 0..↑n, f x
```

R1 with `(a := fun k : ℕ => (k : ℝ))` and R2 adds the first `hsum` below, and
`simp only [Nat.cast_zero, Nat.cast_succ] at hsum` (R3, R4) turns it into the second, which is the goal
itself (`exact hsum`):

```text
hsum : ∑ k ∈ Finset.range n, ∫ (x : ℝ) in ↑k..↑(k + 1), f x = ∫ (x : ℝ) in ↑0..↑n, f x
hsum : ∑ x ∈ Finset.range n, ∫ (x : ℝ) in ↑x..↑x + 1, f x = ∫ (x : ℝ) in 0..↑n, f x
```

**W2: n errors each `≤ ε`.** From `hε : ∀ k, |u k - v k| ≤ ε`: R5 merges the sums,

```lean-goal
⊢ |∑ k ∈ Finset.range n, u k - ∑ k ∈ Finset.range n, v k| ≤ ↑n * ε
⊢ |∑ x ∈ Finset.range n, (u x - v x)| ≤ ↑n * ε
```

then a `calc` (R6): `_ ≤ ∑ k ∈ Finset.range n, |u k - v k|` by R7, `_ ≤ ∑ _k ∈ Finset.range n, ε` by R8 and
R9, `_ = _` by `simp` (R12). The exercise has the same shape plus the integral split (R1–R4) and the node
rewrite (R10, R11).

---

## Traps

- Without `(a := fun k : ℕ => a + k * h)`, Lean cannot know the nodes and R1 fails to elaborate. In
  `(a := …)` the left `a` is the lemma's parameter name and the right `a` is your variable; that is fine.
- Write `fun k : ℕ => …`: the nodes are indexed by naturals, and `k * h` then inserts the cast `↑k`.
- `hsum` comes out with `a + ↑0 * h` and `↑(k + 1)`. Without R3, `rw [← hsum]` does not find its right side
  in the goal. Without R4, the panel integrals keep the endpoint `a + ↑(k + 1) * h` while the trapezoid sum
  has `a + (↑k + 1) * h`, and the first `calc` step fails with "invalid 'calc' step, left-hand side is …".
- `hpanel (a + ↑k * h)` has right endpoint `a + ↑k * h + h`, not `a + (↑k + 1) * h`; `rw [h]` needs literal
  matches, so rewrite with `show … by ring` (R10) before closing (R11).
- After rewrites the sum's index may print as `x`, next to the integral's own `x`. They are different
  variables; it is only display. When you type the `calc` middle sum, do not copy that text: write
  `∑ k ∈ Finset.range n, |(∫ t in a + k * h..a + (k + 1) * h, f t) - …|` with fresh names `k`, `t`
  (bound variable names do not matter for matching).
- `rw [Finset.sum_sub_distrib]` (left to right) splits a sum; to merge two sums you need `←`.
- `t1 ; t2` runs `t2` on the first goal only; inside a `calc` step, indent the `by` block further than `_`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| integral over `[a, a + n h]` = sum of panel integrals | `have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (f := f) (a := nodes) (n := n) hint` | R1 |
| integrability of a continuous `f` | `fun k _ => hf.intervalIntegrable _ _` | R2 |
| `a + ↑0 * h → a` in `hsum` | `simp only [Nat.cast_zero, zero_mul, add_zero] at hsum` | R3 |
| `↑(k + 1) → ↑k + 1` | `Nat.cast_succ` (add to the `simp only` list) | R4 |
| whole integral → panel sum | `rw [← hsum]` | |
| `∑ u - ∑ v → ∑ (u - v)` | `rw [← Finset.sum_sub_distrib]` | R5 |
| chain `≤` / `=` steps | `calc _ ≤ … := … ⏎ _ ≤ … := … ⏎ _ = _ := …` | R6 |
| `\|∑ u\| ≤ ∑ \|u\|` | `Finset.abs_sum_le_sum_abs _ _` | R7 |
| `∑ u ≤ ∑ v` termwise | `gcongr with k hk` | R8 |
| the panel bound at a node | `have := hpanel x` | R9 |
| fix an endpoint inside a hypothesis | `rw [show e₁ = e₂ by ring] at this` | R10 |
| rewrite, then the hypothesis is the goal | `rwa [e] at this` | R11 |
| `∑ _k ∈ range n, c = ↑n * c` | `simp` (`Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`) | R12 |
| see the state | infoview | |
