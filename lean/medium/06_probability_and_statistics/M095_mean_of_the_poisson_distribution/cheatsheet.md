# M095 · Mean of the Poisson distribution: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's Poisson measure
`ProbabilityTheory.poissonMeasure`, integrals against a measure (`∫ … ∂μ`), infinite series (`HasSum`,
`∑'`), finite sums over `Finset.range`, nonnegative reals `ℝ≥0`, and the casts `ℕ → ℝ`, `ℝ≥0 → ℝ`.

The math. For a rate $r \ge 0$, the Poisson law gives $P(K = n) = p_n := e^{-r} r^n / n!$, and
$\sum_n p_n = 1$. The mean is $E[K] = \sum_n p_n\, n$. The $n = 0$ term is $0$, and
$p_{n+1}(n+1) = r\, p_n$ (because $(n+1)! = (n+1)\, n!$). So the series shifted by one index is $r$
times the total probability, which is $r \cdot 1$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is any goal the step leaves untouched.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[MulOneClass α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ≥0` (also `NNReal`) | the nonnegative reals `{x : ℝ // 0 ≤ x}`; needs `open scoped NNReal` for the notation |
| `↑r` with `r : ℝ≥0` | `r` cast to `ℝ` (forget the proof `0 ≤ r`); written `(r : ℝ)` in source |
| `↑n` with `n : ℕ` | the natural number `n` cast to `ℝ`; written `(n : ℝ)` in source |
| `Po(r)` | `poissonMeasure r : Measure ℕ`, the Poisson law: the measure of `{n}` is `e^{-r} rⁿ / n!` |
| `∫ (k : ℕ), ↑k ∂Po(r)` | the integral of `k ↦ (k : ℝ)` against `Po(r)`: the expectation $E[K]$ |
| `Real.exp x` | $e^x$ |
| `n.factorial` | $n!$ (the notation `n !` needs `open Nat`) |
| `a • b` | scalar multiplication; for a real acting on a real it is `a * b` (R9) |
| `HasSum f a` | the series $\sum_n f(n)$ converges to `a` *unconditionally*: the finite partial sums over any growing family of finite sets of indices tend to `a` (for real series: absolute convergence) |
| `∑' (n : ℕ), f n`, `tsum f` | the value of the series; by definition `0` if it does not converge, so `∑'` alone carries no convergence information |
| `∑ i ∈ Finset.range k, f i` | the finite sum $f(0) + \dots + f(k-1)$ |
| `f : ℕ → ℝ := fun n => …` | a local definition made by `set` (R2): `f` is a name for that function |
| `inst✝ : MulOneClass α` | an unnamed type-class assumption from a `[…]` binder |

---

## Part 1 · `poisson_mean`

Statement: for every rate `r : ℝ≥0`, `∫ k, (k : ℝ) ∂(poissonMeasure r) = r`, i.e. $E[K] = r$ for
$K \sim \mathrm{Po}(r)$. Plan: turn the integral into a series (R1), name its summand `f` (R2), prove the
milestone `HasSum f r` (R4–R16), and read off the series' value (R3).

### From the expectation to a series

**R1 · `rw [integral_poissonMeasure]`** changes the **goal**. The lemma (`ProbabilityTheory.` prefix,
opened in the problem) is `∫ n, g n ∂Po(r) = ∑' n, (Real.exp (-↑r) * ↑r ^ n / ↑n.factorial) • g n`: an
expectation is the probability-weighted sum of the values. Placeholders: `(r : ℝ≥0) (g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (n : ℕ), g n ∂Po(r))` | `⊢ P (∑' (n : ℕ), (Real.exp (-↑r) * ↑r ^ n / ↑n.factorial) • g n)` |

**R2 · `set f : ℕ → ℝ := e with hf`** changes the **context and the goal**: it adds the local
definition `f := e` and the equation `hf : f = e`, and replaces every copy of `e` in the goal by `f`. On
a goal `∑' n, f n` the result prints as `tsum f`. Placeholders: `(c : ℝ)`, here `e = fun n => c * ↑n`.

| Before | After |
|---|---|
| `⊢ P fun n => c * ↑n` | `f : ℕ → ℝ := fun n => c * ↑n, hf : f = fun n => c * ↑n ⊢ P f` |

**R3 · `exact h.tsum_eq`** **closes** the goal. The lemma is `HasSum.tsum_eq : HasSum f a → ∑' b, f b = a`;
`h.tsum_eq` is dot notation for `HasSum.tsum_eq h`. This is the last step: once the milestone
`HasSum f a` is proved, the value of `∑'` follows. Placeholders: `(f : ℕ → ℝ) (a : ℝ) (h : HasSum f a)`.

| Before | After |
|---|---|
| `⊢ ∑' (n : ℕ), f n = a` | closed |

### The milestone, step 1: the shifted series from the total probability

**R4 · `have h1 := hasSum_one_poissonMeasure r`** changes the **context**: the Poisson probabilities sum
to `1`. Statement: `HasSum (fun n => Real.exp (-↑r) * ↑r ^ n / ↑n.factorial) 1`. Placeholders:
`(r : ℝ≥0)`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : HasSum (fun n => Real.exp (-↑r) * ↑r ^ n / ↑n.factorial) 1 ⊢ G` |

**R5 · `have h2 := h.mul_left c`** changes the **context**. The lemma is
`HasSum.mul_left (a₂) : HasSum f a₁ → HasSum (fun i => a₂ * f i) (a₂ * a₁)`. Placeholders:
`(f : ℕ → ℝ) (a c : ℝ) (h : HasSum f a)`. With `r : ℝ≥0` write `h.mul_left (r : ℝ)`: the constant must
live in `ℝ`, like the series.

| Before | After |
|---|---|
| `h : HasSum f a ⊢ G` | `h2 : HasSum (fun i => c * f i) (c * a) ⊢ G` |

**R6 · `rw [mul_one] at h`** changes the **context**: `rw … at h` rewrites the hypothesis `h`, not the
goal. The lemma is `mul_one : a * 1 = a`. Placeholders: `{α : Type} [MulOneClass α] (a : α)` (`α` has `*`
and `1`; `ℝ`, `ℕ`, `ℂ` qualify). Use it on the `↑r * 1` that R5 leaves.

| Before | After |
|---|---|
| `h : P (a * 1) ⊢ P a` | `h : P a ⊢ P a` |

### The milestone, step 2: the summand identity, pointwise

R5 gives a `HasSum` for `fun i => ↑r * p i`, but you need it for `fun n => f (n + 1)`. Prove the two
functions equal (`have e : (fun n => f (n + 1)) = fun i => …`), then `rw [e]` in the goal and `exact`
the hypothesis.

**R7 · `funext n`** changes the **goal and the context**: an equation of functions becomes the equation
at a new arbitrary `n`. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `n : α ⊢ f n = g n` |

**R8 · `simp only [hf]`** changes the **goal**: with `hf : f = fun n => …` (from R2), it replaces `f` by
its body and substitutes the argument (β-reduction). Placeholders: `(c : ℝ) (f : ℕ → ℝ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (f (k + 1))` | `⊢ P (c * ↑(k + 1))` |

**R9 · `smul_eq_mul`** changes the **goal**. The lemma is `a • b = a * b`. Placeholders:
`{α : Type} [Mul α] (a b : α)` (any type with `*`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R10 · `Nat.factorial_succ`** changes the **goal**. The lemma is
`(n + 1).factorial = (n + 1) * n.factorial`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (n + 1).factorial` | `⊢ P ((n + 1) * n.factorial)` |

**R11 · `push_cast`** changes the **goal**: it moves casts `↑` inward, past `*`, `+` and numerals, so
`↑((m + 1) * n)` (one cast of a natural-number product) becomes `(↑m + 1) * ↑n` (a real product). Only
then can real-number tactics see the factors. Placeholders: `(m n : ℕ)`, the goal in `ℝ`.

| Before | After |
|---|---|
| `⊢ P ↑((m + 1) * n)` | `⊢ P ((↑m + 1) * ↑n)` |

**R12 · `field_simp`** changes the **goal**: it multiplies out the denominators of an equation in a
field (`ℝ`), cancelling common factors. It must know each denominator is `≠ 0`: it proves this by itself
for `↑n.factorial` and `↑n + 1`; for other denominators put `hb : b ≠ 0` in the context. The exact shape
it leaves varies, so finish with `ring` (R13). Placeholders: `(a c : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a / ↑n.factorial = c` | `⊢ a = ↑n.factorial * c` |

**R13 · `ring`** **closes** an identity of commutative rings, with symbolic exponents such as
`x ^ (n + 1) = x * x ^ n` included. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ x ^ (n + 1) = x * x ^ n` | closed |

**W3** chains R7, R10 (twice), R11, R12, R13 on the second factorial moment's summand, another identity:

```lean-goal
⊢ x ^ (n + 2) / ↑(n + 2).factorial * (↑(n + 2) * ↑(n + 1)) = x ^ 2 * (x ^ n / ↑n.factorial)
⊢ x ^ (n + 2) / ↑((n + 1 + 1) * ((n + 1) * n.factorial)) * (↑(n + 2) * ↑(n + 1)) = x ^ 2 * (x ^ n / ↑n.factorial)
⊢ x ^ (n + 2) / ((↑n + 1 + 1) * ((↑n + 1) * ↑n.factorial)) * ((↑n + 2) * (↑n + 1)) = x ^ 2 * (x ^ n / ↑n.factorial)
⊢ x ^ (n + 2) * (↑n + 2) = (↑n + 1 + 1) * x ^ 2 * x ^ n
```

### The milestone, step 3: unshift the index

**R14 · `rw [← hasSum_nat_add_iff' 1]`** changes the **goal**. The lemma is
`hasSum_nat_add_iff' k : HasSum (fun n => f (n + k)) (g - ∑ i ∈ Finset.range k, f i) ↔ HasSum f g`:
a series converges to `g` iff its tail from index `k` converges to `g` minus the first `k` terms. Right
to left, `HasSum f g` becomes a statement about the tail. Placeholders: `(f : ℕ → ℝ) (g : ℝ)`.
(The unprimed `hasSum_nat_add_iff` puts the finite sum on the other side: `… g ↔ HasSum f (g + ∑ …)`.)

| Before | After |
|---|---|
| `⊢ HasSum f g` | `⊢ HasSum (fun n => f (n + 1)) (g - ∑ i ∈ Finset.range 1, f i)` |

**R15 · `Finset.sum_range_one`** changes the **goal**. The lemma is `∑ k ∈ Finset.range 1, f k = f 0`;
`simp` applies it by itself. Placeholders: `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range 1, f i)` | `⊢ P (f 0)` |

**R16 · `simpa [l] using h`** **closes** the goal: it simplifies both the goal and `h` with `simp [l]`
and then closes the goal with the simplified `h`. Here `simp` turns `∑ i ∈ Finset.range 1, f i` into
`f 0` (R15), `f 0` into `0` (via `l`), and `a - 0` into `a`. In the exercise pass `[hf]`: `simp` then
unfolds `f` (R8) and sees that the term `n = 0` is `(…) • ↑0 = 0` by itself. Placeholders:
`(f : ℕ → ℝ) (a : ℝ) (h0 : f 0 = 0) (h : HasSum f a)`.

| Before | After |
|---|---|
| `⊢ HasSum f (a - ∑ i ∈ Finset.range 1, f i)` | closed |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: scale a known sum, then read off `∑'`.** From `h : HasSum g 1`, `h.mul_left 3` (R5), then
`rw [mul_one] at h3` (R6), then `exact h3.tsum_eq` (R3) proves `∑' n, 3 * g n = 3`:

| Before | After |
|---|---|
| `⊢ ∑' (n : ℕ), 3 * g n = 3` | `h3 : HasSum (fun i => 3 * g i) (3 * 1) ⊢ ∑' (n : ℕ), 3 * g n = 3` |
| `h3 : HasSum (fun i => 3 * g i) (3 * 1) ⊢ ∑' (n : ℕ), 3 * g n = 3` | `h3 : HasSum (fun i => 3 * g i) 3 ⊢ ∑' (n : ℕ), 3 * g n = 3` |

**W2: unshift a series whose term 0 vanishes.** With `h0 : g 0 = 0` and
`h : HasSum (fun n => g (n + 1)) a`: R14, then `simpa [h0] using h` (R15, R16).

| Before | After |
|---|---|
| `⊢ HasSum g a` | `⊢ HasSum (fun n => g (n + 1)) (a - ∑ i ∈ Finset.range 1, g i)` |

---

## Traps

- Do not compute with `∑'` directly: it is `0` for a divergent series, so lemmas about `∑'` need
  summability side conditions. Prove a `HasSum` (which carries convergence) and convert at the end (R3).
- Prove the summand identity as a function equation with `funext n` (R7) and `rw` it into the goal.
  Do not use `convert … using 1` on a `HasSum`: it leaves side goals about type-class instances that are
  hard to close.
- `h.mul_left r` with `r : ℝ≥0` has the wrong type: write `h.mul_left (r : ℝ)`.
- R5 leaves `↑r * 1`, not `↑r`; `rw [mul_one] at h1` (R6) before matching it against the goal.
- `set` (R2) replaces only an expression that matches the goal's: copy the summand from the goal R1
  leaves, `fun n => (Real.exp (-r) * r ^ n / n.factorial) • (n : ℝ)`. If the goal still shows `∑' …`
  instead of `tsum f`, your `f` differs from the summand, and `simp only [hf]` later will not help.
- After `set` (R2) the goal shows `f`; `simp`/`field_simp` cannot see inside `f` until you unfold it with
  `simp only [hf]` (R8).
- `field_simp` needs the factorial and `↑n + 1` as *real* factors: apply `Nat.factorial_succ` (R10) and
  `push_cast` (R11) first, or it sees one opaque `↑((n + 1) * n.factorial)`.
- `hasSum_nat_add_iff'` (with `'`) has `g - ∑ …`; `hasSum_nat_add_iff` has `g + ∑ …` on the other side.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| expectation under `Po(r)` → series | `rw [integral_poissonMeasure]` | R1 |
| name the summand | `set f : ℕ → ℝ := fun n => … with hf` | R2 |
| `∑' n, f n = a` from `h : HasSum f a` | `exact h.tsum_eq` | R3 |
| Poisson probabilities sum to 1 | `hasSum_one_poissonMeasure r` | R4 |
| scale a series by `c` | `h.mul_left c` | R5 |
| `c * 1 → c` in a hypothesis | `rw [mul_one] at h` | R6 |
| function equation → pointwise | `funext n` | R7 |
| unfold a `set` name | `simp only [hf]` | R8 |
| `a • b → a * b` | `smul_eq_mul` | R9 |
| `(n + 1)! → (n + 1) * n!` | `Nat.factorial_succ` | R10 |
| move casts inward | `push_cast` | R11 |
| clear denominators | `field_simp` | R12 |
| finish the algebra | `ring` | R13 |
| `HasSum f g` → tail from index 1 | `rw [← hasSum_nat_add_iff' 1]` | R14 |
| `∑ i ∈ Finset.range 1, f i → f 0` | `Finset.sum_range_one` (in `simp`) | R15 |
| close after simplifying both sides | `simpa [l] using h` | R16 |
| see the state | infoview | |
