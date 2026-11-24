# H053 · Variance of the binomial distribution: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The mean `E[K] = n p` is problem M094 (milestone 1 here).
**New here:** Mathlib's binomial measure `Bin(n, p)`, Lebesgue integrals `∫ … ∂μ` against it, finite
sums `∑ k ∈ s, f k` (`Finset`), binomial coefficients and the binomial theorem, casts `ℕ → ℝ`, and
Mathlib's variance `Var[X; μ]` with its `L²` side condition `MemLp X 2 μ`.

The math: write `K` for the number of successes and `C(n, k)` for `n.choose k`. Then
`Var K = E[K²] - (E K)²`, `E[K²] = E[K(K-1)] + E[K]`, `E[K] = n p` and `E[K(K-1)] = n(n-1)p²`, so
`Var K = n(n-1)p² + np - n²p² = np(1-p)`. The factorial moment uses the absorption identity
`(a+1)·C(a, b) = (b+1)·C(a+1, b+1)` twice, which turns `k(k-1)·C(m+2, k)` into
`(m+2)(m+1)·C(m, k-2)`, and the binomial theorem `∑ₖ C(m,k) pᵏ (1-p)^(m-k) = (p + (1-p))^m = 1`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{Ω : Type} [MeasurableSpace Ω]` is any type with a σ-algebra
  (`ℕ` has one: all subsets). `μ : Measure Ω` is a measure on it; `[IsProbabilityMeasure μ]` says
  `μ Ω = 1`. A bracket such as `[CommSemiring R]` is a requirement on a type (a *type class*); `ℝ` meets
  every one used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `unitInterval`, `p : ↑unitInterval` | the set `[0, 1] ⊆ ℝ`; `p` is an element of it (a real with a proof that it lies in `[0, 1]`) |
| `↑p` | the real number underlying `p` (coercion out of the subtype) |
| `↑k`, `↑(k + 1)` | the natural number `k`, resp. `k + 1`, cast into `ℝ`. `↑(k + 1)` and `↑k + 1` are equal but different text (R13) |
| `Bin(n, p)` | `binomial n p : Measure ℕ`, mass `C(n, k) pᵏ (1-p)^(n-k)` at each `k ≤ n` |
| `∫ (k : ℕ), f k ∂μ` | the integral (expectation, when `μ` is a probability measure) of `f` against `μ` |
| `∑ k ∈ s, f k` | finite sum over the finite set `s : Finset ℕ`; `s.sum g` is the same with the function `g` written bare |
| `Finset.range n` | `{0, 1, …, n-1}` |
| `Finset.Iic n` | `{0, 1, …, n}` ("interval closed, infinite below", here bounded by `0`) |
| `n.choose k` | the binomial coefficient `C(n, k)`, a natural number (`0` when `k > n`) |
| `a • b` | scalar multiplication; for `a b : ℝ` it is `a * b` (R6) |
| `m - k` on `ℕ` | truncated subtraction: `m - k = 0` when `k > m` (R12) |
| `Var[X; μ]` | the variance of `X : Ω → ℝ` under `μ` |
| `(X ^ 2) x` | the function `X ^ 2` (pointwise square) applied to `x`; equal to `X x ^ 2` (R27) |
| `Integrable f μ` | `f` is measurable (a.e.) and `∫ |f| ∂μ < ∞` |
| `AEStronglyMeasurable f μ` | the measurability half of `Integrable`; automatic on `ℕ` |
| `MemLp f 2 μ` | `f ∈ L²(μ)`: a.e.-strongly measurable and `∫ |f|² ∂μ < ∞`. The `2` is the exponent of `Lᵖ`, of type `ℝ≥0∞` (`[0, ∞]`), not a real number |
| `IsProbabilityMeasure μ` | `μ` has total mass `1`; Lean finds it for `Bin(n, p)` by itself |
| `a✝` | a hypothesis you did not name (`intro k _`); it cannot be referred to |
| `case e_f` | the goal `congr 1` produced for the integrand (R22) |

---

## Part 1 · `binomial_mean` (milestone 1, problem M094)

Statement: `∫ k, (k : ℝ) ∂(binomial n p) = n * p`, i.e. `E[K] = n p`. The same plan as Part 2 with one
peeled term and one absorption identity. The entries the two parts share (R1, R2, R4, R6–R19) are
explained here; Part 2 adds only R3, R5 and R13.

### From the integral to a finite sum

**R1 · `rw [integral_binomial]`** changes the **goal**: an integral against `Bin(n, q)` becomes the finite
weighted sum
`∫ x, f x ∂Bin(n, q) = ∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • f k`.
Placeholders: `(n : ℕ) (q : unitInterval) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℕ), f x ∂Bin(n, q))` | `⊢ P (∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • f k)` |

**R2 · `rw [← Nat.range_succ_eq_Iic]`** changes the **goal**. The lemma is
`Nat.range_succ_eq_Iic n : Finset.range (n + 1) = Finset.Iic n`; right to left it turns `Iic n` into
`range (n + 1)`, the form that R4, R5 and R17 are stated for. Placeholders: `(n : ℕ) (g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.Iic n, g k)` | `⊢ P (∑ k ∈ Finset.range (n + 1), g k)` |

### Split on `n`, peel the vanishing terms

For the mean, split `n = 0 | m + 1` with `cases n with | zero => … | succ m => …` (Lean basics); R3 is
the three-way version Part 2 needs. Peel the `k = 0` term with R4 once, then clean it with R6–R8.

**R4 · `rw [Finset.sum_range_succ']`** changes the **goal**: the **first** term `f 0` is split off and the
rest is reindexed by `k ↦ k + 1`:
`∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0`. Placeholders: `(n : ℕ) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range (n + 1), f k)` | `⊢ P (∑ k ∈ Finset.range n, f (k + 1) + f 0)` |

**R6 · `smul_eq_mul`** changes the **goal**: `a • b = a * b`. `integral_binomial` writes the weight with `•`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R7 · `Nat.cast_zero`, `Nat.cast_one`** change the **goal**: `((0 : ℕ) : ℝ) = 0`, `((1 : ℕ) : ℝ) = 1`.

| Before | After |
|---|---|
| `⊢ P (↑0 + ↑1)` | `⊢ P (0 + 1)` |

**R8 · `zero_mul`, `mul_zero`, `sub_self`, `zero_add`, `add_zero`** change the **goal**: `0 * a = 0`,
`a * 0 = 0`, `a - a = 0`, `0 + a = a`, `a + 0 = a`. Together with R6, R7 inside one
`simp only [...]` they delete the peeled terms. Placeholders: `(s c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (0 + s + c * (0 * (0 - 1)) + c * (1 * (1 - 1)))` | `⊢ P s` |

### One term at a time

**R9 · `intro k hk`** changes the **goal and the context**. `∀ k ∈ s, Q k` is notation for
`∀ k, k ∈ s → Q k`, the shape of the per-term fact `key` that R15 needs. Placeholders:
`(s : Finset ℕ) (Q : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ k ∈ s, Q k` | `k : ℕ, hk : k ∈ s ⊢ Q k` |

**R10 · `Nat.add_one_mul_choose_eq`** changes the **context** (with `have h := …`): the absorption identity
in `ℕ`, `Nat.add_one_mul_choose_eq a b : (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1)`.
Placeholders: `(a b : ℕ)`. Part 1 uses it at `(m, k)`.

| Before | After |
|---|---|
| `⊢ (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1)` | `h : (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1) ⊢ (a + 1) * a.choose b = (a + 1).choose (b + 1) * (b + 1)` |

**R11 · `exact_mod_cast e`** **closes** a goal that is `e` up to casts: here `e : x * y = z * w` in `ℕ`, goal
`(x : ℝ) * y = z * w` in `ℝ`. It is how R10 gets into `ℝ`:
`have h : ((m + 1 : ℕ) : ℝ) * (m.choose k) = … := by exact_mod_cast Nat.add_one_mul_choose_eq m k`.
Placeholders: `(x y z w : ℕ)`.

| Before | After |
|---|---|
| `e : x * y = z * w ⊢ ↑x * ↑y = ↑z * ↑w` | closed |

**R12 · `rw [show a + 1 - (b + 1) = a - b by omega]`** changes the **goal**: `show T by tac` is a term
proving `T`, here by `omega` (a decision procedure for linear arithmetic over `ℕ` and `ℤ`, truncated `-`
included). `ring` cannot do this: on `ℕ`, `a + 1 - (b + 1) = a - b` is not a ring identity. In the
exercise the exponent `m + 1 - (k + 1)` (Part 1) or `m + 2 - (k + 1 + 1)` (Part 2) must become `m - k`,
the exponent `add_pow` produces. Placeholders: `(a b : ℕ)`, `P : ℕ → Prop`.

| Before | After |
|---|---|
| `⊢ P (a + 1 - (b + 1))` | `⊢ P (a - b)` |

**R14 · `linear_combination e * h`** **closes** `L = R` when `L - R - e * (lhs h - rhs h)` is `0` by `ring`.
`e` is any expression; with several facts write `linear_combination e₁ * h₁ + e₂ * h₂`, and `h.symm`
flips a fact. Find `e` by asking: what must I multiply `h` by to get the goal? Placeholders:
`(a b c x : ℝ) (h : a * b = c)`.

| Before | After |
|---|---|
| `h : a * b = c ⊢ x * a * b + 1 = x * c + 1` | closed |

### The whole sum

**R15 · `rw [Finset.sum_congr rfl key]`** changes the **goal**: every term of the sum is rewritten by
`key : ∀ k ∈ s, f k = g' k`. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` keeps the index set.
Placeholders: `(s : Finset ℕ) (f g : ℕ → ℝ)`, here `key : ∀ k ∈ s, f k = 2 * g k`. The left side of `key`
must match the summand exactly as Lean prints it (copy it from the infoview). The bound variable may
come back renamed (`k` → `x`); that is only a name.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ s, f k)` | `⊢ P (∑ x ∈ s, 2 * g x)` |

**R16 · `rw [← Finset.mul_sum]`** changes the **goal**. The lemma is
`Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left it pulls a constant factor out.
The constant must be the **leftmost** factor of every term (that is why `key` puts it first).
Placeholders: `(s : Finset ℕ) (a : ℝ) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, a * f i)` | `⊢ P (a * ∑ i ∈ s, f i)` |

**R17 · `rw [← add_pow]`** changes the **goal**: the binomial theorem
`add_pow x y m : (x + y) ^ m = ∑ k ∈ range (m + 1), x ^ k * y ^ (m - k) * ↑(m.choose k)`, right to left.
The summand must be **exactly** `x ^ k * y ^ (m - k) * ↑(m.choose k)`, in this order. Placeholders:
`(x y : ℝ) (m : ℕ)`; in the exercise `x = ↑p`, `y = 1 - ↑p`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range (m + 1), x ^ k * y ^ (m - k) * ↑(m.choose k))` | `⊢ P ((x + y) ^ m)` |

**R18 · `rw [add_sub_cancel]`** changes the **goal**: `add_sub_cancel a b : a + (b - a) = b`, so
`↑p + (1 - ↑p)` becomes `1`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a + (b - a))` | `⊢ P b` |

**R19 · `one_pow`, then `mul_one`** change the **goal**: `1 ^ m = 1`, `a * 1 = a`. Placeholders:
`(a : ℝ) (m : ℕ)`.

| Before | After `rw [one_pow]` | After `rw [mul_one]` |
|---|---|---|
| `⊢ P (a * 1 ^ m)` | `⊢ P (a * 1)` | `⊢ P a` |

After R19 both sides are the same, and `rw` closes the goal by `rfl`.

---

## Part 2 · `binomial_factorial_moment` (milestone 2)

Statement: `∫ k, (k : ℝ) * ((k : ℝ) - 1) ∂(binomial n p) = n * (n - 1) * (p : ℝ) ^ 2`, i.e.
`E[K(K-1)] = n(n-1)p²`. R1, R2; then split `n` three ways (R3), because only for `n = m + 2` do two
vanishing terms exist to peel.

**R3 · `match n with | 0 => … | 1 => … | m + 2 => …`** changes the **goal list**: one goal per shape of
`n`, with `n` replaced by `0`, `1`, `m + 2` (a new variable `m`). In the tactic form each alternative is
followed by its own tactic block (W3). In `guide.lean` the form `refine match n with | 0 => ?_ | … ` is
used, which leaves the three goals open so you can see them. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `⊢ P 1`, `n m : ℕ ⊢ P (m + 2)` |

**R5 · `Finset.sum_range_succ`** changes the **goal**: the **last** term `f n` is split off,
`∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. For `n = 1`, `simp [Finset.sum_range_succ]` unrolls
the whole sum and closes the goal. Placeholders: `(n : ℕ) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range (n + 1), f k)` | `⊢ P (∑ x ∈ Finset.range n, f x + f n)` |

For `m + 2`: R4 twice, then `simp only` with R6–R8 (W1 shows exactly this on another sum). The per-term
identity needs R10 at `(m, k)` and at `(m + 1, k + 1)`, both moved to `ℝ` with R11, R12 on the exponent,
then R13 before R14:

**R13 · `push_cast at h ⊢`** changes the **context and the goal**: casts are pushed to the leaves,
`↑(m + 2)` becomes `↑m + 2`. Do it before `linear_combination`, so that `h1`, `h2` and the goal speak about
the same atoms `↑m`, `↑k`. Placeholders: `(m k : ℕ) (x : ℝ)`.

| Before | After |
|---|---|
| `h : ↑(m + 2) = ↑k ⊢ ↑(m + 2) * x = ↑k * x` | `h : ↑m + 2 = ↑k ⊢ (↑m + 2) * x = ↑k * x` |

Then R14 with two facts, and R15 → R16 → R17 → R18 → R19 exactly as in Part 1.

---

## Part 3 · `binomial_second_moment` (milestone 3)

Statement: `E[K²] = E[K(K-1)] + E[K]`, as integrals against `Bin(n, p)`. Linearity of the integral, then
a pointwise identity.

**R20 · `integrable_binomial f`** changes the **context** (with `have h := …`): every `f : ℕ → ℝ` is
integrable against `Bin(n, q)`, because `Bin(n, q)` sits on the finite set `{0, …, n}`. Its arguments
`n`, `q` are implicit (Lean finds them from the goal; `(n := n) (p := q)` names them).
Placeholders: `(n : ℕ) (q : unitInterval) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable f Bin(n, q)` | context gains `h : Integrable f Bin(n, q)`; goal unchanged |

**R21 · `rw [← integral_add hf hg]`** changes the **goal**. The lemma is
`integral_add : Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`;
right to left it merges a sum of two integrals into one. Pass `integrable_binomial _` (R20) for both
proofs. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), f x ∂μ + ∫ (x : Ω), g x ∂μ)` | `⊢ P (∫ (a : Ω), f a + g a ∂μ)` |

**R22 · `congr 1`** changes the **goal**: an equation of two integrals against the same `μ` becomes an
equation of the integrands (as functions). Placeholders: `(μ : Measure Ω) (F G : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∫ (x : Ω), F x ∂μ = ∫ (x : Ω), G x ∂μ` | `⊢ (fun x => F x) = fun x => G x` |

**R23 · `funext k`** changes the **goal and the context**: an equation of functions becomes one at a new
point `k`. Then `ring` closes `↑k ^ 2 = ↑k * (↑k - 1) + ↑k`. Placeholders: `(F G : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ F = G` | `k : ℕ ⊢ F k = G k` |

---

## Part 4 · `binomial_variance` (the spec theorem)

Statement: `Var[fun k : ℕ => (k : ℝ); binomial n p] = n * p * (1 - p)`. Build `hL2 : MemLp … 2 …`
(R20, R24, R25), rewrite the variance (R26, R27), then rewrite with milestones 3, 2, 1 and `ring`.

**R24 · `hf.aestronglyMeasurable`** changes the **context** (with `have h := …`): from
`hf : Integrable f μ` you get `AEStronglyMeasurable f μ`. Placeholders: `(μ : Measure Ω) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `hf : Integrable f μ ⊢ AEStronglyMeasurable f μ` | `h : AEStronglyMeasurable f μ ⊢ AEStronglyMeasurable f μ` |

**R25 · `(memLp_two_iff_integrable_sq hm).2 hsq`** changes the **context** (with `have h := …`). The
lemma is `memLp_two_iff_integrable_sq : AEStronglyMeasurable f μ → (MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ)`.
`.2` (also `.mpr`) is the right-to-left direction of an `↔`: give it the integrability of the square and
get `MemLp`. In the exercise both `hm` and `hsq` come from R20 (R24 for `hm`). Placeholders:
`(μ : Measure Ω) (f : Ω → ℝ) (hm : AEStronglyMeasurable f μ) (hsq : Integrable (fun x => f x ^ 2) μ)`.

| Before | After |
|---|---|
| `⊢ MemLp f 2 μ` | `h : MemLp f 2 μ ⊢ MemLp f 2 μ` |

**R26 · `rw [variance_eq_sub hX]`** changes the **goal**. The lemma is
`variance_eq_sub : MemLp X 2 μ → Var[X; μ] = ∫ x, (X ^ 2) x ∂μ - (∫ x, X x ∂μ) ^ 2`, for a probability
measure `μ` (`binomial n p` is one; Lean finds that instance itself). Placeholders:
`(μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)`.

| Before | After |
|---|---|
| `⊢ P Var[X; μ]` | `⊢ P (∫ (x : Ω), (X ^ 2) x ∂μ - (∫ (x : Ω), X x ∂μ) ^ 2)` |

**R27 · `simp only [Pi.pow_apply]`** changes the **goal**: `Pi.pow_apply : (f ^ a) i = f i ^ a`. With
`X = fun k => ↑k`, `simp` also β-reduces, so `((fun k => ↑k) ^ 2) x` becomes `↑x ^ 2`, which is the left
side of milestone 3 (up to the bound variable's name, which `rw` ignores). Placeholders:
`(f : ℕ → ℝ) (x : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((f ^ 2) x)` | `⊢ P (f x ^ 2)` |

### Worked combinations (W1–W5, on objects that are not the exercise's)

**W1: peel two terms, clean up.** `∑ k ∈ range (m + 2), c k • (↑k * (↑k - 1))`: R4 twice gives

```lean-goal
⊢ ∑ k ∈ Finset.range m, c (k + 1 + 1) • (↑(k + 1 + 1) * (↑(k + 1 + 1) - 1)) + c (0 + 1) • (↑(0 + 1) * (↑(0 + 1) - 1)) + c 0 • (↑0 * (↑0 - 1)) = ∑ k ∈ Finset.range m, c (k + 1 + 1) * (↑(k + 1 + 1) * (↑(k + 1 + 1) - 1))
```

and one `simp only [smul_eq_mul, Nat.cast_zero, zero_add, Nat.cast_one, zero_mul, sub_self, mul_zero, add_zero]`
deletes the two peeled terms and closes it. Note `0 + 1`, `k + 1 + 1`: R4 twice writes indices this way,
not as `1`, `k + 2`.

**W2: constant times a binomial sum.** R16 then R17, with `x = y = 1`:

```lean-goal
⊢ ∑ k ∈ Finset.range (m + 1), a * (1 ^ k * 1 ^ (m - k) * ↑(m.choose k)) = a * 2 ^ m
⊢ a * ∑ i ∈ Finset.range (m + 1), 1 ^ i * 1 ^ (m - i) * ↑(m.choose i) = a * 2 ^ m
⊢ a * (1 + 1) ^ m = a * 2 ^ m
```

and `norm_num` closes the last one.

**W3: the tactic `match`** with three alternatives `| 0 => …`, `| 1 => …`, `| m + 2 => …`, each with its
own tactic block.

**W4: an `ℕ` fact in `ℝ`.** `have h : (2 : ℝ) * a = b + 3 := by exact_mod_cast e` (R11), then
`linear_combination -x * h` (R14) closes `↑b * x + 3 * x = 2 * ↑a * x`.

**W5: the variance pipeline on another measure** `μ : Measure ℕ` with every `f` integrable, `E[K] = 2`,
`E[K²] = 5`: R25, R26, R27 give

```lean-goal
⊢ ∫ (x : ℕ), ((fun k => ↑k) ^ 2) x ∂μ - (∫ (x : ℕ), ↑x ∂μ) ^ 2 = 1
⊢ ∫ (x : ℕ), ↑x ^ 2 ∂μ - (∫ (k : ℕ), ↑k ∂μ) ^ 2 = 1
⊢ 5 - 2 ^ 2 = 1
```

(the last after `rw [h1, h2]`), and `norm_num` closes it.

---

## Traps

- `rw [h]` needs the left side of `h` to appear literally. `↑(k + 1)` and `↑k + 1` are different text;
  so are `k + 1 + 1` and `k + 2`, and `(m + 2).choose (k + 1 + 1)` and `(m + 2).choose (k + 2)`. State `key`
  with the summand exactly as the infoview prints it after peeling, and use `push_cast` (R13) only
  inside the proof of `key`.
- `ℕ` subtraction is truncated. `m + 2 - (k + 1 + 1) = m - k` needs `omega` (R12), not `ring`; and
  `↑(n - 1)` is NOT `↑n - 1` in `ℝ` when `n = 0`. The statement writes `(n : ℝ) - 1`, subtraction in `ℝ`.
- `add_pow` (R17) only matches the summand `x ^ k * y ^ (m - k) * ↑(m.choose k)` in this order, and
  `← Finset.mul_sum` (R16) only pulls out a factor that is leftmost in every term. Arrange `key`'s right
  side as `const * (x ^ k * y ^ (m - k) * ↑(m.choose k))`.
- `variance_eq_sub` needs `MemLp X 2 μ`, not `Integrable X μ`. Get it from R25; `integrable_binomial`
  (R20) gives both `hm` (via R24) and the integrability of the square.
- After `variance_eq_sub` the square is `((fun k => ↑k) ^ 2) x`, a power of a function. `rw` with
  milestone 3 fails until `simp only [Pi.pow_apply]` (R27) has made it `↑x ^ 2`.
- `t1 ; t2` runs `t2` on the first goal only. After `match`/`cases`, prove each case in its own branch.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| integral against `Bin(n, p)` → finite sum | `rw [integral_binomial, ← Nat.range_succ_eq_Iic]` | R1, R2 |
| split `n` into `0`, `1`, `m + 2` | `match n with \| 0 => … \| 1 => … \| m + 2 => …` | R3 |
| peel the first / last term of `∑ k ∈ range (n + 1)` | `rw [Finset.sum_range_succ']` / `Finset.sum_range_succ` | R4, R5 |
| `•` → `*`, `↑0` → `0`, kill zero terms | `simp only [smul_eq_mul, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_self, zero_add, add_zero]` | R6–R8 |
| per-term fact over a `Finset` | `have key : ∀ k ∈ s, … := by intro k _; …` | R9 |
| `(a+1)·C(a,b) = C(a+1,b+1)·(b+1)` in `ℝ` | `have h : … := by exact_mod_cast Nat.add_one_mul_choose_eq a b` | R10, R11 |
| `ℕ` exponent arithmetic | `rw [show m + 2 - (k + 1 + 1) = m - k by omega]` | R12 |
| `↑(m + 2)` → `↑m + 2` in facts and goal | push_cast at h1 h2 ⊢ | R13 |
| goal = combination of equations | `linear_combination e₁ * h₁ + e₂ * h₂` | R14 |
| rewrite every term of a sum | `rw [Finset.sum_congr rfl key]` | R15 |
| constant out of a sum | `rw [← Finset.mul_sum]` | R16 |
| binomial theorem backwards | `rw [← add_pow]` | R17 |
| `p + (1 - p)` → `1`, `1 ^ m`, `* 1` | `rw [add_sub_cancel, one_pow, mul_one]` | R18, R19 |
| any `f` integrable against `Bin(n, p)` | `integrable_binomial _` | R20 |
| `∫ f + ∫ g` → `∫ (f + g)` | `rw [← integral_add hf hg]` | R21 |
| integrals equal ← integrands equal | `congr 1; funext k` | R22, R23 |
| `X ∈ L²` | `(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hsq` | R24, R25 |
| `Var` → `E[X²] - E[X]²` | `rw [variance_eq_sub hL2]; simp only [Pi.pow_apply]` | R26, R27 |
| polynomial identity in `ℝ` | `ring` | |
| see the state | infoview | |
