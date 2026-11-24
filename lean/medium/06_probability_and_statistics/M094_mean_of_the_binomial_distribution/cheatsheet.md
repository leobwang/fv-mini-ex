# M094 · Mean of the binomial distribution: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's binomial measure
`ProbabilityTheory.binomial`, Bochner integrals `∫ … ∂μ` against a measure, the unit interval as a subtype
of `ℝ`, finite sums over `Finset`s (`∑ k ∈ s, f k`), binomial coefficients `Nat.choose`, ℕ → ℝ casts, and
the tactics `exact_mod_cast` and `linear_combination`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommSemiring R]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it; `ℝ` meets
  all of the brackets below, `ℕ` all except `[CommRing R]` and `[AddCommGroup G]` (no negatives).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `unitInterval` | the set `[0, 1] ⊆ ℝ` (`Set.Icc 0 1`) |
| `p : ↑unitInterval` | `p` is an element of the subtype `{x : ℝ // 0 ≤ x ∧ x ≤ 1}`: a real together with a proof it lies in `[0, 1]` |
| `↑p` | the real number inside `p` (`p.val`, written `(p : ℝ)` in your own code) |
| `Bin(n, p)` | `binomial n p : Measure ℕ`, the law of the number of successes in `n` independent trials with success probability `p` |
| `∫ (k : ℕ), f k ∂μ` | the integral of `f : ℕ → ℝ` against the measure `μ`; for `μ = Bin(n, p)` this is the expectation `E[f(K)]`, `K ~ Bin(n, p)` |
| `Finset.Iic n` | the finite set `{0, 1, …, n}` (`I`nterval, `i`nfinite below, `c`losed above, inside ℕ) |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` |
| `∑ k ∈ s, f k` | the finite sum of `f k` over `k ∈ s` |
| `s.sum g` | the same sum, printed this way when the summand is a bare function `g` (R12) |
| `n.choose k` | the binomial coefficient `C(n, k)` (a natural number; `0` when `k > n`) |
| `Nat.choose 0 k` | `n.choose k` with `n = 0`; a numeral is printed in prefix form (`case zero` goal) |
| `↑(n.choose k)`, `↑k`, `↑(m + 1)` | a natural number cast into `ℝ`. `↑(m + 1)` (cast of a sum) and `↑m + 1` are different terms |
| `c • x` | scalar multiplication; here `c x : ℝ`, so it is ordinary `*` (R5) |
| `n - k` | truncated ℕ subtraction: `0` when `k > n` |
| `∀ k ∈ s, Q k` | `∀ k, k ∈ s → Q k` |
| `a✝`, `inst✝` | an unnamed (inaccessible) hypothesis, e.g. from `intro k _`, or an unnamed type-class instance |
| `case zero`, `case succ` | the two goals after splitting `n` into `0` and `m + 1` |

---

## Part 1 · `binomial_mean`

Statement: for `n : ℕ` and `p ∈ [0, 1]`, `∫ k, (k : ℝ) ∂(binomial n p) = n * p`, i.e. `E[K] = n p` for
`K ~ Bin(n, p)`. The proof is the textbook one: write the expectation as the finite sum
`∑_{k=0}^{n} C(n,k) p^k (1-p)^(n-k) · k`, drop `k = 0`, use `k C(n,k) = n C(n-1,k-1)`, and recognise
`n p (p + (1 - p))^(n-1)`.

### From the integral to a finite sum

**R1 · `rw [integral_binomial]`** changes the **goal**. The lemma is
`∫ x, f x ∂Bin(n, p) = ∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑p ^ k * (1 - ↑p) ^ (n - k)) • f k`: the integral
against the binomial law is the sum of `f k` weighted by `P(K = k)`. Placeholders: `(n : ℕ) (q : unitInterval)
(f : ℕ → ℝ)`. (In Mathlib `f` may take values in any complete normed real vector space `E`; you need `E = ℝ`.)

| Before | After |
|---|---|
| `⊢ P (∫ (k : ℕ), f k ∂Bin(n, q))` | `⊢ P (∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • f k)` |

**R2 · `rw [← Nat.range_succ_eq_Iic]`** changes the **goal**. The lemma is
`Nat.range_succ_eq_Iic n : Finset.range (n + 1) = Finset.Iic n`; `←` turns `Iic n` into `range (n + 1)`, the
form R4 and R14 are stated in. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Finset.Iic n)` | `⊢ P (Finset.range (n + 1))` |

### Case split on `n`

**R3 · `rcases n with _ | m`** changes the **goal list and the context**: one goal per form of `n`, `0` or
`m + 1`. `cases n with | zero => t₀ | succ m => t₁` makes the same two goals and runs `t₀`, `t₁` on them.
Placeholders: `(P : ℕ → Prop) (n : ℕ)`. Why split: the identity `k C(n,k) = n C(n-1,k-1)` needs `n - 1`, and
writing `n = m + 1` avoids ℕ subtraction. In the problem the `zero` goal is a sum over `range (0 + 1)` with
the single term `k = 0`, which is `0`; `simp` closes it.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `m : ℕ ⊢ P (m + 1)` |

### Splitting off the `k = 0` term

**R4 · `rw [Finset.sum_range_succ']`** changes the **goal**. The lemma is
`∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0`: it peels off the first term and shifts the
index. Placeholders: `{M : Type} [AddCommMonoid M]` (a commutative `+` with `0`; `ℕ`, `ℝ`), `(f : ℕ → M) (n : ℕ)`.
With `n = m + 1` the goal's range is `range (m + 1 + 1)`, so the remaining sum runs over `range (m + 1)`.
(`Finset.sum_range_succ`, without `'`, peels off the *last* term instead.)

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range (n + 1), f k)` | `⊢ P (∑ k ∈ Finset.range n, f (k + 1) + f 0)` |

**R5 · `smul_eq_mul`** changes the **goal**: `a • b = a * b` when the scalars and the vectors are the same
type. Placeholders: `{α : Type} [Mul α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R6 · `simp only [Nat.cast_zero, mul_zero, add_zero]`** changes the **goal**: `↑0 = 0`, `c * 0 = 0`,
`s + 0 = s`, so the `k = 0` term disappears. In the problem, pass R5 in the same `simp only` list. Placeholders:
`(s c : ℝ)`. `simp only` may rename the bound variable of a sum (`k` becomes `x`); that changes nothing.

| Before | After |
|---|---|
| `⊢ P (s + c * ↑0)` | `⊢ P s` |

### The termwise identity

Prove it as `have key : ∀ k ∈ Finset.range (m + 1), (summand) = (new summand) := by …`, with the summand
copied from the goal (casts written out: `(p : ℝ)`, `((k + 1 : ℕ) : ℝ)`).

**R7 · `intro k hk`** on a goal `∀ k ∈ s, Q k` changes the **context and the goal**: it adds `k` and
`hk : k ∈ s` and leaves `Q k`. `intro k _` does the same and names the membership `a✝`. Placeholders:
`{ι : Type} (s : Finset ι) (Q : ι → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ k ∈ s, Q k` | `k : ι, hk : k ∈ s ⊢ Q k` |

**R8 · `Nat.add_one_mul_choose_eq n k`** is a fact in ℕ (here added to the **context** with `have`):
`(n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)`, i.e. `(k + 1) C(n + 1, k + 1) = (n + 1) C(n, k)`,
the absorption identity with no subtraction. Placeholders: `(n k : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` | `e : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) ⊢ G` |

**R9 · `exact_mod_cast e`** **closes** the goal. It moves casts outward (`↑a * ↑b` → `↑(a * b)`,
`↑a = ↑b` → `a = b`) in both the goal and `e`, then matches them. Use it to turn an ℕ identity into the same
identity in ℝ: `have h' : (ℝ statement) := by exact_mod_cast Nat.add_one_mul_choose_eq m k`. Placeholders:
`(a b c d : ℕ)`.

| Before | After |
|---|---|
| `e : (a + 1) * b = c * (d + 1) ⊢ ↑(a + 1) * ↑b = ↑c * ↑(d + 1)` | no goals |

**R10 · `rw [show a + 1 - (b + 1) = a - b by omega]`** changes the **goal**. `show T by omega` is a proof of
`T` built on the spot; `omega` proves linear facts about `ℕ`/`ℤ`, truncated subtraction included. Needed
because `ring` and `linear_combination` treat `a + 1 - (b + 1)` as an unknown unrelated to `a - b`.
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a + 1 - (b + 1))` | `⊢ P (a - b)` |

**R11 · `linear_combination e * h`** **closes** a goal `L = R` when `L - R - e * (h.lhs - h.rhs)` is `0` by
`ring`. Here `e` is any expression and `h` an equation; `h.symm` is `h` read right to left (`b = a` becomes
`a = b`). Placeholders: `{R : Type} [CommRing R] (a b c d : R)` (`ℝ` qualifies). To find `e`, compare the goal
with `h`: if each side of the goal is a side of `h` times the same product (up to reordering), `e` is that
product; if the sides come in the opposite order, use `h.symm`.

| Before | After |
|---|---|
| `h : b = a ⊢ c * a + d = c * b + d` | no goals (`linear_combination c * h.symm`) |

### Resumming

**R12 · `rw [Finset.sum_congr rfl key]`** changes the **goal**. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x)
→ s₁.sum f = s₂.sum g`; with `rfl` for the first argument it rewrites a sum over `s` termwise. The left side
of `key` must be the goal's summand as Lean prints it (bound-variable names do not matter). Placeholders:
`{ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M) (key : ∀ k ∈ s, f k = g k)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ s, f k)` | `⊢ P (s.sum g)` |

**R13 · `rw [← Finset.mul_sum]`** changes the **goal**. The lemma is `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`;
right to left it pulls a constant factor out of the sum. The factor must be the *leftmost* factor of every
summand (`a * f i`). Placeholders: `{ι R : Type} [Semiring R] (s : Finset ι) (f : ι → R) (a : R)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, a * f i)` | `⊢ P (a * ∑ i ∈ s, f i)` |

**R14 · `rw [← add_pow]`** changes the **goal**. `add_pow` is the binomial theorem,
`(x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m)`; right to left it collapses a sum of
exactly this shape, **factor order included**, into a power. Placeholders: `{R : Type} [CommSemiring R]
(x y : R) (n : ℕ)`. In the problem `x = ↑p`, `y = 1 - ↑p`, `n = m`.

| Before | After |
|---|---|
| `⊢ P (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))` | `⊢ P ((x + y) ^ n)` |

**R15 · `rw [add_sub_cancel]`** changes the **goal**: `a + (b - a) = b`. Placeholders:
`{G : Type} [AddCommGroup G] (a b : G)` (a commutative `+` with negatives; `ℝ`, not `ℕ`).

| Before | After |
|---|---|
| `⊢ P (a + (b - a))` | `⊢ P b` |

**R16 · `rw [one_pow]`** changes the **goal**: `1 ^ n = 1`. Placeholders: `{M : Type} [Monoid M] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n)` | `⊢ P 1` |

**R17 · `rw [mul_one]`** changes the **goal**: `a * 1 = a`. Placeholders: `{M : Type} [Monoid M] (a : M)`.
The last `rw` closes the goal by `rfl` once both sides agree.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

### Worked combinations (W1–W2, on statements that are not the exercise's)

**W1: total mass, `∫ _k, (1 : ℝ) ∂(binomial n q) = 1`.** The same pipeline without the index shift. R1, then R2:

```lean-goal
⊢ ∫ (_k : ℕ), 1 ∂Bin(n, q) = 1
⊢ ∑ k ∈ Finset.Iic n, (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • 1 = 1
⊢ ∑ k ∈ Finset.range (n + 1), (↑(n.choose k) * ↑q ^ k * (1 - ↑q) ^ (n - k)) • 1 = 1
```

`simp only [smul_eq_mul, mul_one]` (R5, R17) renames `k` to `x`. The summand has `↑(n.choose x)` first, but
`add_pow` wants it last, so a `key` proved by `ring` reorders it (R12):

```lean-goal
⊢ ∑ x ∈ Finset.range (n + 1), ↑(n.choose x) * ↑q ^ x * (1 - ↑q) ^ (n - x) = 1
⊢ ∑ x ∈ Finset.range (n + 1), ↑q ^ x * (1 - ↑q) ^ (n - x) * ↑(n.choose x) = 1
```

Then R14, R15, and R16 closes it:

```lean-goal
⊢ (↑q + (1 - ↑q)) ^ n = 1
⊢ 1 ^ n = 1
```

**W2: a ℕ identity used in ℝ.** Pascal's rule `Nat.choose_succ_succ' n k : (n + 1).choose (k + 1) =
n.choose k + n.choose (k + 1)`, cast with R9 into `e`, then `linear_combination x * e` (R11):

```lean-goal
⊢ x * ↑((n + 1).choose (k + 1)) = x * ↑(n.choose k) + x * ↑(n.choose (k + 1))
```

---

## Traps

- `m + 1 - (k + 1)` is truncated ℕ subtraction. `ring` and `linear_combination` cannot simplify it to `m - k`;
  rewrite it first with `rw [show m + 1 - (k + 1) = m - k by omega]` (R10).
- `↑(k + 1)` and `↑k + 1` are different terms. Write casts in `have` statements the way the goal prints them:
  `((k + 1 : ℕ) : ℝ)` for `↑(k + 1)`, `(p : ℝ)` for `↑p`. Without the ascription Lean may elaborate the
  expression in the wrong type, and `rw` will not find it in the goal.
- `rw [Finset.sum_congr rfl key]` fails unless `key`'s left side is the goal's summand verbatim, including
  parenthesization (`a * b * c * d` is `((a * b) * c) * d`).
- `rw [← add_pow]` needs the summand in the order `x ^ m * y ^ (n - m) * ↑(n.choose m)`, and `rw [← Finset.mul_sum]`
  needs the constant as the leftmost factor. Choose the right side of `key` so both match.
- `t1 ; t2` runs `t2` on the first goal only; after `cases n`, handle each case (`| zero => …`, `| succ m => …`).
- `bernsteinPolynomial` is banned: Mathlib's Bernstein-polynomial API already contains sums of this shape.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| expectation under `Bin(n, p)` → finite sum | `rw [integral_binomial]` | R1 |
| `Iic n` → `range (n + 1)` | `rw [← Nat.range_succ_eq_Iic]` | R2 |
| split `n` into `0` and `m + 1` | `rcases n with _ \| m`, or `cases n with \| zero => … \| succ m => …` | R3 |
| peel off the `k = 0` term | `rw [Finset.sum_range_succ']` | R4 |
| `•` → `*`, drop the `0` term | `simp only [smul_eq_mul, Nat.cast_zero, mul_zero, add_zero]` | R5, R6 |
| termwise fact over a range | `have key : ∀ k ∈ Finset.range N, … := by intro k _; …` | R7 |
| `(n+1) C(n,k) = C(n+1,k+1) (k+1)` | `Nat.add_one_mul_choose_eq n k` | R8 |
| ℕ identity → ℝ identity | `exact_mod_cast h` | R9 |
| `a + 1 - (b + 1)` → `a - b` | `rw [show a + 1 - (b + 1) = a - b by omega]` | R10 |
| goal = `e *` (an equation) up to `ring` | `linear_combination e * h` (or `h.symm`) | R11 |
| rewrite a sum termwise | `rw [Finset.sum_congr rfl key]` | R12 |
| pull a constant out of a sum | `rw [← Finset.mul_sum]` | R13 |
| binomial sum → `(x + y) ^ n` | `rw [← add_pow]` | R14 |
| `a + (b - a)` → `b`, `1 ^ n` → `1`, `a * 1` → `a` | `rw [add_sub_cancel, one_pow, mul_one]` | R15, R16, R17 |
| see the state | infoview | |
