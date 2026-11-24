# M089 · Mean squared error decomposition: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure-theoretic probability:
measures, the Bochner integral `∫ x, f x ∂μ` (expectation), integrability, `MemLp`, and `Var[X; μ]`.

The mathematics. For a random variable $X$ with $E[X^2] < \infty$ and a constant $c \in \mathbb{R}$,
expand $(X - c)^2 = X^2 - 2cX + c^2$ and integrate term by term (linearity of $E$, $E[c^2] = c^2$ on a
probability space):
$E[(X-c)^2] = E[X^2] - 2c\,E X + c^2 = \big(E[X^2] - (E X)^2\big) + (E X - c)^2 = \operatorname{Var} X + (E X - c)^2.$
Taking $c = E X$ kills the second term, and $(E X - c)^2 \ge 0$ gives the minimization.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a `have` leaves untouched.
- Placeholders are written as Lean binders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)`.
  A bracket such as `[IsProbabilityMeasure μ]` is a requirement (a *type class* instance) that Lean finds
  by itself; the exercise provides it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ω : Type*`, `[MeasurableSpace Ω]` | the sample space, with a σ-algebra of measurable sets (`Type*` = a type in any universe) |
| `Ω : Type u_1`, `inst✝ : IsProbabilityMeasure μ` | how the infoview prints `Type*` (`u_1` is a universe variable) and an unnamed `[…]` instance argument (`inst✝` cannot be referred to by name; Lean finds it by itself) |
| `μ : Measure Ω` | a measure on `Ω` |
| `[IsProbabilityMeasure μ]` | `μ Ω = 1`; it implies `IsFiniteMeasure μ`, which R1 and R5 need |
| `X : Ω → ℝ` | a real random variable (measurability is not assumed separately; it is part of `MemLp` / `Integrable`) |
| `∫ (x : Ω), f x ∂μ` | the integral of `f` against `μ` = the expectation $E f$. It is `0` when `f` is not integrable (a "junk value") |
| `μ[f]` | notation for `∫ x, f x ∂μ`. The infoview always prints the `∫` form |
| `∫ (x : Ω), (fun ω => F ω) x ∂μ` | how `μ[fun ω => F ω]` is printed: the function, applied to `x`. `rw [e]` (R9) removes the application |
| `∫ (a : Ω), f a ∂μ` | the same integral; rewriting renames the bound variable (`x`, `a`, `ω` all mean the same) |
| `∫ (x : Ω), X x ∂μ - c` | the integrand ends at `∂μ`, so this is `(∫ X) - c`, i.e. $E X - c$, not $\int (X - c)$ |
| `Integrable f μ` | `f` is (a.e.-strongly) measurable and $\int \lvert f\rvert\,d\mu < \infty$ |
| `MemLp f 2 μ` | `f` is measurable and $\int \lvert f\rvert^2\,d\mu < \infty$, i.e. $f \in L^2(\mu)$ (needs `E[X²] < ∞`). The exponent `2` lives in `ENNReal` = `ℝ≥0∞` (the extended reals `[0, ∞]`); that is why R1's side condition `one_le_two` is `(1 : ℝ≥0∞) ≤ 2` |
| `Var[X; μ]` | `ProbabilityTheory.variance X μ`, the variance $E[(X - E X)^2]$ |
| `f ^ 2`, `(f ^ 2) x` | the function `x ↦ f x ^ 2` (powers act pointwise on functions), applied to `x`; `Pi.pow_apply` (R13) turns it into `f x ^ 2` |
| `f - g` | the function `x ↦ f x - g x` |
| `μ.real Set.univ` | the measure of the whole space `Set.univ` as a real number: `μ s` itself is in `ℝ≥0∞`, and `μ.real s` is `(μ s).toReal`; `1` for a probability measure (R15) |
| `r • c` | scalar multiplication; for `r c : ℝ` it is just `r * c` (R16) |

---

## Part 1 · `mse_decomposition`

Statement: for `X ∈ L²(μ)` and `c : ℝ`, `μ[fun ω => (X ω - c) ^ 2] = Var[X; μ] + (μ[X] - c) ^ 2`.
The plan: collect integrability facts, rewrite the integrand as `X² - 2cX + c²`, split the integral, and
let `ring` compare with `E[X²] - (E X)² + (E X - c)²`.

### Integrability facts

Every `integral_add` / `integral_sub` needs proofs that both pieces are integrable. Build them first with
`have`. All of these change the **context** only.

**R1 · `MemLp.integrable`** changes the **context**. Lemma: `1 ≤ q → MemLp f q μ → Integrable f μ` on a finite
measure (`L^q ⊂ L¹` when `μ` is finite). Write `hf.integrable one_le_two`; `one_le_two : 1 ≤ 2` is the side
condition. Placeholders: `(μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `have hi : Integrable f μ := hf.integrable one_le_two` |
|---|---|
| `hf : MemLp f 2 μ ⊢ G` | `hi : Integrable f μ ⊢ G` |

**R2 · `MemLp.integrable_sq`** changes the **context**. Lemma: `MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ`
(the square of an `L²` function is in `L¹`). Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `have hs : … := hf.integrable_sq` |
|---|---|
| `hf : MemLp f 2 μ ⊢ G` | `hs : Integrable (fun x => f x ^ 2) μ ⊢ G` |

**R3 · `Integrable.const_mul`** changes the **context**. Lemma: `Integrable f μ → ∀ a, Integrable (fun x => a * f x) μ`.
Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (a : ℝ)`. `hf.const_mul _` lets Lean infer `a` from the stated type.

| Before | After `have ha : … := hf.const_mul a` |
|---|---|
| `hf : Integrable f μ ⊢ G` | `ha : Integrable (fun x => a * f x) μ ⊢ G` |

**R4 · `Integrable.sub`** changes the **context**. Lemma: `Integrable f μ → Integrable g μ → Integrable (f - g) μ`
(`Integrable.add` is the same for `+`). The result is stated with the *function* `f - g`. Give the `have` an
explicit type `Integrable (fun x => f x - g x) μ` (the same fact, accepted by definitional unfolding): that is the
form R10 and R11 match. Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After `have h₀ := hf.sub hg` | After `have h₁ : Integrable (fun x => f x - g x) μ := hf.sub hg` |
|---|---|---|
| `hg : Integrable g μ ⊢ G` | `h₀ : Integrable (f - g) μ ⊢ G` | `h₁ : Integrable (fun x => f x - g x) μ ⊢ G` |

**R5 · `integrable_const`** changes the **context**. Lemma: `[IsFiniteMeasure μ] (c : β) : Integrable (fun x => c) μ`.
Usually passed inline as an argument: `integral_add h (integrable_const _)`. Placeholders: `(c : ℝ)`.

| Before | After `have hc : … := integrable_const c` |
|---|---|
| `c : ℝ ⊢ G` | `hc : Integrable (fun x => c) μ ⊢ G` |

### Rewriting the integrand

**R6 · `funext x`** changes the **goal and the context**: an equation between functions becomes the equation at a
fresh point `x` (function extensionality). Prove the integrand identity this way as a `have e : (fun ω => …) = fun ω => … := by …`.
Placeholders: `(f : Ω → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ (fun x => (f x + a) * (f x - a)) = fun x => f x ^ 2 - a ^ 2` | `x : Ω ⊢ (f x + a) * (f x - a) = f x ^ 2 - a ^ 2` |

**R7 · `ring`** **closes** an identity of commutative rings. It treats every non-arithmetic subterm (`f x`,
`∫ (a : Ω), X a ∂μ`, `Var[…]`) as an unknown, and alpha-equivalent integrals (`∫ (a : Ω), X a ∂μ` and
`∫ (x : Ω), X x ∂μ`) as the same unknown. Used after R6 and at the very end of Part 1.

| Before | After |
|---|---|
| `⊢ (u + v) ^ 2 - 2 * u * v = u ^ 2 + v ^ 2` | no goals |

### Variance and the integral rules

**R8 · `variance_eq_sub`** changes the **goal**. Lemma (probability measure):
`MemLp f 2 μ → Var[f; μ] = ∫ x, (f ^ 2) x ∂μ - (∫ x, f x ∂μ) ^ 2`, i.e. $\operatorname{Var} f = E[f^2] - (E f)^2$.
Note the `(f ^ 2) x` form (R13 fixes it). Placeholders: `(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After `rw [variance_eq_sub hf]` |
|---|---|
| `⊢ P Var[f; μ]` | `⊢ P (∫ (x : Ω), (f ^ 2) x ∂μ - (∫ (x : Ω), f x ∂μ) ^ 2)` |

**R9 · `rw [e]`** with a function equation `e : (fun ω => …) = fun ω => …` changes the **goal**: the integrand is
replaced, and the printed application `(fun ω => …) x` disappears. Placeholders: `(f : Ω → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), (fun ω => (f ω + a) * (f ω - a)) x ∂μ)` | `⊢ P (∫ (ω : Ω), f ω ^ 2 - a ^ 2 ∂μ)` |

**R10 · `integral_add`** changes the **goal**. Lemma:
`Integrable f μ → Integrable g μ → ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`. With the two integrability
proofs given, `rw` looks for the integrand `f a + g a` literally, with `f`, `g` read off those proofs' types
(R4). Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After `rw [integral_add hf hg]` |
|---|---|
| `⊢ P (∫ (x : Ω), f x + g x ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ + ∫ (a : Ω), g a ∂μ)` |

**R11 · `integral_sub`** changes the **goal**. Lemma: the same shape as R10 with `-`. Placeholders as in R10.

| Before | After `rw [integral_sub hf hg]` |
|---|---|
| `⊢ P (∫ (x : Ω), f x - g x ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ - ∫ (a : Ω), g a ∂μ)` |

**R12 · `integral_const_mul`** changes the **goal**. Lemma: `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ`, no integrability
needed (if `f` is not integrable both sides are `0`). It pulls out the *whole* left factor, so
`∫ 2 * c * X a` gives `2 * c * ∫ X a` (`*` groups to the left: `2 * c * X a` is `(2 * c) * X a`).
Placeholders: `(f : Ω → ℝ) (r : ℝ)`.

| Before | After `rw [integral_const_mul]` |
|---|---|
| `⊢ P (∫ (x : Ω), r * f x ∂μ)` | `⊢ P (r * ∫ (a : Ω), f a ∂μ)` |

**R13 · `Pi.pow_apply`** changes the **goal**. Lemma: `(f ^ n) x = f x ^ n`. The `x` is bound by `∫`, so `rw`
cannot reach it (it does not rewrite terms containing a bound variable); `simp only [Pi.pow_apply]` can.
Placeholders: `(f : Ω → ℝ)`.

| Before | After `simp only [Pi.pow_apply]` |
|---|---|
| `⊢ P (∫ (x : Ω), (f ^ 2) x ∂μ)` | `⊢ P (∫ (x : Ω), f x ^ 2 ∂μ)` |

**R14 · `integral_const`** changes the **goal**. Lemma: `∫ x, c ∂μ = μ.real Set.univ • c` (total mass times `c`).
Placeholders: `(c : ℝ)`.

| Before | After `rw [integral_const]` |
|---|---|
| `⊢ P (∫ (x : Ω), c ∂μ)` | `⊢ P (μ.real Set.univ • c)` |

**R15 · `probReal_univ`** changes the **goal**. Lemma: `[IsProbabilityMeasure μ] : μ.real Set.univ = 1`.

| Before | After `rw [probReal_univ]` |
|---|---|
| `⊢ P (μ.real Set.univ)` | `⊢ P 1` |

**R16 · `smul_eq_mul`, `one_mul`** change the **goal**. Lemmas: `a • b = a * b` (for a type acting on itself, such as
`ℝ`) and `1 * a = a`. Placeholders: `(c : ℝ)`.

| Before | After `rw [smul_eq_mul]` | After `rw [one_mul]` |
|---|---|---|
| `⊢ P (1 • c)` | `⊢ P (1 * c)` | `⊢ P c` |

R13–R16 are usually given together: `simp only [Pi.pow_apply, integral_const, probReal_univ, smul_eq_mul, one_mul]`.

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: `E[3 f + 2] = 3 E f + 2`** for integrable `f`. `have h3 : Integrable (fun x => 3 * f x) μ := hf.const_mul 3`
(R3), then `rw [integral_add h3 (integrable_const _)]` (R10 with R5), `rw [integral_const_mul]` (R12), and
`simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]` (R14–R16) closes it:

```lean-goal
⊢ ∫ (x : Ω), 3 * f x + 2 ∂μ = 3 * ∫ (x : Ω), f x ∂μ + 2
⊢ ∫ (a : Ω), 3 * f a ∂μ + ∫ (a : Ω), 2 ∂μ = 3 * ∫ (x : Ω), f x ∂μ + 2
⊢ 3 * ∫ (a : Ω), f a ∂μ + ∫ (a : Ω), 2 ∂μ = 3 * ∫ (x : Ω), f x ∂μ + 2
```

**W2: `Var[f; μ] ≤ E[f²]`.** R8, then R13, then `nlinarith [sq_nonneg (∫ x, f x ∂μ)]` (R18, R19):

```lean-goal
⊢ Var[f; μ] ≤ ∫ (x : Ω), f x ^ 2 ∂μ
⊢ ∫ (x : Ω), (f ^ 2) x ∂μ - (∫ (x : Ω), f x ∂μ) ^ 2 ≤ ∫ (x : Ω), f x ^ 2 ∂μ
⊢ ∫ (x : Ω), f x ^ 2 ∂μ - (∫ (x : Ω), f x ∂μ) ^ 2 ≤ ∫ (x : Ω), f x ^ 2 ∂μ
```

---

## Part 2 · `mean_minimizes_mse`

Statement: `μ[fun ω => (X ω - μ[X]) ^ 2] ≤ μ[fun ω => (X ω - c) ^ 2]`: the constant guess `μ[X]` has the least
mean squared error. Both sides are instances of Part 1 (with `c := μ[X]` and with `c`). Rewrite both, then the
goal is `Var + (E X - E X)² ≤ Var + (E X - c)²`, which follows from `0 ≤ (E X - c)²`.

**R17 · `rw [T]`** with a theorem `T : ∀ k, F k = G k` changes the **goal**. `rw` fixes the open argument `k` at the
*first* match and rewrites only that instance, so two different instances need two `rw [T]`. Your Part 1 theorem
is such a `T` once you give it `μ X hX` and leave `c` open. Placeholders: `(F G : ℝ → ℝ) (T : ∀ k, F k = G k) (a b : ℝ)`.

| Before | After first `rw [T]` | After second `rw [T]` |
|---|---|---|
| `⊢ P (F a) (F b)` | `⊢ P (G a) (F b)` | `⊢ P (G a) (G b)` |

**R18 · `sq_nonneg`** changes the **context** (with `have`) or is passed to R19 as a hint. Lemma: `sq_nonneg t : 0 ≤ t ^ 2`
in any ordered ring such as `ℝ`. Placeholders: `(s t : ℝ)`.

| Before | After `have hst := sq_nonneg (s - t)` |
|---|---|
| `s t : ℝ ⊢ G` | `hst : 0 ≤ (s - t) ^ 2 ⊢ G` |

**R19 · `nlinarith [t₁, …]`** **closes** a goal `≤`, `<`, `=` over `ℝ` that follows linearly from the hypotheses,
the hint terms `tᵢ`, and their pairwise products, after normalizing with `ring` (so `(u - u) ^ 2` counts as `0`).
`linarith [t₁, …]` (no products) also suffices here.

| Before | After `nlinarith [sq_nonneg (x - y)]` |
|---|---|
| `⊢ 2 * x * y ≤ x ^ 2 + y ^ 2` | no goals |

---

## Traps

- `rw [integral_add h₁ h₂]` matches only when `h₁`, `h₂` are stated as `Integrable (fun ω => …) μ` with exactly the
  integrand's pieces. `hf.sub hg` without a type gives `Integrable (f - g) μ`, and `rw` then fails with
  "did not find an occurrence of the pattern `∫ (a : Ω), (f - g) a + … ∂μ`" (R4).
- Split from the outside in: the integrand `X² - 2cX + c²` is `(X² - 2cX) + c²`, so `integral_add` comes first
  (pieces `X² - 2cX` and `c²`), then `integral_sub` on the first piece.
- `rw` cannot rewrite under `∫ x, …` when the term mentions `x`: use `simp only [Pi.pow_apply]` (R13).
- `variance_eq_sub` produces `(X ^ 2) x`, but your `integral_sub` step produces `X a ^ 2`. `ring` sees two different
  unknowns until R13 makes them the same.
- `Var[X; μ]` is a definition that neither `simp` nor `ring` opens; only R8 turns it into integrals, and only with
  the `MemLp X 2 μ` proof.
- `μ[X]` is `0` when `X` is not integrable; that is why `integral_add` / `integral_sub` (R10, R11) need the
  integrability facts R1–R5 (`integral_const_mul`, R12, does not).
- `have e : (fun ω => …) = fun ω => … := by` then `funext ω` and `ring` on the next lines, indented further than
  `have`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Integrable X μ` from `MemLp X 2 μ` | `hX.integrable one_le_two` | R1 |
| `Integrable (fun ω => X ω ^ 2) μ` | `hX.integrable_sq` | R2 |
| `Integrable (fun ω => r * X ω) μ` | `hXi.const_mul _` | R3 |
| `Integrable (fun ω => f ω - g ω) μ` | `have h : Integrable (fun ω => …) μ := hf.sub hg` | R4 |
| `Integrable (fun ω => c) μ` | `integrable_const _` | R5 |
| integrand identity | `have e : (fun ω => …) = fun ω => … := by funext ω; ring` | R6, R7 |
| `Var[X; μ]` → `E[X²] - (E X)²` | `rw [variance_eq_sub hX]` | R8 |
| replace the integrand | `rw [e]` | R9 |
| `∫ (f + g)`, `∫ (f - g)` | `rw [integral_add hf hg]`, `rw [integral_sub hf hg]` | R10, R11 |
| `∫ r * f` → `r * ∫ f` | `rw [integral_const_mul]` | R12 |
| `(X ^ 2) x`, `∫ c`, `μ.real univ`, `1 • c` | `simp only [Pi.pow_apply, integral_const, probReal_univ, smul_eq_mul, one_mul]` | R13–R16 |
| polynomial identity in the integrals | `ring` | R7 |
| use Part 1 at two different `c` | `rw [T args, T args]` | R17 |
| `0 ≤ t ^ 2` | `sq_nonneg t` | R18 |
| close the inequality | `nlinarith [sq_nonneg t]` | R19 |
| see the state | infoview | |
