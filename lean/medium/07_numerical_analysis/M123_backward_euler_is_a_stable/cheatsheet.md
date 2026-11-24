# M123 · Backward Euler is A-stable: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching on `ℕ`, `rw`, `simp`, `have`,
`exact`, `ring`. **New here:** Mathlib's real numbers `ℝ` with `|·|` and `⁻¹`, the arithmetic tactics
`field_simp`, `linarith`, `nlinarith`, `positivity`, `gcongr`, `calc`, and limits written with `Tendsto`.

**The maths.** Backward Euler for the ODE `y' = λy` with step `h` sets `yₙ₊₁ = yₙ + h·λ·yₙ₊₁`. Solved for
`yₙ₊₁` this is `yₙ₊₁ = yₙ / (1 - hλ)`, which is the spec's `beuler lam h y₀` (`lam` is `λ`, a reserved word
in Lean). So `yₙ = rⁿ · y₀` with ratio `r = (1 - hλ)⁻¹`. For `λ ≤ 0` and `h ≥ 0`, `1 - hλ ≥ 1`, so
`0 < r ≤ 1` for every step size `h`: that is A-stability (explicit Euler needs `h|λ| ≤ 2`). For `λ < 0`,
`h > 0`, `r < 1` and `rⁿ → 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal the step leaves alone.
- Placeholders are written as Lean binders. `{M : Type}` is any type; a bracket such as `[Monoid M]` is a
  requirement on `M` (a *type class*: `M` has an associative `*` with a `1`; `ℕ`, `ℝ`, `ℂ` qualify).
  The order lemmas (R7–R11, R14, R18) hold in any ordered field; the entries state them on `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A state containing `|a|` cannot be a code cell in a Markdown table, so it is plain text there and is
  repeated below the table in a `lean-goal` block, exactly as the infoview prints it.

## Reading the goals

| You see | It means |
|---|---|
| `beuler lam h y₀ n` | the `n`-th backward Euler iterate `yₙ` for `y' = lam·y`, step `h`, start `y₀` |
| `beuler lam h y₀ (n + 1)` | `yₙ₊₁`; only this form (and `… 0`) unfolds with R1 |
| `\|a\|` | absolute value of the real number `a` |
| `a⁻¹` | `1 / a`. In `ℝ`, `0⁻¹ = 0` by convention, so lemmas about `⁻¹` need `a ≠ 0` or `1 ≤ a` |
| `(1 - h * lam)⁻¹ ^ n` | `((1 - h·lam)⁻¹)ⁿ`: `⁻¹` binds tighter than `^`, which binds tighter than `*` |
| `Tendsto u atTop (𝓝 L)` | `uₙ → L` as `n → ∞` (`Filter.Tendsto`; `open Filter Topology` lets you write it so) |
| `atTop` | the filter "n large enough" on `ℕ`: the source of the limit |
| `𝓝 L` | the neighbourhood filter of `L` ("arbitrarily close to `L`"): the target of the limit |
| `fun n => r ^ n` | the sequence `n ↦ rⁿ` |
| `case zero`, `case succ` | the two goals made by `induction` (R3) |
| `case hbc`, `case hbc.ha₀`, `case ha₁` | goals made by `gcongr`/`apply`, named after the lemma's hypotheses (`ha₀ : 0 ≤ a`, `ha₁ : a ≤ 1` of R14); a dotted name is a goal inside a goal |
| a second goal with no `case` line | the side goal `0 < a` that `rw [abs_of_pos]` (R10) adds |

---

## Part 1 · `beuler_implicit`

Statement: if `1 - h·lam ≠ 0`, then `yₙ₊₁ = yₙ + h·(lam·yₙ₊₁)`: the explicit formula solves the implicit
equation. Unfold `yₙ₊₁` on both sides, clear the denominator `1 - h·lam`, finish with `ring`.

**R1 · `simp only [f]`** changes the **goal**: `f … (n + 1)` becomes the right-hand side of the `n + 1` line
of `f`'s definition (Lean made one equation lemma per line). `rw [f]` does the same. A term `f … n` with a
variable `n` matches neither `0` nor `n + 1` and stays. Placeholders: `(q y₀ : ℝ) (n : ℕ)`, `geo` as defined
in `guide.lean` (`geo q y₀ (n + 1) = q * geo q y₀ n`).

| Before | After |
|---|---|
| `⊢ P (geo q y₀ (n + 1))` | `⊢ P (q * geo q y₀ n)` |

**R2 · `field_simp`** changes the **goal**: an equation with fractions becomes one without, by multiplying
through by every denominator it can show is `≠ 0`. It looks for hypotheses `b ≠ 0` in the context (in the
exercise: `hne`). It also normalises the result, so expect a reordered equation; follow it with `ring`.
Placeholders: `(a b c d : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `⊢ a / b = c + d * (a / b)` | `⊢ a = b * c + a * d` |

---

## Part 2 · `beuler_stable`

Statement: if `lam ≤ 0` and `h ≥ 0`, then `|yₙ| ≤ |y₀|` for every `n`. First prove the milestone (a helper
theorem of your own, placed after `beuler_implicit`, outside the spec regions):

```
beuler_closed (lam h y₀ : ℝ) (n : ℕ) : beuler lam h y₀ n = (1 - h * lam)⁻¹ ^ n * y₀
```

It is proved by induction (R3, R1, R4, R2) and used in Parts 2 and 3. Then `|yₙ| = |r|ⁿ·|y₀|` (R7, R8), and
`|r| ≤ 1` (R5, R9, R10, R6, R11) gives the bound (R12–R16).

### The closed form by induction

**R3 · `induction n with | zero => … | succ k ih => …`** changes the **goal list and the context**: a goal
about every `n : ℕ` becomes the case `0` and the case `k + 1`, and the second case gets `k` and the
induction hypothesis `ih` about `k`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`. In the guide each case is `?_`
so you can see both goals; in a proof, each `=>` is followed by the tactics that prove that case.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `k : ℕ, ih : P k ⊢ P (k + 1)` |

In the exercise: the `zero` case is `y₀ = r⁰ · y₀`, which `simp [beuler]` closes (R1 plus `pow_zero`,
`one_mul`). In the `succ` case unfold `beuler … (k + 1)` (R1), `rw [ih]`, split the power (R4), then R2.

**R4 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

### Facts about `1 - h·lam`

**R5 · `nlinarith`** **closes** an inequality that follows from the hypotheses once products of pairs of
them are added. `h ≥ 0` and `lam ≤ 0` give `h·lam ≤ 0` only as such a product, so `linarith` fails and
`nlinarith` succeeds on `1 ≤ 1 - h * lam`. Placeholders: `(x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0)`.

| Before |
|---|
| `⊢ 2 ≤ 2 + x * y` |

**R6 · `linarith`** **closes** a goal `≤`, `<`, `=` that is a linear consequence of the hypotheses (adds them
with nonnegative coefficients). In the exercise it proves `0 < 1 - h * lam` from `h1 : 1 ≤ 1 - h * lam`.
Placeholders: `(x : ℝ) (h1 : 1 ≤ x)`.

| Before |
|---|
| `⊢ 0 < x` |

### Absolute values

**R7 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`. Placeholders:
`(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a * b\| | ⊢ P (\|a\| * \|b\|) |

As the infoview prints them:

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R8 · `rw [abs_pow]`** changes the **goal**. The lemma is `abs_pow : |a ^ n| = |a| ^ n`. Placeholders:
`(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| ⊢ P \|a ^ n\| | ⊢ P (\|a\| ^ n) |

As the infoview prints them:

```lean-goal
⊢ P |a ^ n|
⊢ P (|a| ^ n)
```

**R9 · `rw [abs_inv]`** changes the **goal**. The lemma is `abs_inv : |a⁻¹| = |a|⁻¹`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a⁻¹\| | ⊢ P \|a\|⁻¹ |

As the infoview prints them:

```lean-goal
⊢ P |a⁻¹|
⊢ P |a|⁻¹
```

**R10 · `rw [abs_of_pos]`** changes the **goal list**. The lemma is `abs_of_pos : 0 < a → |a| = a`, so the goal
is rewritten and a side goal `0 < a` is added. Write `rw [abs_of_pos (by linarith)]` to close it on the spot
(R6). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a\| | `⊢ P a`, `⊢ 0 < a` |

As the infoview prints them:

```lean-goal
⊢ P |a|
```

**R11 · `inv_le_one_of_one_le₀`** changes the **goal**: the lemma is `1 ≤ a → a⁻¹ ≤ 1`; `apply` it and the
goal becomes its hypothesis, or write `exact inv_le_one_of_one_le₀ h1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a⁻¹ ≤ 1` | `⊢ 1 ≤ a` |

### The bound

**R12 · `calc`** **closes** `a ≤ c` by a chain `a ≤ b`, `_ = c`, each step with its own proof
(`:= term` or `:= by tactics`); `_` stands for the previous right-hand side. Placeholders: `(a b c : ℝ)`. In
the exercise: `|r| ^ n * |y₀| ≤ 1 * |y₀|` (by R13, R14), then `_ = |y₀|` (R16).

| Before |
|---|
| `⊢ a ≤ c` |

**R13 · `gcongr`** changes the **goal**: for `x * c ≤ y * c` it leaves `x ≤ y` ("congruence": the common
factor is dropped). It proves the side condition `0 ≤ c` itself (here `c = |z|`), and closes `x ≤ y` too if
a hypothesis says exactly that. Placeholders: `(f : ℝ → ℝ) (a z : ℝ)`.

| Before | After |
|---|---|
| ⊢ f a * \|z\| ≤ 1 * \|z\| | `⊢ f a ≤ 1` |

As the infoview prints them:

```lean-goal
⊢ f a * |z| ≤ 1 * |z|
```

**R14 · `pow_le_one₀`** changes the **goal list**: the lemma is `0 ≤ a → a ≤ 1 → a ^ n ≤ 1`; `apply` leaves
its two hypotheses as goals. Or `exact pow_le_one₀ h0 h1`. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ^ n ≤ 1` | `⊢ 0 ≤ a`, `⊢ a ≤ 1` |

**R15 · `abs_nonneg`** **closes** `0 ≤ |a|`: `exact abs_nonneg a` (or `abs_nonneg _`). Placeholders:
`(a : ℝ)`.

| Before |
|---|
| ⊢ 0 ≤ \|a\| |

As the infoview prints them:

```lean-goal
⊢ 0 ≤ |a|
```

**R16 · `one_mul`** changes the **goal**: `one_mul : 1 * a = a`; as a term, `one_mul _` proves
`1 * a = a`, the last `calc` step. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

---

## Part 3 · `beuler_tendsto_zero`

Statement: if `lam < 0` and `h > 0`, then `yₙ → 0`. Get `1 < 1 - h·lam` (R5), so `0 ≤ r` (R17) and `r < 1`
(R18). Then `rⁿ → 0` (R19), so `rⁿ·y₀ → 0·y₀` (R20) `= 0` (R21), and `yₙ = rⁿ·y₀` transfers the limit
(R22 with R23 and the closed form).

**R17 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` by looking at the shape of `e` (sums, products,
powers, `⁻¹`, `|·|` of things it knows are positive). For an atom such as `x` or `1 - h * lam` it uses a
hypothesis `c < x` or `c ≤ x` with a numeral `c ≥ 0`. Placeholders: `(x : ℝ) (hx : 2 < x)`.

| Before |
|---|
| `⊢ 0 ≤ x⁻¹` |

**R18 · `inv_lt_one_of_one_lt₀`** changes the **goal**: the lemma is `1 < a → a⁻¹ < 1`. Placeholders:
`(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a⁻¹ < 1` | `⊢ 1 < a` |

**R19 · `tendsto_pow_atTop_nhds_zero_of_lt_one`** changes the **context**. The lemma is
`0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`; `have hlim := lemma h0 h1` adds it. Placeholders:
`(r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1)`.

| Before | After |
|---|---|
| `⊢ G` | `hlim : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R20 · `Filter.Tendsto.mul_const`** changes the **context**. The lemma is: from
`hf : Tendsto f l (𝓝 a)` and a constant `c`, `Tendsto (fun x => f x * c) l (𝓝 (a * c))`. Written with dot
notation, `hf.mul_const c`; it also chains, `(lemma h0 h1).mul_const c`. Placeholders:
`(f : ℕ → ℝ) (a c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : Tendsto (fun x => f x * c) atTop (𝓝 (a * c)) ⊢ G` |

**R21 · `rw [zero_mul] at h`** changes the **context**: `zero_mul : 0 * a = 0` rewrites the hypothesis `h`,
not the goal. Needed because R20 gives the limit `0 * y₀`, and `Tendsto … (𝓝 (0 * y₀))` does not match
`Tendsto … (𝓝 0)`. Placeholders: `(Q : ℝ → Prop) (c : ℝ)`.

| Before | After |
|---|---|
| `h : Q (0 * c) ⊢ Q 0` | `h : Q 0 ⊢ Q 0` |

**R22 · `Filter.Tendsto.congr`** changes the **goal**. The lemma is
`(∀ x, f₁ x = f₂ x) → Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂`: two sequences that agree everywhere have the same
limit. With `h : Tendsto f₁ …`, `h.congr ?_` leaves the pointwise equation; `exact h.congr e` closes the goal
in one go. Note the direction: `f₁` is the sequence you know the limit of. Placeholders:
`(f₁ f₂ : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto f₂ atTop (𝓝 L)` | `⊢ ∀ (x : ℕ), f₁ x = f₂ x` |

**R23 · `e.symm`** (`Eq.symm`) **closes** `a = b` given `e : b = a`. The closed form says `yₙ = rⁿ·y₀`, R22
needs `rⁿ·y₀ = yₙ`: write `fun n => (beuler_closed … n).symm`. Placeholders: `{α : Type} (f g : ℕ → α)`.

| Before |
|---|
| `⊢ f n = g n` |

### Worked combinations (on `geo q y₀ n = qⁿ·y₀`, not the exercise's sequence)

**W1.** `geo_closed : geo q y₀ n = q ^ n * y₀` by `induction n with`: the `zero` case by `simp [geo]`, the
`succ` case by `rw [geo, ih, pow_succ]; ring` (R3, R1, R4).

**W2.** `Tendsto (geo (1 / 2) 5) atTop (𝓝 0)`: build the limit of `(1/2)ⁿ·5` (R19, R20), fix `0 * 5` (R21),
transfer it with W1 (R22, R23).

| After `have hlim := (…).mul_const 5` | After `rw [zero_mul] at hlim` |
|---|---|
| `hlim : Tendsto (fun x => (1 / 2) ^ x * 5) atTop (𝓝 (0 * 5)) ⊢ Tendsto (geo (1 / 2) 5) atTop (𝓝 0)` | `hlim : Tendsto (fun x => (1 / 2) ^ x * 5) atTop (𝓝 0) ⊢ Tendsto (geo (1 / 2) 5) atTop (𝓝 0)` |

---

## Traps

- `λ` is reserved in Lean (it means `fun`), so the spec calls it `lam`.
- `beuler` is `noncomputable` because division on `ℝ` is not computable; this changes nothing in proofs.
- `grind` and `try?` are banned: `grind [beuler]` would do Part 1 without `field_simp`.
- `simp only [beuler]` unfolds `beuler … (n + 1)` but not `beuler … n`: there is nothing to unfold for a
  variable index. That is why Parts 2 and 3 need the closed form, proved by induction.
- `field_simp` clears `1 - h * lam` only because `hne : 1 - h * lam ≠ 0` is in the context. In Part 1 it
  leaves `beuler lam h y₀ n = beuler lam h y₀ n * (1 - h * lam + h * lam)` for `ring`. In the closed
  form's `succ` case the goal has `⁻¹` on both sides; `field_simp` needs no `≠ 0` fact there and closes
  the goal by itself, so a `ring` after it fails with "no goals".
- State the closed form exactly as `(1 - h * lam)⁻¹ ^ n * y₀`; `rw [beuler_closed]` then turns `|yₙ|` into
  `|(1 - h * lam)⁻¹ ^ n * y₀|`, ready for R7, R8.
- `linarith` cannot multiply hypotheses: `h * lam ≤ 0` from `0 ≤ h`, `lam ≤ 0` needs `nlinarith` (R5).
- R20 gives the limit `0 * y₀`, not `0`: rewrite the hypothesis with R21 before R22.
- R22 transfers a limit from `f₁` to `f₂` and needs `f₁ x = f₂ x`: with the closed form oriented
  `yₙ = rⁿ·y₀` you need `.symm` (R23).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `f … (n + 1)` | `simp only [f]` / `rw [f]` | R1 |
| clear denominators | `field_simp` (with `hb : b ≠ 0` in context), then `ring` | R2 |
| statement for all `n : ℕ` | `induction n with \| zero => … \| succ k ih => …` | R3 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R4 |
| inequality needing a product of hypotheses | `nlinarith` | R5 |
| linear inequality | `linarith` | R6 |
| `\|a * b\|`, `\|a ^ n\|`, `\|a⁻¹\|` | `rw [abs_mul, abs_pow]`, `rw [abs_inv]` | R7–R9 |
| `\|a\| → a` when `0 < a` | `rw [abs_of_pos (by linarith)]` | R10 |
| `a⁻¹ ≤ 1` / `a⁻¹ < 1` | `inv_le_one_of_one_le₀ h` / `inv_lt_one_of_one_lt₀ h` | R11, R18 |
| chain of `≤` and `=` | `calc a ≤ b := … ⏎ _ = c := …` | R12 |
| drop a common factor `c ≥ 0` | `gcongr` | R13 |
| `a ^ n ≤ 1` | `pow_le_one₀ h0 h1` | R14 |
| `0 ≤ \|a\|` | `abs_nonneg _` | R15 |
| `1 * a = a` | `one_mul _` | R16 |
| `0 ≤ e` by shape | `positivity` | R17 |
| `rⁿ → 0` | `tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` | R19 |
| `f → a` ⇒ `f·c → a·c` | `hf.mul_const c` | R20 |
| rewrite a hypothesis | `rw [zero_mul] at h` | R21 |
| same limit for equal sequences | `h.congr fun n => (e n).symm` | R22, R23 |
