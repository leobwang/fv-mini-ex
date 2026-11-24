# M098 · Maximum likelihood for a coin: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the casts
`ℕ → ℝ`, the real logarithm `Real.log`, order lemmas used as proof terms (`h.trans`, `h.le`, `h.ne'`,
`Iff.mpr`), and the automation `exact_mod_cast`, `positivity`, `field_simp`, `nlinarith`.

**The math.** Write `p = k / n` (the sample frequency). Then

$$\ell(\theta) - \ell(p) = k\log\frac{\theta}{p} + (n-k)\log\frac{1-\theta}{1-p}
\le k\Big(\frac{\theta}{p} - 1\Big) + (n-k)\Big(\frac{1-\theta}{1-p} - 1\Big) = (n\theta - k) + (n(1-\theta) - (n-k)) = 0,$$

using $\log x \le x - 1$ for $x > 0$ twice, and $k/p = n$, $(n-k)/(1-p) = n$. This is Gibbs' inequality
(cross-entropy ≥ entropy) for the two-point distributions $(p, 1-p)$ and $(\theta, 1-\theta)$. In Lean the
logs of quotients are split with `Real.log_div`, so the bounds read `log θ - log p ≤ θ / p - 1`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `have` or as a proof term. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal that the step leaves alone (used when only the context changes); the
  extra hypothesis `h : … → G` only finishes the example.
- Placeholders are written as Lean binders. A lemma stated for a type class (`[Semifield α]`,
  `[AddGroupWithOne R]`) is used here at `α = ℝ`; each entry names the class.
- **closed** means no goal is left. Every `⊢` cell is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `↑k` | the natural number `k` cast into `ℝ` (`(k : ℝ)` in source). Lean prints every cast as `↑` |
| `↑(n - k)` | **natural** subtraction `n - k` (truncated: `3 - 5 = 0` in `ℕ`), then cast into `ℝ` |
| `↑n - ↑k` | **real** subtraction of the casts. Equal to `↑(n - k)` only when `k ≤ n` (R4) |
| `Real.log x` | natural logarithm. Total function: `Real.log 0 = 0` and `Real.log x = Real.log \|x\|`, so the lemmas need `0 < x` or `x ≠ 0` |
| `↑k / ↑n` | real division. Also total: `x / 0 = 0` |
| `θ` | the coin's heads-probability, a real variable with `h0 : 0 < θ`, `h1 : θ < 1` |
| `a ≠ 0` | `a = 0 → False` |
| `logLik n k θ` | the spec definition `k * Real.log θ + ↑(n - k) * Real.log (1 - θ)`; `unfold` shows the body (R14) |

---

## Part 1 · `mle_bernoulli`

Statement: for `0 < k < n` (naturals) and `0 < θ < 1` (real),
`logLik n k θ ≤ logLik n k (↑k / ↑n)`: the log-likelihood at any `θ` is at most its value at `p = k / n`.

The proof has four phases (see the SKELETON in `problem.lean`): side facts about casts and positivity
(R1–R7), the two Gibbs bounds (R8–R12), the algebraic identity that their weighted right-hand sides sum to
`0` (R13), and the final linear combination (R14–R16).

### Facts about casts `ℕ → ℝ`

**R1 · `exact_mod_cast h`** **closes** the goal when it is `h` up to casts. It moves casts out of the way
(`↑a < ↑b` in `ℝ` is the same as `a < b` in `ℕ`, since the cast preserves order) and then uses `h`.
Placeholders: `(a b : ℕ) (h : a < b)`. It also works for `0 < ↑k` from `0 < k` (the numeral `0` is a cast).

| Before | After |
|---|---|
| `h : a < b ⊢ ↑a < ↑b` | closed |

**R2 · `h₁.trans h₂`** is a **proof term** (lemma `lt_trans`): from `h₁ : a < b` and `h₂ : b < c` it gives
`a < c`. Dot notation: `h₁.trans` means `LT.lt.trans h₁`, found from the type of `h₁`. Combine with R1:
`exact_mod_cast hk0.trans hkn`. Placeholders: `(a b c : ℕ)`.

| Before | After `exact h₁.trans h₂` |
|---|---|
| `h₁ : a < b, h₂ : b < c ⊢ a < c` | closed |

**R3 · `h.le`** is a **proof term** (lemma `le_of_lt`): from `h : a < b` it gives `a ≤ b`. Needed because
`Nat.cast_sub` and `mul_le_mul_of_nonneg_left` take `≤`, not `<`. Placeholders: `(a b : ℕ)`.

| Before | After `exact h.le` |
|---|---|
| `h : a < b ⊢ a ≤ b` | closed |

**R4 · `rw [Nat.cast_sub hmn]`** changes the **goal**. The lemma is
`Nat.cast_sub : m ≤ n → ↑(n - m) = ↑n - ↑m` (for any `[AddGroupWithOne R]`, here `R = ℝ`): the cast of a
natural difference is the difference of the casts, provided nothing was truncated. Placeholders:
`(m n : ℕ) (hmn : m ≤ n)`. In the exercise, store it as a fact first,
`have hcast : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hkn.le`, and `rw [hcast]` later.

| Before | After |
|---|---|
| `⊢ P ↑(n - m)` | `⊢ P (↑n - ↑m)` |

### Positivity side facts

**R5 · `rw [sub_pos]`** changes the **goal**. The lemma is `sub_pos : 0 < a - b ↔ b < a` (`rw` can rewrite
with an `↔` like with an `=`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < a - b` | `⊢ b < a` |

**R6 · `positivity`** **closes** goals `0 < e`, `0 ≤ e`, `e ≠ 0` where `e` is built from `+`, `*`, `/`, `^`,
numerals and casts; for a variable it looks for a hypothesis `0 < x` in the context. It **fails on
subtraction**: it cannot prove `0 < 1 - x / y`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x, hy : 0 < y ⊢ 0 < x / y` | closed |

**R7 · `rw [div_lt_one hb]`** changes the **goal**. The lemma is `div_lt_one : 0 < b → (a / b < 1 ↔ a < b)`
(for a `[Semifield α]` with an order, here `ℝ`). Placeholders: `(a b : ℝ) (hb : 0 < b)`. For
`0 < 1 - ↑k / ↑n`: R5, then R7, then R1.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ a / b < 1` | `⊢ a < b` |

### The Gibbs bound `log x ≤ x - 1`

**R8 · `have g := Real.log_le_sub_one_of_pos hx`** changes the **context**. The lemma is
`Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1` (`x` is implicit: Lean reads it off `hx`).
Placeholders: `(x : ℝ) (hx : 0 < x)`. In the exercise `x` is `θ / p` and then `(1 - θ) / (1 - p)`, and
`hx` is built with R9.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ G` | `g : Real.log x ≤ x - 1 ⊢ G` |

**R9 · `div_pos ha hb`** is a **proof term**, here stored with `have`, so the **context** changes. The lemma
is `div_pos : 0 < a → 0 < b → 0 < a / b`. Placeholders: `(a b : ℝ)`.

| Before | After `have hab := div_pos ha hb` |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ G` | `hab : 0 < a / b ⊢ G` |

**R10 · `sub_pos.mpr h`** is a **proof term**: `Iff.mpr` uses an `↔` from right to left (`.mp` goes left
to right). With `sub_pos : 0 < a - b ↔ b < a` it turns `hba : b < a` into `0 < a - b`; in the exercise
`sub_pos.mpr h1 : 0 < 1 - θ`. Placeholders: `(a b : ℝ)`.

| Before | After `have hab := sub_pos.mpr hba` |
|---|---|
| `hba : b < a ⊢ G` | `hab : 0 < a - b ⊢ G` |

**R11 · `h.ne'`** is a **proof term** (lemma `LT.lt.ne'`): from `ha : 0 < a` it gives `a ≠ 0`. Without the
prime, `ha.ne : 0 ≠ a`, which is the wrong way round for `Real.log_div` and `field_simp`. Placeholders:
`(a : ℝ)`.

| Before | After `have ha' := ha.ne'` |
|---|---|
| `ha : 0 < a ⊢ G` | `ha' : a ≠ 0 ⊢ G` |

**R12 · `rw [Real.log_div hx hy] at g`** changes the **context**: `at g` rewrites the hypothesis `g`
instead of the goal. The lemma is
`Real.log_div : x ≠ 0 → y ≠ 0 → Real.log (x / y) = Real.log x - Real.log y`. Placeholders:
`(x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`. In the exercise: `rw [Real.log_div h0.ne' hp.ne'] at g1`.

| Before | After |
|---|---|
| `g : Real.log (x / y) ≤ c ⊢ Real.log x - Real.log y ≤ c` | `g : Real.log x - Real.log y ≤ c ⊢ Real.log x - Real.log y ≤ c` |

### Algebra: clearing denominators

**R13 · `field_simp`** changes the **goal**: it multiplies out every denominator it can show is nonzero,
leaving an equation without `/`. It finds nonzero-ness from hypotheses `b ≠ 0` or `0 < b` in the context
(and from numerals). Follow it with `ring`. Placeholders: `(a b c : ℝ) (hb : b ≠ 0)`. In the exercise it
turns the identity `↑k * (θ / (↑k / ↑n) - 1) + (↑n - ↑k) * ((1 - θ) / (1 - ↑k / ↑n) - 1) = 0` into a
polynomial equation that `ring` closes; `1 - ↑k / ↑n` has to be seen as `(↑n - ↑k) / ↑n`, so keep
`0 < ↑n - ↑k` (or `↑n - ↑k ≠ 0`) in the context.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a / b + c = 1` | `⊢ a + b * c = b` |

### Assembling the inequality

**R14 · `unfold f`** changes the **goal**: every occurrence of the defined name `f` is replaced by its body.
Placeholders: `f` defined by `noncomputable def f (x : ℝ) : ℝ := 2 * Real.log x` (`noncomputable` because
`Real.log` cannot be evaluated). In the exercise: `unfold logLik`, then `rw [hcast]` (R4).

| Before | After |
|---|---|
| `⊢ P (f x)` | `⊢ P (2 * Real.log x)` |

**R15 · `mul_le_mul_of_nonneg_left hbc ha`** is a **proof term**: multiply both sides of an inequality by a
nonnegative number. The lemma is `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c` (for ordered
types such as `ℝ`). Placeholders: `(a b c : ℝ)`. In the exercise: `mul_le_mul_of_nonneg_left g1 hk.le`
weights the first bound by `↑k` (R3 for `.le`).

| Before | After `have hs := mul_le_mul_of_nonneg_left hbc ha` |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ G` | `hs : a * b ≤ a * c ⊢ G` |

**R16 · `nlinarith [t₁, t₂]`** **closes** a goal `≤`, `<` or `=` (or `False`) that follows by a linear
combination of the context hypotheses and the listed proof terms `tᵢ` (plus pairwise products of them).
After multiplying out, it treats each nonlinear monomial such as `↑k * Real.log θ` as an opaque atom. So
the facts must already contain the right products: pass the weighted bounds from R15, and have the
identity `e` from R13 in the context. `linarith [t₁, t₂]` is the same tactic without the pairwise products;
it suffices whenever the right products are already among the facts (W3). Placeholders: `(a x y : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a * x ≤ a * y, h₂ : a * y = 0 ⊢ a * x ≤ 0` | closed |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a cast fact for a ℕ-difference.** For `hab : a < b` in `ℕ`, prove `(0 : ℝ) < ↑(b - a)` with R4
(using `hab.le`, R3), then R5, then R1:

```lean-goal
⊢ 0 < ↑(b - a)
⊢ 0 < ↑b - ↑a
⊢ ↑a < ↑b
```

**W2: one weighted Gibbs bound.** For `hw : 0 < w`, `hx : 0 < x`: `have g := Real.log_le_sub_one_of_pos
(div_pos hx hw)` (R9, R8) adds `g : Real.log (x / w) ≤ x / w - 1`; `have e : w * (x / w - 1) = x - w` is
closed by `field_simp` alone (R13, which finds `w ≠ 0` from `hw`); then
`nlinarith [mul_le_mul_of_nonneg_left g hw.le]` (R15, R3, R16) closes

```lean-goal
⊢ w * Real.log (x / w) ≤ x - w
```

**W3: split a log inside a hypothesis, then combine.** With `g : Real.log (x / y) ≤ 0`,
`rw [Real.log_div hx.ne' hy.ne'] at g` (R11, R12) gives `g : Real.log x - Real.log y ≤ 0`, and `linarith`
(R16 without products) closes

```lean-goal
⊢ Real.log x ≤ Real.log y
```

---

## Traps

- `↑(n - k)` is natural subtraction cast into `ℝ`, not `↑n - ↑k`. `ring` and `exact_mod_cast` cannot change
  one into the other without a proof of `k ≤ n`: rewrite with `Nat.cast_sub hkn.le` (R4).
- `Real.log` is total (`Real.log 0 = 0`, `Real.log (-x) = Real.log x`), so `Real.log_div` needs `x ≠ 0`,
  `y ≠ 0` and `Real.log_le_sub_one_of_pos` needs `0 < x`. Prove the positivity facts first.
- `h.ne'` gives `a ≠ 0`; `h.ne` gives `0 ≠ a` (R11).
- `positivity` fails on any subtraction, so `0 < ↑n - ↑k` and `0 < 1 - ↑k / ↑n` go through `sub_pos`
  (R5, R7).
- Write the cast in a `have` statement: `(0 : ℝ) < n`, `0 < (k : ℝ) / n`. A bare `0 < k / n` is division in
  `ℕ` (which rounds down) and gives a fact about naturals.
- `nlinarith` sees `↑k * Real.log θ` as one atom. Give it the bounds already multiplied by `↑k` and
  `↑n - ↑k` (R15); it will not discover the weights itself.
- Split the logs (`rw [...] at g1`) before `nlinarith`: it cannot see that `Real.log (θ / p)` equals
  `Real.log θ - Real.log p`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `↑a < ↑b` from `a < b` | `exact_mod_cast h` | R1 |
| `a < c` from `a < b`, `b < c` | `h₁.trans h₂` | R2 |
| `a ≤ b` from `a < b` | `h.le` | R3 |
| `↑(n - m) = ↑n - ↑m` | `Nat.cast_sub hmn` (`hmn : m ≤ n`) | R4 |
| `0 < a - b` → `b < a` | `rw [sub_pos]` | R5 |
| `0 < x / y`, products, casts | `positivity` | R6 |
| `a / b < 1` → `a < b` | `rw [div_lt_one hb]` | R7 |
| `Real.log x ≤ x - 1` | `Real.log_le_sub_one_of_pos hx` | R8 |
| `0 < a / b` as a term | `div_pos ha hb` | R9 |
| use an `↔` right to left | `sub_pos.mpr h` | R10 |
| `a ≠ 0` from `0 < a` | `h.ne'` | R11 |
| split `Real.log (x / y)` in `g` | `rw [Real.log_div hx hy] at g` | R12 |
| clear denominators | `field_simp`, then `ring` | R13 |
| see a definition's body | `unfold f` | R14 |
| multiply an inequality by `a ≥ 0` | `mul_le_mul_of_nonneg_left hbc ha` | R15 |
| linear combination of facts | `nlinarith [t₁, t₂]` (or `linarith [t₁, t₂]`) | R16 |
| see the state | infoview | |
