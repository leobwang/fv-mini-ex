# E105 · Derivatives with HasDerivAt: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `have`, `refine … ?_`, `rw`, dot notation and
proofs written as terms. **New here:** Mathlib's derivative predicate `HasDerivAt`, the derivative
function `deriv`, the library rules for powers, the identity, `exp`, `sin`, `cos`, and the sum, constant
multiple and product rules, and `congr_deriv` to restate a derivative in a nicer form.

## How to read an entry

Each entry is one tactic or one library lemma. It says what changes (**goal**, **context**, or **goal
list**), gives the lemma's statement, lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- Most lemmas here are **proof terms** you combine, not rewrites. An entry shows a term `t` through
  `have h := t`: the context gains `h` with the statement of `t`, and the goal `G : Prop` stays. That is also
  the way to inspect a combined term in your own proof before you use it.
- Placeholders: `(f g : ℝ → ℝ)` are arbitrary real functions, `(f' g' x c : ℝ)` real numbers, `(n : ℕ)` a
  natural number. The lemmas hold over any *nontrivially normed field* `𝕜` (a field with an absolute value
  that is not discrete: `ℝ`, `ℂ`); this sheet states them for `ℝ`, the only case the exercise needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (the type `Real`). A numeral such as `3` in a real goal is the real number 3 |
| `HasDerivAt f f' x` | `f : ℝ → ℝ` is differentiable at the point `x` and its derivative there is the number `f' : ℝ`, i.e. $f(x + h) = f(x) + f' h + o(h)$ as $h \to 0$. A `Prop` |
| `deriv f x` | a real number: the derivative of `f` at `x` if `f` is differentiable there, and the junk value `0` otherwise (E069). So `deriv` facts come from `HasDerivAt` facts (R10) |
| `fun x => x ^ n` | the function $x \mapsto x^n$; `fun x => x` is the identity |
| `↑n` with `n : ℕ` | the natural number `n` cast into `ℝ` (E063). The power rule has `↑n * x ^ (n - 1)` |
| `x ^ (n - 1)` | a power with a natural-number exponent; `n - 1` is subtraction in `ℕ` (so `3 - 1` is the numeral expression, evaluated by `norm_num`) |
| `f + g`, `f * g` (functions) | the pointwise sum and product: `(f + g) y = f y + g y` holds by definition. The sum and product rules produce this form |
| `(fun y => 3 * y ^ 2) + fun x => x` | the pointwise sum of two lambdas: what R3 and R4 build for $3x^2 + x$ |
| `Real.exp`, `Real.sin`, `Real.cos` | the real exponential, sine and cosine, as functions `ℝ → ℝ` (not lambdas) |
| `hf.add hg` | dot notation: `HasDerivAt.add hf hg`, because `hf : HasDerivAt …` |

Two expressions are *definitionally equal* when they become the same term after unfolding definitions
(`f + g` and `fun y => f y + g y` are). `exact` and `have h : T := t` accept a term whose type is
definitionally equal to the target; `rw` needs the pattern **syntactically** (W2, W3).

---

## Part 1 · `deriv_cubic`

Statement: for every `a : ℝ`, `HasDerivAt (fun x => x ^ 3 + 2 * x) (3 * a ^ 2 + 2) a`, i.e.
$\frac{d}{dx}(x^3 + 2x) = 3x^2 + 2$ at $x = a$. Build the derivative of each piece (R1, R2), combine them
(R3, R4), then restate the derivative in the asked form (R5, R6).

**R1 · `hasDerivAt_pow n x`** changes the **context** (through `have`). The lemma is
`hasDerivAt_pow (n : ℕ) (x : 𝕜) : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x`, the power rule, with
the derivative in this raw form (no simplification). Placeholders: `(n : ℕ) (x : ℝ)`.

| Before | After `have h := hasDerivAt_pow n x` |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x ⊢ G` |

**R2 · `hasDerivAt_id' x`** changes the **context**. The lemma is
`hasDerivAt_id' (x : 𝕜) : HasDerivAt (fun x => x) 1 x`. (Without the prime, `hasDerivAt_id` states it for the
function `id`, which `rw` does not see as `fun x => x`.) Placeholders: `(x : ℝ)`.

| Before | After `have h := hasDerivAt_id' x` |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun x => x) 1 x ⊢ G` |

**R3 · `hf.const_mul c`** changes the **context**. The lemma is
`HasDerivAt.const_mul (c : 𝔸) : HasDerivAt f f' x → HasDerivAt (fun y => c * f y) (c * f') x` (`𝔸` is any
normed algebra over `𝕜`, here `ℝ` itself). Note the argument order: `c` first, then the fact, so the dot form
is `hf.const_mul c`. Placeholders: `(f : ℝ → ℝ) (f' x c : ℝ) (hf : HasDerivAt f f' x)`.

| Before | After `have h := hf.const_mul c` |
|---|---|
| `⊢ G` | `h : HasDerivAt (fun y => c * f y) (c * f') x ⊢ G` |

**R4 · `hf.add hg`** changes the **context**. The lemma is
`HasDerivAt.add : HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (f + g) (f' + g') x`. Both facts must be
at the same point `x`. The function is the pointwise sum `f + g`, not a lambda. Placeholders:
`(f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)`.

| Before | After `have h := hf.add hg` |
|---|---|
| `⊢ G` | `h : HasDerivAt (f + g) (f' + g') x ⊢ G` |

**R5 · `refine hf.congr_deriv ?_`** changes the **goal**. The lemma is
`HasDerivAt.congr_deriv : HasDerivAt f f' x → f' = g' → HasDerivAt f g' x`: keep the function, replace the
derivative by an equal number. The new goal is that equation. As a term: `hf.congr_deriv (by norm_num)`.
Placeholders: `(f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x)`.

| Before | After |
|---|---|
| `⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

Lean also checks that the function of `hf` matches the goal's function, up to definitional equality: a fact
about `(fun y => 3 * y ^ 2) + fun x => x` proves a goal about `fun x => 3 * x ^ 2 + x` (W1).

**R6 · `norm_num`** **closes** numeral arithmetic: casts of numerals `↑4 = 4`, `ℕ` exponents such as
`4 - 1 = 3`, `* 1`. It does not reorder products: after R5 in W1 it leaves `3 * (2 * b) = 6 * b`, which `ring`
closes (TACTIC_STATES, "Closing"). Placeholders: `(b : ℝ)`.

| Before | After `norm_num` |
|---|---|
| `⊢ ↑4 * b ^ (4 - 1) + 5 * 1 = 4 * b ^ 3 + 5` | no goals |

### Worked combination W1 (not the exercise's polynomial)

**W1: $\frac{d}{dx}(3x^2 + x) = 6b + 1$ at $x = b$.** One `have` with R1, R3, R2, R4:
`have h := ((hasDerivAt_pow 2 b).const_mul 3).add (hasDerivAt_id' b)`. Then R5, R6, `ring`:

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun x => 3 * x ^ 2 + x) (6 * b + 1) b` | `h : HasDerivAt ((fun y => 3 * y ^ 2) + fun x => x) (3 * (↑2 * b ^ (2 - 1)) + 1) b ⊢ HasDerivAt (fun x => 3 * x ^ 2 + x) (6 * b + 1) b` |

```lean-goal
⊢ 3 * (↑2 * b ^ (2 - 1)) + 1 = 6 * b + 1
⊢ 3 * (2 * b) = 6 * b
```

---

## Part 2 · `hasDerivAt_exp_mul_sin`

Statement: for every `x : ℝ`, the function $t \mapsto e^t \sin t$ has derivative
$e^x \sin x + e^x \cos x$ at `x`. This is the product rule (R9) applied to R7 and R8, and the asked
derivative is already in the form the rule produces, so no R5 is needed.

**R7 · `Real.hasDerivAt_exp x`** changes the **context**. The lemma is
`Real.hasDerivAt_exp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x`. Placeholders: `(x : ℝ)`.

| Before | After `have h := Real.hasDerivAt_exp x` |
|---|---|
| `⊢ G` | `h : HasDerivAt Real.exp (Real.exp x) x ⊢ G` |

**R8 · `Real.hasDerivAt_sin x`, `Real.hasDerivAt_cos x`** change the **context**. The lemmas are
`HasDerivAt Real.sin (Real.cos x) x` and `HasDerivAt Real.cos (-Real.sin x) x`. Placeholders: `(x : ℝ)`.

| Before | After `have hs := Real.hasDerivAt_sin x` | After `have hc := Real.hasDerivAt_cos x` |
|---|---|---|
| `⊢ G` | `hs : HasDerivAt Real.sin (Real.cos x) x ⊢ G` | `hc : HasDerivAt Real.cos (-Real.sin x) x ⊢ G` |

**R9 · `hf.mul hg`** changes the **context**. The lemma is
`HasDerivAt.mul : HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (f * g) (f' * g x + f x * g') x`, the
product rule $(fg)' = f'g + fg'$, in exactly this order of terms. Placeholders:
`(f g : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)`.

| Before | After `have h := hf.mul hg` |
|---|---|
| `⊢ G` | `h : HasDerivAt (f * g) (f' * g x + f x * g') x ⊢ G` |

**W2: $\frac{d}{dy}(y e^y)$** with R2, R7, R9: `have h := (hasDerivAt_id' x).mul (Real.hasDerivAt_exp x)`, then
`exact h` closes the goal although the function is written differently (definitional equality):

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun y => y * Real.exp y) (1 * Real.exp x + x * Real.exp x) x` | `h : HasDerivAt ((fun x => x) * Real.exp) (1 * Real.exp x + x * Real.exp x) x ⊢ HasDerivAt (fun y => y * Real.exp y) (1 * Real.exp x + x * Real.exp x) x` |

---

## Part 3 · `deriv_two_mul`

Statement: if `hf : HasDerivAt f 3 0`, then `deriv (fun x => 2 * f x) 0 = 6`. Build the `HasDerivAt` fact for
`fun x => 2 * f x` from `hf` (R3), turn `deriv` into its value (R10), finish the numbers (R6).

**R10 · `rw [hf.deriv]`** changes the **goal**. The lemma is
`HasDerivAt.deriv : HasDerivAt f f' x → deriv f x = f'`. `rw` looks for `deriv f x` with `f` written
**exactly** as in the fact, so build the fact for the goal's own function. Placeholders:
`(f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x)`.

| Before | After |
|---|---|
| `⊢ P (deriv f x)` | `⊢ P f'` |

R3 produces the lambda `fun y => c * f y`, so `rw [(hf.const_mul c).deriv]` matches a goal
`deriv (fun x => c * f x) …` directly. R4 and R9 produce `f + g` and `f * g`, which `rw` does not match
against a lambda: restate the fact first (W3).

**W3: `deriv` of a sum.** With `hg : HasDerivAt g 5 1`, the goal is `deriv (fun x => g x + x) 1 = 6`. State the
fact with the goal's function, `have h : HasDerivAt (fun x => g x + x) (5 + 1) 1 := hg.add (hasDerivAt_id' 1)`
(accepted by definitional equality), then `rw [h.deriv]` and `norm_num`:

| Before | After `have h : … := …` |
|---|---|
| `⊢ deriv (fun x => g x + x) 1 = 6` | `h : HasDerivAt (fun x => g x + x) (5 + 1) 1 ⊢ deriv (fun x => g x + x) 1 = 6` |

```lean-goal
⊢ 5 + 1 = 6
```

---

## Traps

- The rules return derivatives in raw form, `↑3 * a ^ (3 - 1) + 2 * 1`, not `3 * a ^ 2 + 2`. An `exact` of the
  combined fact fails on the derivative; wrap it in `congr_deriv` (R5) and prove the equation with `norm_num`
  (R6), adding `ring` if it leaves a product to reorder.
- `HasDerivAt.const_mul` takes the constant **before** the fact (`HasDerivAt.const_mul c hf`); dot notation
  `hf.const_mul c` puts `hf` in the right slot for you. Its function is `fun y => c * f y`, constant on the
  left: `2 * x` matches it with `f` the identity (R2), but `x * 2` does not.
- `hasDerivAt_id` (no prime) is about `id`; use `hasDerivAt_id'` for `fun x => x`.
- `rw [h.deriv]` fails with "Did not find an occurrence of the pattern `deriv (g + fun x => x) 1` in the target
  expression" when `h` came from R4 or R9: state `h` with the goal's lambda first (W3).
- Do not try to compute `deriv` by unfolding it or with `simp` alone: go through a `HasDerivAt` fact (R10).
  `deriv f x` of a non-differentiable `f` is `0`, so no `deriv` value follows from the formula alone.
- The derivative in R9 is `f' * g x + f x * g'`; if the asked derivative has the terms in another order or
  shape, you need R5.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| derivative of `x ^ n` | `hasDerivAt_pow n x` | R1 |
| derivative of `fun x => x` | `hasDerivAt_id' x` | R2 |
| derivative of `fun y => c * f y` | `hf.const_mul c` | R3 |
| derivative of a sum `f + g` | `hf.add hg` | R4 |
| derivative of a product `f * g` | `hf.mul hg` | R9 |
| `exp`, `sin`, `cos` | `Real.hasDerivAt_exp x`, `Real.hasDerivAt_sin x`, `Real.hasDerivAt_cos x` | R7, R8 |
| see what a combined term proves | `have h := …` and the infoview | R1–R4 |
| right function, derivative in the wrong form | `h.congr_deriv (by norm_num)` / `refine h.congr_deriv ?_` | R5, R6 |
| numeral arithmetic with `↑k`, `k - 1` | `norm_num` (then `ring` if needed) | R6 |
| `deriv f x` from `hf : HasDerivAt f f' x` | `rw [hf.deriv]` | R10 |
| fact about `f + g` for a goal with a lambda | `have h : HasDerivAt (fun x => …) _ _ := …` | W3 |
| see the state | infoview | |
