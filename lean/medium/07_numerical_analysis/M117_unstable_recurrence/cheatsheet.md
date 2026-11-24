# M117 · An unstable recurrence: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `have`, `exact`, `ring`, `simp`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `theorem`, `rw`, `simp`, `have`, `exact`,
`induction`. **New here:** Mathlib's real numbers `ℝ`, `Real.exp`, derivatives as the predicate `HasDerivAt`,
interval integrals `∫ x in a..b, f x` and the integration-by-parts lemma, casts `ℕ → ℝ` and `push_cast`,
`Nat.factorial`, and `linear_combination`.

The mathematics. `I n = ∫₀¹ xⁿ e^(x-1) dx`. Integration by parts with `u = x^(n+1)` (so `u' = (n+1)xⁿ`) and
`v = e^(x-1)` (so `v' = v`) gives `I (n+1) = [u v]₀¹ - (n+1) I n`, and the boundary term is
`1·e⁰ - 0·e⁻¹ = 1`. Part 2: if `J` obeys the same recurrence, the error `eₙ = Jₙ - Iₙ` obeys
`eₙ₊₁ = -(n+1) eₙ` (the `1`s cancel), so `eₙ = (-1)ⁿ n! e₀`. An error of `10⁻¹⁶` in `J₀` becomes `20!·10⁻¹⁶ ≈ 243`
by `n = 20`, although every `Iₙ` lies in `[0, 1]`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a context-only step leaves alone; the hypothesis
  `g : … → G` is there only to finish the example.
- Placeholders are written as Lean binders: `(f : ℝ → ℝ)` is any real function, `(f' x c : ℝ)` any reals.
  No type classes appear: every entry is stated directly on `ℝ`, the only type the exercise uses.
- *Dot notation*: for `h : HasDerivAt f f' x`, `h.exp` means `HasDerivAt.exp h` (Lean looks the name up in the
  namespace of `h`'s type). Chains such as `((hasDerivAt_id' x).sub_const 1).exp` build a derivative fact step
  by step.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∫ (x : ℝ) in a..b, f x` | the interval integral `∫ₐᵇ f(x) dx` (Lebesgue measure; for `a > b` it is `-∫_b^a`). You type `∫ x in a..b, f x` |
| `Set.uIcc a b` | the closed interval between `a` and `b`: `[min a b, max a b]`. `x ∈ Set.uIcc 0 1` is `0 ≤ x ≤ 1` here |
| `∀ x ∈ s, Q x` | `∀ x, x ∈ s → Q x` |
| `HasDerivAt f f' x` | `f` is differentiable at the point `x` with derivative `f'` (a number, not a function) |
| `IntervalIntegrable f MeasureTheory.volume a b` | `f` is integrable on the interval between `a` and `b`; `MeasureTheory.volume` is Lebesgue measure on `ℝ` |
| `Continuous f` | `f : ℝ → ℝ` is continuous everywhere |
| `Real.exp t` | `eᵗ` |
| `↑n` | the natural number `n` cast to `ℝ` (`(n : ℝ)` in source; `((n + 1 : ℕ) : ℝ)` is `↑(n + 1)`: add in `ℕ`, then cast) |
| `↑(n + 1)` vs `↑n + 1` | cast of a sum vs sum of a cast: equal, but different terms for `rw` (R18) |
| `n.factorial`, `Nat.factorial 0` | `n!`, a natural number; `↑n.factorial` is `↑(n.factorial)`, the cast of `n!` |
| `n + 1 - 1` (in `ℕ`) | truncated subtraction on naturals; `simp` reduces it to `n` |
| `x✝` | a hypothesis with no usable name (you wrote `_` for it) |
| `case zero`, `case succ` | the two goals of `induction n` |

---

## Part 1 · `I_succ`

Statement: `I (n + 1) = 1 - (n + 1) * I n`, i.e. `∫₀¹ xⁿ⁺¹ e^(x-1) dx = 1 - (n+1) ∫₀¹ xⁿ e^(x-1) dx`. In the
statement, `(n + 1)` is a real number: Lean prints it as `↑n + 1`.

### Derivatives, one point at a time

**R1 · `intro x hx`** changes the **context and the goal**: a bounded `∀ x ∈ s` gives you the point `x` and the
membership proof `hx`. In a `have … :=` term you write the same thing as `fun x hx => …`, or `fun x _ => …`
when `hx` is not needed (the infoview then calls it `x✝`). Placeholders: `(s : Set ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ x ∈ s, Q x` | `x : ℝ, hx : x ∈ s ⊢ Q x` |

**R2 · `hasDerivAt_pow`** changes the **context**. The lemma is
`hasDerivAt_pow (n : ℕ) (x : ℝ) : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x`: the power rule at one point,
with the exponent cast to `ℝ` and a truncated `n - 1`. Placeholders: `(n : ℕ) (x : ℝ)`.

| Before | After `have hd := hasDerivAt_pow n x` |
|---|---|
| `⊢ G` | `hd : HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x ⊢ G` |

**R3 · `simpa using e`** **closes** the goal: it runs `simp` on the type of `e` and on the goal, then closes the
goal with the simplified `e`. Use it when `e` is "the right fact in the wrong form". `simp` rewrites
`k + 1 - 1` to `k` and `↑(k + 1)` to `↑k + 1` on both sides, so they meet. Placeholders: `(k : ℕ)
(Q : ℝ → ℕ → Prop)`. With R2 at exponent `n + 1`: `simpa using hasDerivAt_pow (n + 1) x`.

| Before | After |
|---|---|
| `e : Q (↑(k + 1)) (k + 1 - 1) ⊢ Q (↑k + 1) k` | no goals |

**R4 · `hasDerivAt_id'`** changes the **context**: `hasDerivAt_id' (x : ℝ) : HasDerivAt (fun x => x) 1 x`.
(The unprimed `hasDerivAt_id` states it for the function `id`, which `simp` and `rw` see as a different term.)

| Before | After `have hd := hasDerivAt_id' x` |
|---|---|
| `⊢ G` | `hd : HasDerivAt (fun x => x) 1 x ⊢ G` |

**R5 · `HasDerivAt.sub_const`** changes the **context**: subtracting a constant keeps the derivative,
`h.sub_const c : HasDerivAt (fun x => f x - c) f' x`. Placeholders: `(f : ℝ → ℝ) (f' x c : ℝ)
(h : HasDerivAt f f' x)`.

| Before | After `have h2 := h.sub_const c` |
|---|---|
| `⊢ G` | `h2 : HasDerivAt (fun x => f x - c) f' x ⊢ G` |

**R6 · `HasDerivAt.exp`** changes the **context**: the chain rule for `exp`,
`h.exp : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x`. Same placeholders as R5.

| Before | After `have h2 := h.exp` |
|---|---|
| `⊢ G` | `h2 : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x ⊢ G` |

**R7 · `HasDerivAt.congr_deriv`** changes the **goal**: `h.congr_deriv : f' = g' → HasDerivAt f g' x`. The chain
R4 → R5 → R6 produces the derivative `Real.exp (x - 1) * 1`; to get the stated `Real.exp (x - 1)` you prove the
equation of the two derivative values (here by `ring`). In term form: `h.congr_deriv (by ring)`.
Placeholders: `(f : ℝ → ℝ) (f' g' x : ℝ) (h : HasDerivAt f f' x)`.

| Before | After `refine h.congr_deriv ?_` |
|---|---|
| `⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

### Integrability and integration by parts

**R8 · `Continuous.intervalIntegrable`** changes the **goal**: a continuous function is integrable on every
interval, `Continuous.intervalIntegrable (hf : Continuous f) (a b : ℝ) : IntervalIntegrable f volume a b`. In
term form: `(by fun_prop : Continuous fun x : ℝ => …).intervalIntegrable _ _` (the `_ _` are `a b`, found by
unification). Shorter and immune to the cast trap below: `(Continuous.intervalIntegrable (by fun_prop) _ _)`,
where Lean reads the function off the type that integration by parts (R10) expects. Placeholders:
`(f : ℝ → ℝ) (a b : ℝ)`.

| Before | After `apply Continuous.intervalIntegrable` |
|---|---|
| `⊢ IntervalIntegrable f MeasureTheory.volume a b` | `⊢ Continuous f` |

**R9 · `fun_prop`** **closes** `Continuous f` when `f` is built from constants, `x`, `+`, `-`, `*`, `^` and
continuous functions such as `Real.exp`. Write the function's type in the `by fun_prop : Continuous fun x : ℝ => …`
ascription, with the cast exactly as it appears in `hu` (`((n + 1 : ℕ) : ℝ) * x ^ n`).

**R10 · `intervalIntegral.integral_mul_deriv_eq_deriv_mul`** changes the **goal** (with `rw`) or the
**context** (with `have hibp := …`). Integration by parts:

`(hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
(hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x`.

Lean reads `u`, `u'`, `v`, `v'` off the types of `hu`, `hv`, so state those with the functions written out
(`fun x : ℝ => x ^ (n + 1)`); the resulting equation then has `x ^ (n + 1) * Real.exp (x - 1)` under the integral,
not `(fun x => …) x`. Placeholders: `(u v u' v' : ℝ → ℝ) (a b : ℝ)`.

| Before | After `rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']` |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, u x * v' x)` | `⊢ P (u b * v b - u a * v a - ∫ (x : ℝ) in a..b, u' x * v x)` |

**R11 · `unfold d`** changes the **goal**: every occurrence of the defined name `d` is replaced by its body
(here `F k := ∫ x in (0:ℝ)..1, x ^ k`, a guide-only definition). `unfold I` turns both `I (n + 1)` and `I n` into
integrals, so `rw [hibp]` can find its left side. Placeholders: `(k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (F k)` | `⊢ P (∫ (x : ℝ) in 0..1, x ^ k)` |

### Boundary values

After `rw [hibp]` the boundary term is `1 ^ (n + 1) * Real.exp (1 - 1) - 0 ^ (n + 1) * Real.exp (0 - 1)`. R12–R14
evaluate it to `1` in one `rw [sub_self, Real.exp_zero, one_pow, one_mul, zero_pow (by simp), zero_mul, sub_zero]`,
which leaves `1 - ∫ (x : ℝ) in 0..1, ↑(n + 1) * x ^ n * Real.exp (x - 1) = 1 - (↑n + 1) * ∫ …`. (The reference
solution uses an equivalent `simp only [...]` list; its extra names `ne_eq`, `Nat.add_eq_zero_iff`, `one_ne_zero`,
`and_false`, `not_false_eq_true` are how `simp` proves R13's side goal `n + 1 ≠ 0`.) Plain `simp` does more than
this: it also cancels `1 - ·` on both sides and turns `↑(n + 1)` into `↑n + 1` inside the integral, so the
function you write in R16 must then be the one `simp` left.

**R12 · `sub_self`, then `Real.exp_zero`** change the **goal**: `sub_self : a - a = 0` and
`Real.exp_zero : Real.exp 0 = 1`. Placeholders: `(a : ℝ)`.

| Before | After `rw [sub_self]` | After `rw [Real.exp_zero]` |
|---|---|---|
| `⊢ P (Real.exp (a - a))` | `⊢ P (Real.exp 0)` | `⊢ P 1` |

**R13 · `zero_pow`** changes the **goal list**: `zero_pow : n ≠ 0 → 0 ^ n = 0`, so `rw [zero_pow]` rewrites and
adds the side goal `n ≠ 0` (`simp` proves `k + 1 ≠ 0`). Inside a longer `rw [...]` write `zero_pow (by simp)`
to close it on the spot (`(by simp)` is the proof of `n ≠ 0`; Lean finds `n` when it matches `0 ^ (k + 1)`). Placeholders: `(k : ℕ)`, the base `(0 : ℝ)`.

| Before | After `rw [zero_pow]` |
|---|---|
| `⊢ P (0 ^ (k + 1))` | `⊢ P 0`, `⊢ k + 1 ≠ 0` |

**R14 · `one_pow`, `one_mul`, `zero_mul`, `sub_zero`** change the **goal**: `1 ^ n = 1`, `1 * a = a`,
`0 * a = 0`, `a - 0 = a`. In the exercise R12 leaves `1 ^ (n + 1) * 1`; after `one_pow` it is `1 * 1`, which
`one_mul` (or `mul_one : a * 1 = a`) turns into `1`. Placeholders: `(k : ℕ) (b c : ℝ)`.

| Before | After `simp only [one_pow, one_mul, zero_mul, sub_zero]` |
|---|---|
| `⊢ P (1 ^ k * b - 0 * c)` | `⊢ P b` |

### Pulling a constant out of an integral

After the boundary step the integral is `∫ x in 0..1, ↑(n + 1) * x ^ n * Real.exp (x - 1)`. `*` groups to the left,
so this is `(↑(n + 1) * x ^ n) * Real.exp (x - 1)`: not yet of the form `c * f x` that R17 needs.

**R15 · `funext x`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `(f g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : ℝ ⊢ f x = g x` |

**R16 · `rw [show A = B by tac]`** changes the **goal**: `show A = B by tac` is a proof of `A = B` written inline,
and `rw` uses it at once. Needed here because `rw [mul_assoc]` cannot rewrite inside `fun x => …` (the term
contains the bound `x`), so you state the equation of the whole integrand as functions and prove it by
`funext x; ring` (R15, then `ring`). Placeholders: `(c : ℝ) (f g : ℝ → ℝ) (P : (ℝ → ℝ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P fun x => c * f x * g x` | `⊢ P fun x => c * (f x * g x)` |

**R17 · `intervalIntegral.integral_const_mul`** changes the **goal**: `∫ x in a..b, c * f x = c * ∫ x in a..b, f x`.
Placeholders: `(c a b : ℝ) (f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c * f x)` | `⊢ P (c * ∫ (x : ℝ) in a..b, f x)` |

**R18 · `push_cast`** changes the **goal**: it moves casts `↑` inward through `+`, `*` and numerals
(`↑(k + 1) = ↑k + 1`, `↑(a * b) = ↑a * ↑b`), so the two sides use the same form. After it, `ring` (or `rfl`)
finishes `I_succ`. Placeholders: `(k m : ℕ)`, the goal in `ℝ`.

| Before | After |
|---|---|
| `⊢ P ↑((k + 1) * m)` | `⊢ P ((↑k + 1) * ↑m)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `fun x _ => by simpa using hasDerivAt_pow 3 x` proves
`∀ x ∈ Set.uIcc (0:ℝ) 2, HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x` (R1, R2, R3: `simp` turns `↑3` into `3`
and `3 - 1` into `2`).

**W2.** `((hasDerivAt_id' x).sub_const 2).exp.congr_deriv (by ring)` proves the derivative of `e^(x-2)`
(R4 → R5 → R6 → R7).

**W3: integration by parts on `∫₀¹ x eˣ dx`**, `u = x`, `v = eˣ`. After the R10 rewrite (integrability from R8,
R9), the goal holds the raw boundary term and `u' = 1` inside the integral; `simp` (R12, R14) cleans it up:

```lean-goal
⊢ 1 * Real.exp 1 - 0 * Real.exp 0 - ∫ (x : ℝ) in 0..1, 1 * Real.exp x = Real.exp 1 - ∫ (x : ℝ) in 0..1, Real.exp x
```

---

## Part 2 · `error_amplification`

Statement: for `J : ℕ → ℝ` with `hJ : ∀ n, J (n + 1) = 1 - (n + 1) * J n`,
`J n - I n = (-1) ^ n * n.factorial * (J 0 - I 0)`. Induction on `n`; the step uses `I_succ` (Part 1) as a
rewrite rule, exactly like `hJ`.

**R19 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list**: `P n` becomes `P 0` and
`P (n + 1)` with the hypothesis `ih : P n`. In the exercise you may write the cases on separate lines,
`| zero => …` and `| succ n ih => …`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

**R20 · `pow_zero`, `Nat.factorial_zero`, `Nat.cast_one`, `one_mul`** change the **goal**: `a ^ 0 = 1`, `0! = 1`,
`↑(1 : ℕ) = (1 : ℝ)`, `1 * a = a`. Plain `simp` applies all four and closes the base case. Placeholders: `(c : ℝ)`.

| Before | After `simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]` |
|---|---|
| `⊢ P ((-1) ^ 0 * ↑(Nat.factorial 0) * c)` | `⊢ P c` |

**R21 · `rw [hs]` with `hs : ∀ n, a (n + 1) = g n (a n)`** changes the **goal**: `rw` instantiates the `∀` with the
first match it finds (`n := k`). A proved theorem with arguments, such as `I_succ : ∀ n, I (n + 1) = …`, is used the
same way: `rw [I_succ]`. Placeholders: `(a : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a (k + 1))` | `⊢ P (g k (a k))` |

**R22 · `Nat.factorial_succ`** changes the **goal**: `(n + 1)! = (n + 1) * n!`. Placeholders: `(k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (k + 1).factorial` | `⊢ P ((k + 1) * k.factorial)` |

Then R18 (`push_cast`) turns `↑((n + 1) * n.factorial)` into `(↑n + 1) * ↑n.factorial`.

**R23 · `linear_combination e * ih`** **closes** an equation goal `L = R` when `L - R - e * (ih.lhs - ih.rhs)` is
`0` by `ring`. Here `e` is any real expression and `ih : a = b` any equation; several terms
(`e₁ * h₁ + e₂ * h₂`) are allowed. Placeholders: `(a b c : ℝ) (ih : a = b)`. Guide example:
`1 - c * a = 1 - c * b` is `(-c)` times `ih`, so `linear_combination (-c) * ih`.

| Before | After |
|---|---|
| `ih : a = b ⊢ 1 - c * a = 1 - c * b` | no goals |

**W4: error propagation in `aₙ₊₁ = 2aₙ + 1`.** Two solutions `a`, `b`; claim `a n - b n = 2 ^ n * (a 0 - b 0)`.
R19 gives

```lean-goal
⊢ a 0 - b 0 = 2 ^ 0 * (a 0 - b 0)
⊢ a (n + 1) - b (n + 1) = 2 ^ (n + 1) * (a 0 - b 0)
```

`simp` closes the first. In the second, `rw [ha, hb]` (R21) and `linear_combination 2 * ih` (R23); `ring` inside
`linear_combination` knows `2 ^ (n + 1) = 2 * 2 ^ n`.

---

## Traps

- State `hu`'s derivative as `((n + 1 : ℕ) : ℝ) * x ^ n` (cast of the sum), the form `simpa using hasDerivAt_pow …`
  delivers. That cast then appears inside the IBP integral, and the continuity proof for R8/R9 must use the same
  function, or Lean rejects the integrability argument (`((n : ℝ) + 1) * x ^ n` is rejected).
  `(Continuous.intervalIntegrable (by fun_prop) _ _)` avoids the issue: Lean supplies the function itself.
- Plain `simp` on the boundary term goes too far (cancels `1 - ·`, pushes the cast into the integral). Use the
  `rw [...]` list of R12–R14, or write R16's function in the form `simp` left.
- `rw [hibp]` before `unfold I` fails: the goal says `I (n + 1)`, not the integral (R11).
- `rw [intervalIntegral.integral_const_mul]` fails on `↑(n + 1) * x ^ n * Real.exp (x - 1)`: the constant is not the
  outer factor. Reassociate first with R16; `rw [mul_assoc]` cannot do it under `fun x`.
- `↑(n + 1)` and `↑n + 1` are different terms: `rw` and `exact` see the difference, `push_cast`/`simp` remove it
  (R18).
- `linear_combination` needs the coefficient's sign right: the step multiplies the error by `-(n + 1)`, so
  `linear_combination (n + 1) * ih` fails (`ring` is left with a nonzero remainder). Writing the type,
  `(-(n + 1 : ℝ))`, makes the intended real coefficient explicit.
- The step of `error_amplification` rewrites with `I_succ`, so prove `I_succ` first (or keep it `sorry` while you
  work on Part 2; the checker still requires both proofs).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| bounded `∀ x ∈ s` | `intro x hx` / `fun x _ => …` | R1 |
| derivative of `x ^ n` | `hasDerivAt_pow n x` | R2 |
| fact in the wrong form (`n + 1 - 1`, casts) | `simpa using e` | R3 |
| derivative of `x`, of `f x - c`, of `exp (f x)` | `hasDerivAt_id' x`, `h.sub_const c`, `h.exp` | R4–R6 |
| fix the derivative's form | `h.congr_deriv (by ring)` | R7 |
| interval integrability | `(Continuous.intervalIntegrable (by fun_prop) _ _)` | R8, R9 |
| integration by parts | `intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'` | R10 |
| unfold a definition | `unfold I` | R11 |
| `exp (a - a)`, `0 ^ (k+1)`, `1 ^ k`, `1 *`, `0 *`, `- 0` | `rw [sub_self, Real.exp_zero, one_pow, one_mul, zero_pow (by simp), zero_mul, sub_zero]` | R12–R14 |
| reassociate under `fun x` | `rw [show (fun x => …) = fun x => … by funext x; ring]` | R15, R16 |
| `∫ c * f x → c * ∫ f x` | `rw [intervalIntegral.integral_const_mul]` | R17 |
| `↑(a + 1) → ↑a + 1`, `↑(a * b) → ↑a * ↑b` | `push_cast` | R18 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R19 |
| base case `(-1)^0 * ↑0! * c` | `simp` | R20 |
| one step of a recurrence / a proved `∀ n` theorem | `rw [hJ, I_succ]` | R21 |
| `(n + 1)! → (n + 1) * n!` | `rw [Nat.factorial_succ]` | R22 |
| goal = `e` × hypothesis, up to ring | `linear_combination e * ih` | R23 |
| see the state | infoview | |
