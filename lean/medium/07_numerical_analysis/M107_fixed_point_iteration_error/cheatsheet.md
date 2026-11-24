# M107 · Fixed-point iteration error: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` with `|·|` and
`‖·‖`, iterated functions `f^[n]`, the linear-arithmetic tactics `linarith`/`nlinarith`, `gcongr`, and limits
of sequences written with `Filter.Tendsto`.

The mathematics. `f : ℝ → ℝ` is `K`-Lipschitz, `|f x - f y| ≤ K |x - y|` with `0 ≤ K`, and `p` is a fixed
point, `f p = p`. The iterates are `xₙ = f^[n] x₀`. One step contracts the error by `K`:
`|f x - p| = |f x - f p| ≤ K |x - p|`. Induction gives `|xₙ - p| ≤ Kⁿ |x₀ - p|`; with `K < 1` the
right side tends to 0, so `xₙ → p`. The a posteriori bound `|xₙ₊₁ - p| ≤ K/(1-K) · |xₙ₊₁ - xₙ|` bounds the
unknown error by the computable step size.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change (or that
  the step reads).
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a context-changing step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- "closed" means no goal is left.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | real numbers, natural numbers `0, 1, 2, …` |
| `\|x\|` | absolute value of `x : ℝ` (Mathlib's `abs`) |
| `‖x‖` | the norm of `x`; on `ℝ` it equals `\|x\|` (R21) |
| `f^[n] x` | `f` applied `n` times to `x` (`Nat.iterate f n x`); `f^[0] x = x` |
| `f (f^[n] x₀)` | the same as `f^[n + 1] x₀`, written with the last step outside (R4) |
| `x : ℝ := f^[n] x₀` | a local definition made by `set` (R8): `x` is a name for that term |
| `fun n => u n` | the sequence `n ↦ u n` (a function `ℕ → ℝ`) |
| `Tendsto u atTop (𝓝 L)` | `u n → L` as `n → ∞`. `Filter.Tendsto` is Mathlib's general notion of limit |
| `atTop` | "`n → ∞`" (`Filter.atTop`: eventually large `n`) |
| `𝓝 L` | "close to `L`" (`nhds L`, the neighbourhoods of `L`); needs `open Topology` |
| `↑n` | the natural number `n` cast into `ℝ` |
| `inst✝ : Monoid M` | an unnamed type-class assumption from a `[…]` binder |
| `case zero`, `case succ` | the two goals made by `induction` |

---

## Part 1 · `iterate_error`

Statement: `|f^[n] x₀ - p| ≤ K ^ n * |x₀ - p|` (the a priori bound), given `0 ≤ K`, the Lipschitz hypothesis
`hf`, and `hp : f p = p`.

### Induction on `n`

**R1 · `induction n with | zero => … | succ n ih => …`** changes the **goal list**: the goal `P n` becomes
`P 0` and `P (n + 1)` with the induction hypothesis `ih : P n`. Each alternative must be finished after its
`=>`; Mathlib's `induction' n with n ih` makes the same split but leaves both goals open. Placeholders:
`(P : ℕ → Prop) (n : ℕ)`. In the exercise `P n` is the bound for `n`, and `ih` is the bound for `n`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `Function.iterate_zero_apply`** changes the **goal**. The lemma is `f^[0] x = x`. Placeholders:
`{α : Type} (g : α → α) (y : α)`.

| Before | After |
|---|---|
| `⊢ P (g^[0] y)` | `⊢ P y` |

**R3 · `pow_zero`, then `one_mul`** change the **goal**. The lemmas are `c ^ 0 = 1` and `1 * a = a`.
Placeholders: `{M : Type} [Monoid M] (c a : M)` (M has an associative `*` with unit `1`; `ℝ` qualifies).
In the `zero` case, plain `simp` applies R2 and R3 by itself and then closes `|x₀ - p| ≤ |x₀ - p|`.

| Before | After `rw [pow_zero]` | After `rw [one_mul]` |
|---|---|---|
| `⊢ P (c ^ 0 * a)` | `⊢ P (1 * a)` | `⊢ P a` |

**R4 · `Function.iterate_succ_apply'`** changes the **goal**. The lemma is `f^[n.succ] x = f (f^[n] x)`:
it peels off the **last** application of `f`, which is where `hf` applies. Placeholders:
`{α : Type} (g : α → α) (n : ℕ) (y : α)`.

| Before | After |
|---|---|
| `⊢ P (g^[n + 1] y)` | `⊢ P (g (g^[n] y))` |

### Chaining the one-step estimate

**R5 · `calc`** changes the **goal list**: a goal `a ≤ d` is proved as a chain `a = b`, `b ≤ c`, `c = d`, each
step `_ rel rhs := proof`. Mixed `=`, `≤`, `<` steps combine to the strongest relation that follows. A step
written `:= ?_` stays open as its own goal. Placeholders: `(a b c d : ℝ)`. The first term after `calc` must be
the goal's left side (syntactically, up to unfolding), the last right side the goal's right side.

| Before | After (`?_` for every step) |
|---|---|
| `⊢ a ≤ d` | `⊢ a = b`, `⊢ b ≤ c`, `⊢ c = d` |

**R6 · `hQ _ _`** **closes** a goal that is an instance of a `∀` hypothesis: `hQ : ∀ x y, Q x y` applied to two
`_` has type `Q ?x ?y`, and Lean finds `?x`, `?y` by matching the goal. Placeholders:
`{α : Type} (Q : α → α → Prop) (a b : α)`. In the exercise this is `hf _ _ : |f ?x - f ?y| ≤ K * |?x - ?y|`.

| Before | After |
|---|---|
| `⊢ Q a b` (with `hQ : ∀ (x y : α), Q x y` in the context) | closed |

**R7 · `gcongr`** changes the **goal**: for `c * a ≤ c * b` it leaves `a ≤ b` ("generalized congruence":
compare the two sides piece by piece). The side condition `0 ≤ c` is closed from the context (by assumption or
`positivity`); if it cannot be, it stays as an extra goal. It also closes `a ≤ b` itself when that is a
hypothesis (in the exercise: `ih`). Placeholders: `(c a b : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ c * a ≤ c * b` | `⊢ a ≤ b` |

The last calc step, `K * (K ^ n * a) = K ^ (n + 1) * a`, is `ring` (TACTIC_STATES, "Closing").

**W1: a fixed point used backwards.** With `hq : g q = q`, the goal `|g y - q| = |g y - g q|` is closed by
`rw [hq]`: it rewrites the `g q` on the right to `q`, and `rw` closes `|g y - q| = |g y - q|` by `rfl`. This
is the first step of every one-step estimate.

```lean-goal
⊢ |g y - q| = |g y - g q|
```

**W2.** Induction on the doubling map, `(fun x => 2 * x)^[n] y = 2 ^ n * y`: R1, then R2, R3 in `zero` and
R4, `rw [ih]`, `ring` in `succ`. Start state:

```lean-goal
⊢ (fun x => 2 * x)^[n] y = 2 ^ n * y
```

---

## Part 2 · `aposteriori_error`

Statement: `|f^[n + 1] x₀ - p| ≤ K / (1 - K) * |f^[n + 1] x₀ - f^[n] x₀|`, now with `K < 1`. Name
`x = f^[n] x₀` (R8), peel the last step (R4), prove two facts with R5, R6 and R9, R10, then clear the
division (R11, R12) and finish with R14.

**R8 · `set z := e`** changes the **context and the goal**: it adds the local definition `z := e` and replaces
every `e` in the goal by `z`. Terms that appear later (from a `rw`) are printed with `e` again, but `z` and `e`
are the same term for `linarith`/`nlinarith`/`exact`. Placeholders: `(g : ℝ → ℝ) (n : ℕ) (y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (g^[n] y + 1)` | `z : ℝ := g^[n] y ⊢ P (z + 1)` |

**R9 · `abs_sub_le`** **closes** a triangle inequality. The lemma is
`abs_sub_le a b c : |a - c| ≤ |a - b| + |b - c|`, the triangle inequality through `b`. Placeholders:
`(a b c : ℝ)`. As a `calc` step: `_ ≤ |x - f x| + |f x - p| := abs_sub_le _ _ _`; as a fact:
`have t := abs_sub_le a b c` adds it to the **context**. Before (closed by `exact abs_sub_le a b c`):

```lean-goal
⊢ |a - c| ≤ |a - b| + |b - c|
```

**R10 · `rw [abs_sub_comm a]`** changes the **goal**. The lemma is `abs_sub_comm a b : |a - b| = |b - a|`.
Giving `a` makes `rw` turn only `|a - _|` around. Placeholders: `(a b : ℝ)`. Before, then after:

```lean-goal
⊢ P |a - b|
⊢ P |b - a|
```

**R11 · `rw [div_mul_eq_mul_div]`** changes the **goal**. The lemma is `a / b * c = a * c / b`. Placeholders:
`{α : Type} [DivisionCommMonoid α] (a b c : α)` (commutative `*` with `⁻¹`, `/`; `ℝ` qualifies). It brings
`K / (1 - K) * d` into the form `b / c` that R12 needs.

| Before | After |
|---|---|
| `⊢ P (a / b * c)` | `⊢ P (a * c / b)` |

**R12 · `rw [le_div_iff₀]`** changes the **goal list**. The lemma is `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔
a * c ≤ b`: it clears a positive denominator. Without an argument it adds the side goal `0 < c`; write
`rw [le_div_iff₀ (by linarith)]` to close it on the spot. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b`, `⊢ 0 < c` |

**R13 · `linarith`** **closes** a goal `t ≤ s`, `t < s`, `t = s` (or `False`) that follows from the
hypotheses by adding them up with nonnegative constant coefficients. Products of unknowns count as opaque
atoms. Placeholders: `(k : ℝ)`.

| Before | After |
|---|---|
| `hk : k < 1 ⊢ 0 < 1 - k` | closed |

**R14 · `nlinarith`** **closes** goals that need products of hypotheses: it multiplies pairs of hypotheses
(and the negated goal) and then runs `linarith`. Here `0 ≤ k` times `u ≤ v` gives `k * u ≤ k * v`.
Placeholders: `(k u v : ℝ)`. In the exercise it needs `hK0 : 0 ≤ K` times the triangle fact. If it fails,
pass the product by hand: `nlinarith [mul_le_mul_of_nonneg_left h2 hK0]`, where
`mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c` (a term in `[…]` is an extra hypothesis for
`linarith`/`nlinarith`).

| Before | After |
|---|---|
| `hk : 0 ≤ k, huv : u ≤ v ⊢ k * u ≤ k * v` | closed |

---

## Part 3 · `iterate_tendsto`

Statement: `Tendsto (fun n => f^[n] x₀) atTop (𝓝 p)`, i.e. `xₙ → p`. Build
`h0 : Kⁿ · |x₀ - p| → 0` (R15, R16, R17), restate the goal as `‖xₙ - p‖ → 0` (R18), squeeze it between `0`
and `Kⁿ · |x₀ - p|` (R19, R20), and the remaining bound is Part 1 after R21.

**R15 · `tendsto_pow_atTop_nhds_zero_of_lt_one`** changes the **context** (with `have`). The lemma is
`0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`. Placeholders: `(r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1)`.

| Before | After `have t := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` |
|---|---|
| `⊢ G` | `t : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R16 · `Filter.Tendsto.mul_const`** changes the **context**. The lemma is
`Tendsto u l (𝓝 a) → Tendsto (fun n => u n * b) l (𝓝 (a * b))`, written with dot notation `hu.mul_const b`.
Placeholders: `(u : ℕ → ℝ) (a b : ℝ)`.

| Before | After `have t := hu.mul_const b` |
|---|---|
| `hu : Tendsto u atTop (𝓝 a) ⊢ G` | `t : Tendsto (fun x => u x * b) atTop (𝓝 (a * b)) ⊢ G` |

**R17 · `simpa using t`** **closes** the goal: it simplifies `t` and the goal with the same `simp` set and then
matches them. Here `0 * b` simplifies to `0`. Placeholders: `(u : ℕ → ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `t : Tendsto (fun n => u n * b) atTop (𝓝 (0 * b)) ⊢ Tendsto (fun n => u n * b) atTop (𝓝 0)` | closed |

**R18 · `rw [tendsto_iff_norm_sub_tendsto_zero]`** changes the **goal**. The lemma is
`Tendsto u l (𝓝 L) ↔ Tendsto (fun n => ‖u n - L‖) l (𝓝 0)`: convergence to `L` is convergence of the
distance to 0. The bound variable may be printed as `e`. Placeholders: `(u : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto u atTop (𝓝 L)` | `⊢ Tendsto (fun e => ‖u e - L‖) atTop (𝓝 0)` |

**R19 · `refine squeeze_zero (fun t => …) (fun t => ?_) hu`** changes the **goal**. The lemma is
`squeeze_zero : (∀ t, 0 ≤ g t) → (∀ t, g t ≤ u t) → Tendsto u l (𝓝 0) → Tendsto g l (𝓝 0)`. The first
argument proves `0 ≤ g t` (R20 in the exercise), `fun t => ?_` leaves the bound `g t ≤ u t` open for one
`t`, the third is the limit of the upper sequence. Placeholders: `(g u : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto g atTop (𝓝 0)` | `t : ℕ ⊢ g t ≤ u t` |

**R20 · `norm_nonneg`** **closes** `0 ≤ ‖a‖`. The lemma is `norm_nonneg a : 0 ≤ ‖a‖`; in the exercise it is
the first argument of R19: `fun n => norm_nonneg _`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ‖a‖` | closed |

**R21 · `rw [Real.norm_eq_abs]`** changes the **goal**. The lemma is `‖r‖ = |r|` for `r : ℝ`. After it, the
remaining bound `|f^[n] x₀ - p| ≤ K ^ n * |x₀ - p|` is exactly Part 1: `exact iterate_error f K hK0 hf p hp x₀ n`
(an earlier theorem is used like a hypothesis, with all its arguments). Placeholders: `(r : ℝ)`.

Before, then after:

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

**W3: squeezing `(1/2)ⁿ / (n + 1)`.** R15 for `r = 1/2`, then R19 with `positivity` (proves `0 ≤ e` for `e` built from
positive pieces) for `0 ≤ …` leaves

```lean-goal
⊢ (1 / 2) ^ n / (↑n + 1) ≤ (1 / 2) ^ n
```

which `div_le_self : 0 ≤ a → 1 ≤ b → a / b ≤ a` closes (`1 ≤ ↑n + 1` by `linarith`).

**W4: a constant factor.** For `(1/3)ⁿ * c → 0`: R15, R16 give `t2 : … → 0 * c`, and R17 closes

```lean-goal
⊢ Tendsto (fun n => (1 / 3) ^ n * c) atTop (𝓝 0)
```

---

## Traps

- `Function.iterate_succ_apply'` (primed) gives `f (f^[n] x)`; the unprimed `Function.iterate_succ_apply`
  gives `f^[n] (f x)`, where `hf` does not help. Use the primed one.
- `rw [hp]` rewrites `f p` to `p`, not the other way. To put `f p` into a goal, state the step in a `calc`
  whose goal contains `f p` (W1) and close it with `rw [hp]`.
- `set x := f^[n] x₀` only abbreviates what is in the goal at that moment. After `rw [Function.iterate_succ_apply']`
  the goal shows `f (f^[n] x₀)` again, while your `have`s say `f x`. This is fine for `nlinarith` and `exact`,
  which see that `x` is `f^[n] x₀`, but `rw [h1]` would not find `f x` literally.
- `rw [abs_sub_comm]` with no argument flips the first `|_ - _|` it meets; give the first argument
  (`abs_sub_comm x`) to pick the one you want.
- `linarith` cannot multiply two hypotheses: the a posteriori step needs `K * (triangle inequality)`, hence
  `nlinarith` (or hand it the product, R14).
- `le_div_iff₀` needs the denominator positive: `0 < 1 - K` comes from `hK : K < 1` by `linarith`, not from
  `hK0`.
- In `squeeze_zero` the order is: nonnegativity, the bound, the limit of the upper sequence.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on the iteration count | `induction n with \| zero => … \| succ n ih => …` | R1 |
| `f^[0] x → x`, `c ^ 0 * a → a` | `simp` (or `rw [Function.iterate_zero_apply, pow_zero, one_mul]`) | R2, R3 |
| `f^[n + 1] x → f (f^[n] x)` | `rw [Function.iterate_succ_apply']` | R4 |
| chain `=` and `≤` steps | `calc a = b := … _ ≤ c := …` | R5 |
| use the Lipschitz hypothesis | `hf _ _` | R6 |
| `c * a ≤ c * b` from `a ≤ b`, `0 ≤ c` | `gcongr` | R7 |
| name a subterm | `set x := f^[n] x₀` | R8 |
| triangle inequality | `abs_sub_le a b c` | R9 |
| flip `\|a - b\|` | `rw [abs_sub_comm a]` | R10 |
| `a / b * c → a * c / b` | `rw [div_mul_eq_mul_div]` | R11 |
| clear a positive denominator | `rw [le_div_iff₀ (by linarith)]` | R12 |
| linear arithmetic | `linarith` | R13 |
| needs a product of hypotheses | `nlinarith` | R14 |
| `rⁿ → 0` for `0 ≤ r < 1` | `tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` | R15 |
| multiply a limit by a constant | `h.mul_const c` | R16 |
| clean `0 * c` and close | `simpa using h` | R17 |
| `uₙ → L` as `‖uₙ - L‖ → 0` | `rw [tendsto_iff_norm_sub_tendsto_zero]` | R18 |
| squeeze to 0 | `refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0` | R19, R20 |
| `‖r‖ → \|r\|` on `ℝ` | `rw [Real.norm_eq_abs]` | R21 |
| reuse Part 1 | `exact iterate_error f K hK0 hf p hp x₀ n` | |
| see the state | infoview | |
