# H098 · Mean-field Curie–Weiss transition: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `constructor` on `↔`, `obtain`, `rintro`, `have`,
`show`, `funext`). **New here:** Mathlib's real numbers `ℝ` as an ordered field, `Real.exp` and the
hyperbolic functions, intervals as sets, continuity, derivatives written with `HasDerivAt`, the
"positive derivative ⇒ strictly increasing" theorem, and the intermediate value theorem.

**The physics in one paragraph.** In mean-field theory each spin feels the average field of its `z`
neighbours, so the magnetisation per spin `m ∈ (-1, 1)` must satisfy the self-consistency equation
`m = tanh (a m)` with `a = βJz` (`β = 1/(k_B T)` inverse temperature, `J > 0` coupling). `m = 0` always
solves it; the theorem says a solution `m > 0` (spontaneous magnetisation) exists exactly when `a > 1`,
that is below the critical temperature `T_c = Jz / k_B`. The proof uses two bounds,
`y / (1 + y) ≤ tanh y < y` for `y > 0`, and the intermediate value theorem.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. All lemmas here are stated for general ordered fields or normed
  fields; every placeholder is `ℝ` (or `ℝ → ℝ`) in this problem, so the entries state them over `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`), an ordered field: `+ - * /`, `<`, `≤` behave as on paper except `x / 0 = 0` |
| `-2 * y`, `… * -2` | `(-2) * y` and `… * (-2)`: unary minus binds tighter than `*`, so `-2 * y` is not `-(2 * y)` (they are equal, but not syntactically) |
| `Real.exp x`, `Real.tanh x`, `Real.sinh x`, `Real.cosh x` | `eˣ`, `tanh x = sinh x / cosh x`, `sinh x = (eˣ - e⁻ˣ)/2`, `cosh x = (eˣ + e⁻ˣ)/2` (may print as `rexp x`) |
| `x⁻¹` | `1 / x`; on `ℝ`, `0⁻¹ = 0` by convention, so lemmas about `/` need `0 < c` or `c ≠ 0` |
| `Set.Icc a b`, `Set.Ici a`, `Set.Ioi a` | the intervals `[a, b]`, `[a, ∞)`, `(a, ∞)` as sets of reals |
| `x ∈ Set.Icc a b` | by definition `a ≤ x ∧ x ≤ b`; so `hx.1 : a ≤ x`, `hx.2 : x ≤ b`, and `⟨h1, h2⟩` proves it |
| `x ∈ Set.Ici a`, `x ∈ Set.Ioi a` | by definition `a ≤ x`, `a < x` (`Set.mem_Ici`, R26; `have : a < x := hx`, R10) |
| `s ⊆ t` | every element of `s` is in `t`; a proof of it is a function taking `h : y ∈ s` to `y ∈ t` (R42) |
| `∀ x ∈ s, P x` | `∀ x, x ∈ s → P x`: `intro x hx` gives `x` and `hx : x ∈ s` |
| `f '' s` | the image `{f x \| x ∈ s}`; `y ∈ f '' s` is by definition `∃ x, x ∈ s ∧ f x = y` (R43) |
| `interior s` | the interior points of `s`; `interior (Set.Ici a) = Set.Ioi a` (R10) |
| `Convex ℝ s` | `s` contains the segment between any two of its points (true for every interval) |
| `Continuous f`, `ContinuousOn f s` | `f` is continuous everywhere / `f` restricted to `s` is continuous |
| `HasDerivAt f f' x` | `f` is differentiable at `x` with derivative the number `f'` |
| `deriv f x` | the derivative of `f` at `x` as a number (junk value `0` if `f` is not differentiable there) |
| `StrictMonoOn f s` | `∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b → f a < f b`; `⦃⦄` binders are implicit, so `hmono ha hb hab : f a < f b` (R25) |
| `id` | the identity function, `id y = y` |
| `f * g`, `f - g` (functions) | the pointwise product / difference: `(f * g) y = f y * g y` by definition |
| `fun x => …` | a function; Lean may rename the bound variable (`fun y => c + f y` prints as `fun x => c + f x`) |
| `f : ℝ → ℝ := fun y => …`, `m₀ : ℝ := ⋯` | a local definition made by `let` (R7) or `set` (R35); the infoview may abbreviate the body as `⋯` (hover to see it) |
| `case hf`, `case hf'`, `case refine_1`, `case mp`, `case mpr` | the names of the goals created by `apply`, `refine`, `constructor` |

---

## Part 1 · `tanh_exp_form` (milestone)

Statement: `tanh y = (e^{2y} - 1) / (e^{2y} + 1)`. Multiply numerator and denominator of
`(eʸ - e⁻ʸ)/(eʸ + e⁻ʸ)` by `eʸ`. In Lean: unfold, express everything through `eʸ`, clear denominators.

**R1 · `rw [Real.tanh_eq]`** changes the **goal**. The lemma is
`Real.tanh_eq x : tanh x = (exp x - exp (-x)) / (exp x + exp (-x))`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.tanh x)` | `⊢ P ((Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)))` |

**R2 · `rw [show 3 * x = x + x + x by ring]`** changes the **goal**: `show T by tac` is a proof of `T` made
on the spot, and `rw` uses it like any equation. Use it to rewrite `2 * y` as `y + y` so that R3 applies.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (3 * x)` | `⊢ P (x + x + x)` |

**R3 · `rw [Real.exp_add]`** changes the **goal**. The lemma is `Real.exp_add x y : exp (x + y) = exp x * exp y`.
Right to left (`rw [← Real.exp_add]`) it merges a product of exponentials, as in `exp a * exp b = 1`
proofs. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp (x + y))` | `⊢ P (Real.exp x * Real.exp y)` |

**R4 · `rw [Real.exp_neg]`** changes the **goal**. The lemma is `Real.exp_neg x : exp (-x) = (exp x)⁻¹`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp (-x))` | `⊢ P (Real.exp x)⁻¹` |

**R5 · `have hx := Real.exp_pos x`** changes the **context**. The lemma is `Real.exp_pos x : 0 < exp x`.
`field_simp` (R6) needs it to know `exp x ≠ 0`; `nlinarith` (R24) needs it as a hint. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hx : 0 < Real.exp x ⊢ G` |

**R6 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (from
`≠ 0` or `0 <` hypotheses in the context, and numerals) and normalises. It often closes an identity of
fractions outright; if not, finish with `ring`. Placeholders: `(x y a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ x / a = y` | `ha : 0 < a ⊢ x = a * y` |

---

## Part 2 · `tanh_lt_self` (milestone)

Statement: `0 < y → tanh y < y`. With Part 1 and `e^{2y} + 1 > 0`, the goal is
`e^{2y} - 1 < y (e^{2y} + 1)`; dividing by `e^{2y}`, it is `1 - y < (1 + y) e^{-2y}`. Let
`f y = (1 + y) e^{-2y} - (1 - y)`. Then `f 0 = 0` and `f' y = 1 - (1 + 2y) e^{-2y} > 0` for `y > 0` because
`e^{2y} > 1 + 2y`. So `f` is strictly increasing on `[0, ∞)` and `f y > f 0 = 0`.

### Naming `f` and reducing monotonicity to the derivative

**R7 · `let f : ℝ → ℝ := fun y => …`** changes the **context**: it adds a local definition. Goals and
hypotheses can then mention `f`; Lean unfolds it when checking definitional equality, and
`simp only [f]` (R27) unfolds it on request.

| Before | After |
|---|---|
| `⊢ G` | `f : ℝ → ℝ := fun y => y ^ 2 + 1 ⊢ G` |

**R8 · `apply strictMonoOn_of_deriv_pos (convex_Ici c)`** changes the **goal list**. The lemma is
`strictMonoOn_of_deriv_pos : Convex ℝ D → ContinuousOn f D → (∀ x ∈ interior D, 0 < deriv f x) → StrictMonoOn f D`,
and `convex_Ici c : Convex ℝ (Set.Ici c)` fills the first argument. Two goals remain: continuity and a
positive derivative inside. Pass the first as `(by fun_prop)` (R9) to keep only the second.
Placeholders: `(f : ℝ → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ StrictMonoOn f (Set.Ici c)` | `⊢ ContinuousOn f (Set.Ici c)`, `⊢ ∀ x ∈ interior (Set.Ici c), 0 < deriv f x` |

**R9 · `fun_prop`** **closes** a `Continuous` or `ContinuousOn` goal for a function built from `+ - *`,
constants, `Real.exp`, `Real.sinh`, `Real.cosh` and powers. It also uses `Continuous g` hypotheses from the
context for functions it does not know (put `continuous_tanh` there with `have`). It sees through a `let`
name such as `f`. It does **not** know `Real.tanh` (Mathlib has no `Real.continuous_tanh`: Part 4).

| Before | After |
|---|---|
| `⊢ ContinuousOn (fun y => y * Real.exp (c * y) - 1) (Set.Ici c)` | no goals |
| `hg : Continuous g ⊢ Continuous fun y => g (c * y) - y` | no goals |

**R10 · `rw [interior_Ici] at hx`** changes the **context**. The lemma is `interior_Ici : interior (Set.Ici a) = Set.Ioi a`.
After it, `hx : x ∈ Set.Ioi c` *is* `c < x` by definition, so `have hx0 : c < x := hx` restates it
in a form `positivity` and `nlinarith` read. Placeholders: `(c x : ℝ)`.

| Before | After `rw [interior_Ici] at hx` | After `have hx0 : c < x := hx` |
|---|---|---|
| `hx : x ∈ interior (Set.Ici c) ⊢ G` | `hx : x ∈ Set.Ioi c ⊢ G` | `hx0 : c < x ⊢ G` |

### Building a derivative

The goal `0 < deriv f x` needs the value of `deriv f x`. Compute it as a `HasDerivAt` fact `hd` from the pieces
of `f`, then rewrite with `hd.deriv` (R20). Each rule below is a term: `have h := …` adds the fact.
Placeholders: `(f g : ℝ → ℝ) (f' g' c x : ℝ)`, with `hf : HasDerivAt f f' x`, `hg : HasDerivAt g g' x`.

**R11 · `hasDerivAt_id x`** changes the **context**: `HasDerivAt id 1 x`, the start of every chain.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt id 1 x ⊢ G` |

**R12 · `hf.const_add c`** changes the **context**: `(c + f)' = f'`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h : HasDerivAt (fun x => c + f x) f' x ⊢ G` |

**R13 · `hf.const_mul c`** changes the **context**: `(c · f)' = c · f'`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h : HasDerivAt (fun y => c * f y) (c * f') x ⊢ G` |

**R14 · `hf.exp`** changes the **context**: the chain rule for `exp`, `(e^{f})' = e^{f(x)} · f'`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x ⊢ G` |

**R15 · `hf.const_sub c`** changes the **context**: `(c - f)' = -f'`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h : HasDerivAt (fun x => c - f x) (-f') x ⊢ G` |

**R16 · `simpa using h`** **closes** the goal when `h` and the goal become the same after `simp` on both.
Chains from `hasDerivAt_id` contain `id y` and `* 1`; state the clean form you want and let `simpa` match:
`have h2 : HasDerivAt (fun y => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x := by simpa using …`.

| Before | After |
|---|---|
| `h : HasDerivAt (fun y => c * id y) (c * 1) x ⊢ HasDerivAt (fun y => c * y) c x` | no goals |

**R17 · `hf.mul hg`** changes the **context**: the product rule. The function is printed `f * g` (pointwise
product); `exact` accepts it for a goal written `fun y => f y * g y`, since the two are equal by definition.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (f * g) (f' * g x + f x * g') x ⊢ G` |

**R18 · `hf.sub hg`** changes the **context**: `(f - g)' = f' - g'`.

| Before | After |
|---|---|
| `⊢ G` | `h : HasDerivAt (f - g) (f' - g') x ⊢ G` |

**R19 · `apply hf.congr_deriv`** changes the **goal**. The lemma is
`HasDerivAt.congr_deriv : HasDerivAt f f' x → f' = g' → HasDerivAt f g' x`: R17/R18 produce the derivative in
an unsimplified shape; this restates it as the one you want, leaving an equation of numbers (usually
`ring`). As a term: `exact (….sub h3).congr_deriv (by ring)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

**R20 · `rw [hf.deriv]`** changes the **goal**. The lemma is `HasDerivAt.deriv : HasDerivAt f f' x → deriv f x = f'`.

| Before | After |
|---|---|
| `⊢ P (deriv f x)` | `⊢ P f'` |

### Inequalities with `exp`

**R21 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` by the shape of `e` (sums and
products of positive things, `exp`, squares, numerals), using hypotheses `0 < x` for the variables. Use it
for side goals: `Real.add_one_lt_exp (by positivity)`, `div_lt_iff₀ (by positivity)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ 0 < 2 * x * Real.exp x + x ^ 2` | no goals |
| `hx : 0 < x ⊢ 2 * x ≠ 0` | no goals |

**R22 · `Real.add_one_lt_exp`** changes the **context**. The lemma is `Real.add_one_lt_exp : x ≠ 0 → x + 1 < exp x`
(`x` implicit). In Part 2 take `x := 2 * x`: `have hlt : 2 * x + 1 < Real.exp (2 * x) := Real.add_one_lt_exp (by positivity)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ G` | `h : x + 1 < Real.exp x ⊢ G` |

**R23 · `Real.exp_zero`** changes the **goal**: `exp 0 = 1`. `simp` knows it, together with `t + -t = 0`, so
after `rw [← Real.exp_add]` (R3 backwards) a goal `exp (t + -t) = 1` closes with `simp`.

| Before | After |
|---|---|
| `⊢ P (Real.exp 0)` | `⊢ P 1` |
| `⊢ Real.exp (t + -t) = 1` | no goals (`simp`) |

**R24 · `nlinarith [p₁, p₂]`** **closes** a goal that follows by linear arithmetic from the hypotheses, the
hints `pᵢ`, and their pairwise products (the negated goal included). Use it when the argument multiplies two
inequalities, e.g. `e^{2x} · e^{-2x} = 1` with `e^{-2x} > 0` and `e^{2x} > 2x + 1`. Pass the positivity facts as
hints (`Real.exp_pos (-2 * x)`) and have the product identity in the context.

| Before | After |
|---|---|
| `hu : 0 ≤ u, huv : u ≤ v ⊢ u * u ≤ v * v` | no goals |
| `hy : 0 < y ⊢ y < y * (1 + Real.exp y)` | no goals (`nlinarith [Real.exp_pos y]`) |

### Using the monotonicity

**R25 · `have key := hmono ha hb hab`** changes the **context**: `StrictMonoOn f s` is a function, applied to
two memberships and `a < b`. Placeholders: `(f : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `hmono : StrictMonoOn f s ⊢ G` | `key : f a < f b ⊢ G` |

**R26 · `Set.mem_Ici.mpr`** changes the **context**. The lemma is `Set.mem_Ici : x ∈ Set.Ici c ↔ c ≤ x`, so
`.mpr` builds the membership. `le_rfl : c ≤ c` gives `c ∈ Set.Ici c`; `hy.le : 0 ≤ y` comes from `hy : 0 < y`.

| Before | After |
|---|---|
| `h : c ≤ x ⊢ G` | `hx : x ∈ Set.Ici c ⊢ G` |

**R27 · `simp only [f] at h`** changes the **context**: it replaces the `let` name `f` in `h` by its body and
beta-reduces. On the goal: `simp only [f]` (with extra lemmas, e.g. `simp only [g, mul_one]`).

| Before | After |
|---|---|
| `h : f a < f b ⊢ G` | `h : g a + 1 < g b + 1 ⊢ G` |

**R28 · `simp only [mul_zero, Real.exp_zero, add_zero, sub_zero, mul_one, sub_self] at h`** changes the
**context**: it evaluates a formula at `0` with `x * 0 = 0`, `exp 0 = 1`, `x + 0 = x`, `x - 0 = x`, `x * 1 = x`,
`x - x = 0`. In the exercise, list R27's `f` in the same `simp only` call.

| Before | After |
|---|---|
| `h : (2 + 0) * Real.exp (c * 0) - (2 - 0) < q ⊢ G` | `h : 0 < q ⊢ G` |

**R29 · `rw [div_lt_iff₀ hc]`** changes the **goal**. The lemma is `div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)`;
`rw` with an `↔` replaces one side by the other. Placeholders: `(a b c : ℝ) (hc : 0 < c)`. Write
`(by positivity)` for `hc`.

| Before | After |
|---|---|
| `⊢ b / c < a` | `⊢ b < a * c` |

---

## Part 3 · `le_tanh` (milestone)

Statement: `0 ≤ y → y / (1 + y) ≤ tanh y`. With Part 1 it is
`y (e^{2y} + 1) ≤ (e^{2y} - 1)(1 + y)`, which simplifies to `2y + 1 ≤ e^{2y}`, the bound R31 at `2y`.

**R30 · `rw [div_le_div_iff₀ hb hd]`** changes the **goal**. The lemma is
`div_le_div_iff₀ : 0 < b → 0 < d → (a / b ≤ c / d ↔ a * d ≤ c * b)` (cross-multiplication).
Placeholders: `(a b c d : ℝ)`. Both side conditions by `(by positivity)`.

| Before | After |
|---|---|
| `⊢ a / b ≤ c / d` | `⊢ a * d ≤ c * b` |

**R31 · `Real.add_one_le_exp x`** changes the **context** (or is passed to `nlinarith` as a hint). The lemma is
`Real.add_one_le_exp x : x + 1 ≤ exp x`, for every `x` (no side condition; the strict version is R22).

| Before | After |
|---|---|
| `⊢ G` | `h : x + 1 ≤ Real.exp x ⊢ G` |

---

## Part 4 · `continuous_tanh` (milestone)

Statement: `Continuous Real.tanh`. `fun_prop` does not know `tanh`, but it knows `sinh` and `cosh`, and
`Real.tanh_eq_sinh_div_cosh x : tanh x = sinh x / cosh x`. Replace the function, then use the quotient rule
for continuity with `cosh x > 0`.

**R32 · `rw [show g = (fun x => …) from funext hg]`** changes the **goal**: `funext hg` turns the pointwise
equation `hg : ∀ x, g x = …` into an equation of functions (E022), and `show … from …` states it so `rw` can use
it. Placeholders: `(g k : ℝ → ℝ) (P : (ℝ → ℝ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P g` | `⊢ P fun x => k x / 2` |

**R33 · `refine Continuous.div ?_ ?_ ?_`** changes the **goal list**. The lemma is
`Continuous.div : Continuous f → Continuous g → (∀ x, g x ≠ 0) → Continuous (f / g)`. Close the first two with
`fun_prop` (R9) and the third with R34. As a term: `exact Continuous.div (by fun_prop) (by fun_prop) fun x => …`.

| Before | After |
|---|---|
| `⊢ Continuous fun x => f x / g x` | `⊢ Continuous f`, `⊢ Continuous g`, `⊢ ∀ (x : ℝ), g x ≠ 0` |

**R34 · `(Real.cosh_pos x).ne'`** changes the **context**. `Real.cosh_pos x : 0 < cosh x`, and for
`h : a < b`, `h.ne' : b ≠ a`; so this is `cosh x ≠ 0`.

| Before | After |
|---|---|
| `⊢ G` | `h : Real.cosh x ≠ 0 ⊢ G` |

---

## Part 5 · `mean_field_transition`

Statement: for `0 < a`, `1 < a ↔ ∃ m, 0 < m ∧ tanh (a m) = m`. Split with `constructor` (E005).

- **(→)** Let `g m = tanh (a m) - m`. At `m₀ = (a - 1)/(2a) ∈ (0, 1]`, `a m₀ = (a - 1)/2 =: y₀` and
  Part 3 gives `tanh (a m₀) ≥ y₀/(1 + y₀) = (a - 1)/(a + 1) ≥ m₀`, so `g m₀ ≥ 0`. At `m = 1`,
  `g 1 = tanh a - 1 < 0`. `g` is continuous (Part 4), so it has a zero `m ∈ [m₀, 1]` (IVT), and `m ≥ m₀ > 0`.
- **(←)** If `a ≤ 1` and `m > 0` solves it, then `m = tanh (a m) < a m ≤ m` (Part 2 at `a m > 0`): contradiction.

**R35 · `set t₀ := e with ht₀`** changes the **context and the goal**: it adds the local definition `t₀ := e`
and the equation `ht₀ : t₀ = e`, and replaces `e` by `t₀` everywhere. `rw [ht₀]` unfolds it again when a lemma
needs the formula. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((a + 1) / 3)` | `t₀ : ℝ := (a + 1) / 3, ht₀ : t₀ = (a + 1) / 3 ⊢ P t₀` |

**R36 · `apply div_pos`** changes the **goal list**. The lemma is `div_pos : 0 < a → 0 < b → 0 < a / b`. As a
term: `div_pos (by linarith) (by linarith)`.

| Before | After |
|---|---|
| `⊢ 0 < a / b` | `⊢ 0 < a`, `⊢ 0 < b` |

**R37 · `linarith`** **closes** a goal that is a linear combination of hypotheses (`<`, `≤`, `=` over an
ordered field). Products of unknowns (`a * m₀`, `Real.tanh (a * m)`) count as single unknowns; for genuinely
nonlinear steps use `nlinarith` (R24). `linarith [Real.tanh_lt_one a]` adds a fact on the spot.

| Before | After |
|---|---|
| `h1 : 1 < a, h2 : b ≤ a - 1 ⊢ b < 2 * a` | no goals |

**R38 · `rw [div_le_one hb]`** changes the **goal**. The lemma is `div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b)`.
For `m₀ ≤ 1`: `rw [hm₀, div_le_one (by linarith)]`, then `linarith`.

| Before | After |
|---|---|
| `⊢ a / b ≤ 1` | `⊢ a ≤ b` |

**R39 · `rw [le_div_iff₀ hc]`** changes the **goal**. The lemma is `le_div_iff₀ : 0 < c → (a ≤ b / c ↔ a * c ≤ b)`.
It turns `m₀ ≤ a m₀ / (1 + a m₀)` into a product inequality for `nlinarith`.

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b` |

**R40 · `Real.tanh_lt_one x`** changes the **context**: `tanh x < 1`, the sign of `g 1`.

| Before | After |
|---|---|
| `⊢ G` | `h : Real.tanh x < 1 ⊢ G` |

**R41 · `apply Continuous.continuousOn`** changes the **goal**. The lemma is
`Continuous.continuousOn : Continuous f → ContinuousOn f s`: continuity everywhere implies continuity on `s`.
Then `fun_prop` (R9) with `continuous_tanh` in the context. As a term:
`(by fun_prop : Continuous g).continuousOn`.

| Before | After |
|---|---|
| `⊢ ContinuousOn f s` | `⊢ Continuous f` |

**R42 · `intermediate_value_Icc' hab hf ⟨h1, h2⟩`** changes the **context**. The lemma is
`intermediate_value_Icc' : a ≤ b → ContinuousOn f (Set.Icc a b) → Set.Icc (f b) (f a) ⊆ f '' Set.Icc a b`:
the IVT for a function that goes *down* from `f a` to `f b` (the unprimed `intermediate_value_Icc` is for going
up). A `⊆` is a function on memberships, so applying it to `⟨h1, h2⟩ : y ∈ Set.Icc (f b) (f a)` gives
`y ∈ f '' Set.Icc a b`. In the exercise `y = 0`, `h1 : g 1 ≤ 0`, `h2 : 0 ≤ g m₀`.
Placeholders: `(f : ℝ → ℝ) (a b y : ℝ)`.

| Before | After |
|---|---|
| `h1 : f b ≤ y, h2 : y ≤ f a ⊢ G` | `h : y ∈ f '' Set.Icc a b ⊢ G` |

**R43 · `obtain ⟨m, hm, hfm⟩ := h`** changes the **context**: image membership is an existential with a
conjunction, so `obtain` unpacks the point and its two facts. R42 and R43 combine as
`obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' …`.

| Before | After |
|---|---|
| `h : y ∈ f '' s ⊢ G` | `m : ℝ, hm : m ∈ s, hfm : f m = y ⊢ G` |

**R44 · `apply lt_of_lt_of_le h1`** changes the **goal**. The lemma is `lt_of_lt_of_le : a < b → b ≤ c → a < c`.
In the exercise, the term `lt_of_lt_of_le hm₀pos hm.1` gives `0 < m` from `0 < m₀` and `hm.1 : m₀ ≤ m`.

| Before | After |
|---|---|
| `h1 : a < b ⊢ a < c` | `⊢ b ≤ c` |

**R45 · `by_contra h`** changes the **goal and the context**: to prove `G`, assume `h : ¬G` and prove `False`.

| Before | After |
|---|---|
| `⊢ G` | `h : ¬G ⊢ False` |

**R46 · `push Not at h`** changes the **context**: it moves `¬` inward, turning `¬a < b` into `b ≤ a` (and
`¬∀` into `∃ ¬`, etc.). Older Mathlib spells it `push_neg at h`.

| Before | After |
|---|---|
| `h : ¬a < b ⊢ G` | `h : b ≤ a ⊢ G` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a derivative from pieces (R11–R19).** For `(2 + y) e^{3y} - y`, prove the pieces `2 + y` (R11, R12, R16)
and `e^{3y}` (R11, R13, R14, R16) with `simpa`, then
`exact ((h1.mul h2).sub (hasDerivAt_id x)).congr_deriv (by ring)` (R17, R18, R19). The goal stays

```lean-goal
⊢ HasDerivAt (fun y => (2 + y) * Real.exp (3 * y) - y) ((7 + 3 * x) * Real.exp (3 * x) - 1) x
```

**W2: strictly increasing from the derivative (R8, R9, R10, R20, R21).** For `y ↦ y + eʸ` on `[0, ∞)`:
R8 with `(by fun_prop)`, `intro x hx`, R10, `hd := (hasDerivAt_id x).add (Real.hasDerivAt_exp x)`, R20,
`positivity`. Two names not needed in the exercise: `hf.add hg : HasDerivAt (f + g) (f' + g') x` is the sum rule
(the `+` twin of R18), and `Real.hasDerivAt_exp x : HasDerivAt Real.exp (Real.exp x) x`.
The goals along the way:

```lean-goal
⊢ StrictMonoOn (fun y => y + Real.exp y) (Set.Ici 0)
⊢ ∀ x ∈ interior (Set.Ici 0), 0 < deriv (fun y => y + Real.exp y) x
⊢ 0 < deriv (fun y => y + Real.exp y) x
⊢ 0 < 1 + Real.exp x
```

**W3: IVT for a decreasing function (R41, R42, R43).** `2 - m²` on `[1, 2]` goes from `1` down to `-2`. State
the signs as `h1 : (fun m => 2 - m ^ 2) 2 ≤ 0` and `h2 : 0 ≤ (fun m => 2 - m ^ 2) 1`, apply R42, unpack with R43:

```lean-goal
⊢ ∃ m ∈ Set.Icc 1 2, 2 - m ^ 2 = 0
```

| Before | After |
|---|---|
| `hcont : ContinuousOn (fun m => 2 - m ^ 2) (Set.Icc 1 2) ⊢ ∃ m ∈ Set.Icc 1 2, 2 - m ^ 2 = 0` | `h : 0 ∈ (fun m => 2 - m ^ 2) '' Set.Icc 1 2 ⊢ ∃ m ∈ Set.Icc 1 2, 2 - m ^ 2 = 0` |

---

## Traps

- The milestones are proved in order and used later: `tanh_exp_form` in Parts 2 and 3, `tanh_lt_self` in
  (←), `le_tanh` and `continuous_tanh` in (→). Each later proof calls the earlier theorem by name.
- `fun_prop` cannot prove continuity of `Real.tanh` by itself: prove `continuous_tanh` and put it in the
  context with `have := continuous_tanh` before calling `fun_prop` on `g`.
- `intermediate_value_Icc` (unprimed) is the increasing version, `Set.Icc (f a) (f b) ⊆ …`. Here `g` goes
  down from `g m₀ ≥ 0` to `g 1 ≤ 0`, so use `intermediate_value_Icc'`.
- Divisions on `ℝ` need positivity side goals (`0⁻¹ = 0`): `div_lt_iff₀`, `div_le_div_iff₀`, `le_div_iff₀`,
  `div_le_one` all take `0 < c`. Discharge them with `(by positivity)` or `(by linarith)`.
- `linarith` does not multiply. `e^{2x} · e^{-2x} = 1` combined with `e^{2x} > 2x + 1` is nonlinear: give
  `nlinarith` the identity in the context and the positivity facts as hints.
- `rw [Real.exp_add]` needs `exp (y + y)` literally; `exp (2 * y)` must first become `exp (y + y)` (R2).
- After `let g := …` or `set m₀ := …`, `linarith` sees `g m₀` and `Real.tanh (a * m₀) - m₀` as different
  unknowns: unfold with `simp only [g]` (R27) first.
- `deriv f x` is a junk `0` where `f` is not differentiable; never compute it directly. Build `HasDerivAt`
  and rewrite with `.deriv` (R20).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| tanh as exponentials | `rw [Real.tanh_eq]` | R1 |
| `2 * y → y + y` | `rw [show 2 * y = y + y by ring]` | R2 |
| `exp (x + y)`, `exp (-x)` | `rw [Real.exp_add, Real.exp_neg]` | R3, R4 |
| `0 < exp x` | `Real.exp_pos x` | R5 |
| clear denominators in an equation | `field_simp` | R6 |
| name a function | `let f : ℝ → ℝ := fun y => …` | R7 |
| strictly increasing on `[c, ∞)` | `apply strictMonoOn_of_deriv_pos (convex_Ici c) (by fun_prop)` | R8, R9 |
| continuity of a formula | `fun_prop` | R9 |
| `x ∈ interior (Set.Ici c)` → `c < x` | `rw [interior_Ici] at hx`; `have : c < x := hx` | R10 |
| derivative pieces | `hasDerivAt_id x`, `.const_add`, `.const_mul`, `.exp`, `.const_sub` | R11–R15 |
| clean a derivative fact | `simpa using …` | R16 |
| combine and restate | `((h1.mul h2).sub h3).congr_deriv (by ring)` | R17–R19 |
| `deriv f x → f'` | `rw [hd.deriv]` | R20 |
| `0 < e`, `e ≠ 0` side goals | `positivity` | R21 |
| `x + 1 < exp x` / `x + 1 ≤ exp x` | `Real.add_one_lt_exp (by positivity)` / `Real.add_one_le_exp x` | R22, R31 |
| `exp a * exp (-a) = 1` | `rw [← Real.exp_add]; simp` | R3, R23 |
| nonlinear inequality | `nlinarith [hints]` | R24 |
| use strict monotonicity | `hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy` | R25, R26 |
| unfold a `let` / evaluate at 0 | `simp only [f, mul_zero, Real.exp_zero, …] at h` | R27, R28 |
| `b / c < a`, `a / b ≤ c / d`, `a ≤ b / c`, `a / b ≤ 1` | `div_lt_iff₀`, `div_le_div_iff₀`, `le_div_iff₀`, `div_le_one` | R29, R30, R39, R38 |
| tanh via sinh / cosh | `rw [show Real.tanh = … from funext Real.tanh_eq_sinh_div_cosh]` | R32 |
| continuity of a quotient | `Continuous.div (by fun_prop) (by fun_prop) fun x => (Real.cosh_pos x).ne'` | R33, R34 |
| abbreviate a value | `set m₀ := … with hm₀` | R35 |
| `0 < a / b` | `div_pos (by linarith) (by linarith)` | R36 |
| linear arithmetic | `linarith` | R37 |
| `tanh x < 1` | `Real.tanh_lt_one x` | R40 |
| `ContinuousOn` from `Continuous` | `(by fun_prop : Continuous g).continuousOn` | R41 |
| IVT, decreasing | `obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hle hcont ⟨h1, h2⟩` | R42, R43 |
| `a < b ≤ c` | `lt_of_lt_of_le h hm.1` | R44 |
| proof by contradiction | `by_contra h; push Not at h` | R45, R46 |
| see the state | infoview | |
