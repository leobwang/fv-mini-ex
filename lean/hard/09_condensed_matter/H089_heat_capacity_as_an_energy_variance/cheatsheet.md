# H089 · Heat capacity as an energy variance: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`, `ring`,
`norm_num`, anonymous functions `fun x => …`. **New here:** Mathlib's one-variable calculus (`HasDerivAt`,
`deriv`, `Differentiable`, `Antitone`), finite sums `∑`, `field_simp`, `generalize`, and physlib's
`CanonicalEnsemble` with its β-parameterised partition function, probabilities and mean energy.

**The physics, in symbols.** Units `k_B = 1`. A finite system has microstates `i ∈ ι` with energies
`E i`. At inverse temperature `b = 1/T`:
$Z(b) = \sum_i e^{-b E_i}$ (partition function), $p_b(i) = e^{-b E_i}/Z(b)$ (Boltzmann probability),
$U(b) = \sum_i E_i\, p_b(i)$ (mean energy), $\mathrm{Var}_b(E) = \sum_i p_b(i)(E_i - U(b))^2$.
Write $N(b) = \sum_i E_i e^{-b E_i}$ and $S_2(b) = \sum_i E_i^2 e^{-b E_i}$, so $U = N/Z$,
$Z' = -N$, $N' = -S_2$, and $\mathrm{Var} = S_2/Z - U^2$. The quotient rule gives
$U' = (N'Z - NZ')/Z^2 = -S_2/Z + N^2/Z^2 = -\mathrm{Var}_b(E) \le 0$. Since $dT/db = -1/b^2$, the heat
capacity $C = dU/dT = b^2\,\mathrm{Var}_b(E) \ge 0$.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Derivative lemmas are used in **term mode**: from `hf : HasDerivAt f f' x` you build a new fact such as
  `hf.neg`. The guide shows them as `have h := hf.neg`, so the context gains `h` and you see its type.
  `hf.neg` is dot notation for `HasDerivAt.neg hf`.
- Placeholders are real-valued (`ℝ`) here, as in the exercise. The sum lemmas hold in any commutative
  additive monoid or group; the `HasDerivAt` lemmas over any *nontrivially normed field* `𝕜` (ℝ or ℂ).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `𝓒 : CanonicalEnsemble ι` | a physlib system with microstates of type `ι`; `𝓒.energy : ι → ℝ` is the energy `E` |
| `[Fintype ι]`, `[Nonempty ι]` | finitely many microstates; at least one (needed for `Z > 0`). `[MeasurableSpace ι]` is required by the structure and plays no role here |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, rexp (-b * 𝓒.energy i)` (R1) |
| `𝓒.probabilityBetaReal b i` | `p_b(i) = rexp (-b * 𝓒.energy i) / Z(b)` (R12) |
| `𝓒.meanEnergyBetaReal b` | `U(b) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i` (R12) |
| `inst✝ : Fintype ι`, `inst✝¹ : …` | unnamed type-class assumptions from the statement's `[…]` brackets; you never refer to them by name |
| `rexp x` | `Real.exp x`, the real exponential |
| `-b * 𝓒.energy i` | `(-b) * E i`: unary minus binds tighter than `*`. After `simp` it prints as `-(b * 𝓒.energy i)` |
| `fun b => …` inside a goal about `b` | the bound variable reuses the name `b`; it is a different variable from the point `b` |
| `∑ i, f i` | the sum of `f i` over all `i : ι` (`Finset.univ`, the finite set of all elements) |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι`; lemma statements use this form, with `s = Finset.univ` here |
| `∑ x, …` | the same sum; after `rw`/`simp` Lean often renames the bound variable to `x` |
| `HasDerivAt f f' x` | `f : ℝ → ℝ` is differentiable at `x` with derivative the number `f'`. A proposition, not a function |
| `deriv f x` | the derivative of `f` at `x` as a number (`0` when `f` is not differentiable there) |
| `DifferentiableAt ℝ f x`, `Differentiable ℝ f` | differentiable at `x`; differentiable at every `x` |
| `Antitone f` | `∀ a b, a ≤ b → f b ≤ f a` (non-increasing) |
| `-f`, `c / d` (functions) | pointwise: `(-f) x = -f x`, `(c / d) x = c x / d x` |
| `(-fun x => x) b` | the negated identity function applied to `b`, i.e. `-b`; `simp` rewrites it (R9) |
| `fun b => …` applied: `(fun x => body) b` | not yet substituted; `beta_reduce` does it (R25) |
| `a✝ : i ∈ Finset.univ`, `x✝ : …` | the unnamed hypothesis from `intro i _` (or `fun i _ => …`); it is always true here |
| `case hf`, `case hf'` | the two goals left by `apply antitone_of_deriv_nonpos` (R26) |

---

## Part 1 · `hasDerivAt_Z` (milestone)

Statement: `HasDerivAt Z (-∑ i, E i * rexp (-b * E i)) b`, i.e. $Z'(b) = -N(b)$. Unfold `Z` into a sum,
move the minus sign into the sum, differentiate term by term, and build each term's derivative from the
identity function.

**R1 · `unfold mathematicalPartitionFunctionBetaReal`** changes the **goal**: the name `Z` (a function
`ℝ → ℝ`) becomes its defining `fun`. Placeholders: `(𝓒 : CanonicalEnsemble ι)`, `P : (ℝ → ℝ) → Prop`.

| Before | After |
|---|---|
| `⊢ P 𝓒.mathematicalPartitionFunctionBetaReal` | `⊢ P fun b => ∑ i, rexp (-b * 𝓒.energy i)` |

**R2 · `rw [← Finset.sum_neg_distrib]`** changes the **goal**. The lemma is
`Finset.sum_neg_distrib : ∑ i ∈ s, -f i = -∑ i ∈ s, f i`; right to left it pushes `-` inside the sum, so
the sum's derivative can be taken term by term. Placeholders: `(f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (-∑ i, f i)` | `⊢ P (∑ x, -f x)` |

**R3 · `apply HasDerivAt.fun_sum`** changes the **goal**: the derivative of a sum is the sum of
derivatives. The lemma is `(∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x`.
Lean matches `A i` to the summand as a function of `y`, and `A' i` to the summand of the derivative.
Placeholders: `(A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ)`. Follow it with `intro i _`.

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x` | `⊢ ∀ i ∈ Finset.univ, HasDerivAt (A i) (A' i) x` |

**R4 · `hasDerivAt_id' x`** changes the **context**: it is the fact `HasDerivAt (fun x => x) 1 x`, the start
of every derivative chain. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun y => y) 1 x` | `h : HasDerivAt (fun x => x) 1 x ⊢ HasDerivAt (fun y => y) 1 x` |

**R5 · `hf.neg`** (`HasDerivAt.neg`) changes the **context**: `HasDerivAt f f' x → HasDerivAt (-f) (-f') x`.
The new function is the *negated function* `-f`, which prints as `(-fun x => x)` when `f` is the identity.
Placeholders: `(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ HasDerivAt (-f) (-f') x` | `h : HasDerivAt (-f) (-f') x ⊢ HasDerivAt (-f) (-f') x` |

**R6 · `hc.mul_const d`** (`HasDerivAt.mul_const`) changes the **context**: multiply by a constant on the
right, `HasDerivAt c c' x → HasDerivAt (fun y => c y * d) (c' * d) x`. Placeholders:
`(c : ℝ → ℝ) (c' d x : ℝ)`.

| Before | After |
|---|---|
| `hc : HasDerivAt c c' x ⊢ HasDerivAt (fun y => c y * d) (c' * d) x` | `h : HasDerivAt (fun y => c y * d) (c' * d) x ⊢ HasDerivAt (fun y => c y * d) (c' * d) x` |

**R7 · `hf.exp`** (`HasDerivAt.exp`, the chain rule for `Real.exp`) changes the **context**:
`HasDerivAt f f' x → HasDerivAt (fun x => rexp (f x)) (rexp (f x) * f') x`. Placeholders:
`(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ HasDerivAt (fun y => rexp (f y)) (rexp (f x) * f') x` | `h : HasDerivAt (fun x => rexp (f x)) (rexp (f x) * f') x ⊢ HasDerivAt (fun y => rexp (f y)) (rexp (f x) * f') x` |

Chaining R4 → R5 → R6 → R7 on the term `rexp (-y * c)` produces the derivative
`rexp ((-fun x => x) b * c) * (-1 * c)`, which is right but not in the goal's form. R8 fixes that.

**R8 · `refine hf.congr_deriv ?_`** (`HasDerivAt.congr_deriv`) changes the **goal**:
`HasDerivAt f f' x → f' = g' → HasDerivAt f g' x`. You keep the function and the point, and trade the
goal for the algebra fact `f' = g'`. The function `f` must match the goal's up to unfolding (Lean checks
`fun y => rexp (-y * c)` against the chain's function by computation, so that part is free).
Placeholders: `(f : ℝ → ℝ) (f' g' x : ℝ)`. In term mode: `hf.congr_deriv (by simp; ring)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

**R9 · `simp`** on the derivative value changes the **goal**: it evaluates the pointwise operations the
chain left behind (`(-fun y => y) x` → `-x`, `-1 * c` → `-c`) and normalises signs (it may also cancel
a `-` on both sides of an equation). Usually `ring` is
then needed for the commutativity that `simp` does not do. Placeholders: `(x c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((-fun y => y) x * c)` | `⊢ P (-(x * c))` |

---

## Part 2 · `hasDerivAt_N` (milestone)

Statement: `HasDerivAt (fun x => ∑ i, E i * rexp (-x * E i)) (-∑ i, E i ^ 2 * rexp (-b * E i)) b`, i.e.
$N' = -S_2$. Same as Part 1 (R2, R3, `intro i _`, R4 → R5 → R6 → R7), with one more step: each term has
the constant factor `E i` in front.

**R10 · `hd.const_mul c`** (`HasDerivAt.const_mul`) changes the **context**: multiply by a constant on the
left, `HasDerivAt d d' x → HasDerivAt (fun y => c * d y) (c * d') x`. Note the argument order: the
constant comes first, `HasDerivAt.const_mul c hd`, or `hd.const_mul c`. Placeholders: `(d : ℝ → ℝ) (c d' x : ℝ)`.

| Before | After |
|---|---|
| `hd : HasDerivAt d d' x ⊢ HasDerivAt (fun y => c * d y) (c * d') x` | `h : HasDerivAt (fun y => c * d y) (c * d') x ⊢ HasDerivAt (fun y => c * d y) (c * d') x` |

Then R8 with `by simp; ring`: the leftover algebra is `E i * (exp … * (-1 * E i)) = -(E i ^ 2 * exp …)`.

---

## Part 3 · `meanEnergy_eq_div` (milestone)

Statement: `𝓒.meanEnergyBetaReal = fun x => N x / Z x`, an equation of **functions**. Go pointwise, unfold
`U` and `p`, and pull the common `/ Z x` out of the sum.

**R11 · `funext x`** changes the **goal and the context**: two functions are equal when they agree at
every point. Placeholders: `(f g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : ℝ ⊢ f x = g x` |

**R12 · `simp only [meanEnergyBetaReal, probabilityBetaReal]`** changes the **goal**: it unfolds `U` and
`p` into their definitions. Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.meanEnergyBetaReal t)` | `⊢ P (∑ x, 𝓒.energy x * (rexp (-t * 𝓒.energy x) / 𝓒.mathematicalPartitionFunctionBetaReal t))` |

**R13 · `Finset.sum_div`** changes the **goal**: `(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`. Left to right it
pushes a division into the sum; `← Finset.sum_div` pulls a common denominator out (Part 4).
Placeholders: `(f : ι → ℝ) (a : ℝ)`; holds in any division semiring.

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) / a)` | `⊢ P (∑ i, f i / a)` |

**R14 · `mul_div_assoc`** changes the **goal**: `a * b / c = a * (b / c)` (`*` and `/` group to the left,
so `a * b / c` is `(a * b) / c`). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * b / c)` | `⊢ P (a * (b / c))` |

After R11, one `simp only` with R12, R13, R14 brings both sides to the same sum, and `simp` closes the goal
by `rfl`.

---

## Part 4 · `variance_eq` (milestone)

Statement: `∑ i, p b i * (E i - U b) ^ 2 = S₂ b / Z b - U b ^ 2`. Expand the square **inside** the sum,
split the sum into three, pull the constants and the common `/ Z` out, fold `∑ exp = Z`, replace `U`
by `N / Z` (Part 3), and then do the algebra with `Z, N, S₂` as plain variables.

**R15 · `𝓒.mathematicalPartitionFunctionBetaReal_pos t`** changes the **context**: `[Nonempty ι] → 0 < Z t`
(a nonempty sum of positive exponentials). `field_simp` and the quotient rule need it. Placeholders:
`(𝓒 : CanonicalEnsemble ι) (t : ℝ)`, `G : Prop`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t ⊢ G` |

**R16 · `simp only [e]` with `e : ∀ a b, l a b = r a b`** changes the **goal**: it rewrites every instance of
the pattern `l`, also under the binder `i` of `∑ i, …`. `rw [e]` fails there, because the summand
mentions the bound `i`. Prove `e` first: `have e : ∀ a b : ℝ, … := by intro a b; ring`. Placeholders:
`(w : ι → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, w i * (c + 1))` | `⊢ P (∑ x, (w x * c + w x))` |

**R17 · `Finset.sum_add_distrib`** changes the **goal**: `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`.
Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R18 · `Finset.sum_sub_distrib`** changes the **goal**: `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i`.
Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i - g i))` | `⊢ P (∑ x, f x - ∑ x, g x)` |

**R19 · `rw [← Finset.mul_sum]`** changes the **goal**. The lemma is `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`;
right to left it pulls a constant factor out of the sum. The constant must be on the **left** of each
summand. Placeholders: `(f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R20 · `have hd : body = name := rfl`** changes the **context**: a definition holds by `rfl`, so you can
state it as an equation and give it to `simp only [hd]` to fold the sum `∑ i, rexp (-t * E i)` back into
`Z t`. Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ)`, `G : Prop`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `hd : ∑ i, rexp (-t * 𝓒.energy i) = 𝓒.mathematicalPartitionFunctionBetaReal t` added |

**R21 · `generalize e = z at *`** changes the **goal and the context**: every occurrence of the term `e`
becomes a fresh variable `z`, and hypotheses about `e` become hypotheses about `z`. Without `at *` only
the goal changes. It must match `e` exactly as printed. Placeholders: `(f : ℝ → ℝ) (t : ℝ)`.

| Before | After |
|---|---|
| `hpos : 0 < f t ⊢ P (f t)` | `z : ℝ, hpos : 0 < z ⊢ P z` |

**R22 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero
(it finds `hz : 0 < z` or `hz : z ≠ 0` in the context), leaving an equation without `/`. Finish with
`ring`. Placeholders: `(a b z : ℝ) (hz : 0 < z)`.

| Before | After |
|---|---|
| `hz : 0 < z ⊢ a / z = b` | `⊢ a = z * b` |

The expansion fact for R16 must be stated so that every summand comes out as `(…) / Z` or
`constant * (…)`, the shapes R13 (backwards) and R19 (backwards) can pull out of a sum:
`expand : ∀ (U Z w E : ℝ), w / Z * (E - U) ^ 2 = E ^ 2 * w / Z - 2 * U * (E * w) / Z + U ^ 2 * (w / Z)`
(proof `intro U Z w E; ring`). A grouping such as `2 * U * E * w / Z` leaves `(2 * U * E i) * w i`,
whose constant part depends on `i`, and the sums no longer match `N b`.

The order is R12 (unfold `p` only) → R16 → R17, R18 → R13 backwards, R19 backwards → R20, all in one
`simp only`, then `simp only [meanEnergy_eq_div 𝓒]`, then R21 three times (for `Z b` with `at *`, then the
two sums), then R22 and `ring`.

---

## Part 5 · `hasDerivAt_meanEnergy` (spec)

Statement: `HasDerivAt U (-∑ i, p b i * (E i - U b) ^ 2) b`, i.e. $U'(b) = -\mathrm{Var}_b(E)$.
Prove Parts 1–4 first. Rewrite the goal with Part 4 and Part 3, so it reads
`HasDerivAt (fun x => N x / Z x) (-(S₂/Z - ((fun x => N x / Z x) b) ^ 2)) b`. Apply the quotient rule to
Parts 2 and 1, fix the derivative's form with R8, and finish the algebra as in Part 4.

**R23 · `hc.div hd hx`** (`HasDerivAt.div`, the quotient rule) changes the **context**:
`HasDerivAt c c' x → HasDerivAt d d' x → d x ≠ 0 → HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x`.
The function is the pointwise quotient `c / d`, which matches `fun x => c x / d x`. Placeholders:
`(c d : ℝ → ℝ) (c' d' x : ℝ) (hx : d x ≠ 0)`.

| Before | After |
|---|---|
| `hx : d x ≠ 0 ⊢ HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x` | `h : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x ⊢ HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x` |

**R24 · `hz.ne'`** (`LT.lt.ne'`) changes the **context**: from `hz : 0 < z` it gives `z ≠ 0`, the third
argument of R23. (`hz.ne` would give `0 ≠ z`, the wrong way round.) Placeholders: `(z : ℝ)`.

| Before | After |
|---|---|
| `hz : 0 < z ⊢ z ≠ 0` | `h : z ≠ 0 ⊢ z ≠ 0` |

**R25 · `beta_reduce`** changes the **goal**: it substitutes the argument into an applied `fun`. After
rewriting with Part 3, `U b` has become `(fun x => N x / Z x) b`; `generalize` cannot see `N b / Z b`
until this step. Placeholders: `(f : ℝ → ℝ) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((fun x => f x + 1) t)` | `⊢ P (f t + 1)` |

After R8 the goal is `((-S₂) * Z - N * -N) / Z ^ 2 = -(S₂ / Z - (N / Z) ^ 2)` written out with the full
sums; R25, R21 (three times), R22 and `ring` close it.

---

## Part 6 · `meanEnergy_antitone` (spec)

Statement: `Antitone U`. A function with derivative `≤ 0` everywhere is non-increasing. Both side
conditions come from Part 5, and `-Var ≤ 0` because the variance is a sum of (probability × square).

**R26 · `apply antitone_of_deriv_nonpos`** changes the **goal list**: the lemma is
`Differentiable ℝ f → (∀ x, deriv f x ≤ 0) → Antitone f`, so you get two goals. Placeholders: `(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Antitone f` | `⊢ Differentiable ℝ f`, `⊢ ∀ (x : ℝ), deriv f x ≤ 0` |

**R27 · `intro x`** on `Differentiable ℝ f` changes the **goal and the context**: `Differentiable ℝ f` is by
definition `∀ x, DifferentiableAt ℝ f x`, so `intro` works. Placeholders: `(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Differentiable ℝ f` | `x : ℝ ⊢ DifferentiableAt ℝ f x` |

**R28 · `hf.differentiableAt`** (`HasDerivAt.differentiableAt`) changes the **context**: a function with a
derivative at `x` is differentiable at `x`. Placeholders: `(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ DifferentiableAt ℝ f x` | `h : DifferentiableAt ℝ f x ⊢ DifferentiableAt ℝ f x` |

**R29 · `rw [hf.deriv]`** (`HasDerivAt.deriv : HasDerivAt f f' x → deriv f x = f'`) changes the **goal**:
`deriv f x` becomes the explicit derivative. Placeholders: `(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (deriv f x)` | `⊢ P f'` |

**R30 · `rw [neg_nonpos]`** changes the **goal**: the lemma is the iff `-a ≤ 0 ↔ 0 ≤ a`, and `rw` can
rewrite with an iff. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ -a ≤ 0` | `⊢ 0 ≤ a` |

**R31 · `apply Finset.sum_nonneg`** changes the **goal**: `(∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i`. In term
mode: `Finset.sum_nonneg fun i _ => …`. Placeholders: `(f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ∑ i, f i` | `⊢ ∀ i ∈ Finset.univ, 0 ≤ f i` |

**R32 · `apply mul_nonneg`** changes the **goal list**: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. In term mode:
`mul_nonneg ?_ (…)` to leave the first factor open. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a * b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

**R33 · `sq_nonneg a`** **closes** `0 ≤ a ^ 2`. Use `sq_nonneg _` to let Lean find `a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a ^ 2` | closed |

**R34 · `apply div_pos`** changes the **goal list**: `0 < a → 0 < b → 0 < a / b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < a / b` | `⊢ 0 < a`, `⊢ 0 < b` |

**R35 · `Real.exp_pos x`** **closes** `0 < rexp x`. With `open Real` you can write `exp_pos _`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < rexp x` | closed |

**R36 · `hab.le`** (`LT.lt.le`) changes the **context**: from `hab : a < b` it gives `a ≤ b`. Placeholders:
`(a b : ℝ)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ a ≤ b` | `h : a ≤ b ⊢ a ≤ b` |

The last goal is `0 ≤ 𝓒.probabilityBetaReal b i`. `p b i` is by definition `rexp (…) / Z b`, so a proof of
`0 < rexp (…) / Z b` (R34 with R35 and R15), turned into `≤` by R36, is accepted by `exact` as it stands.

---

## Worked combinations (W1–W4, on functions that are not the exercise's)

**W1: a derivative chain, fixed up with R8.** `HasDerivAt (fun y => rexp (y * a)) (a * rexp (x * a)) x`
from R4 → R6 → R7 and R8; then `simp` (R9) and `ring`:

```lean-goal
⊢ HasDerivAt (fun y => rexp (y * a)) (a * rexp (x * a)) x
⊢ rexp (x * a) * (1 * a) = a * rexp (x * a)
⊢ rexp (x * a) * a = a * rexp (x * a)
```

**W2: a sum of such terms.** R3, then `intro i _`, then W1 for each term with `(by simp; ring)`:

```lean-goal
⊢ ∀ i ∈ Finset.univ, HasDerivAt (fun y => rexp (y * a i)) (a i * rexp (x * a i)) x
```

**W3: the quotient rule on `y ↦ y / exp y`.** R23 on R4 and R7 (with R24 for `exp x ≠ 0`), then R8
leaves the algebra; R21 names `rexp x`, and R22 closes it:

```lean-goal
⊢ (1 * rexp x - x * (rexp x * 1)) / rexp x ^ 2 = (1 - x) / rexp x
⊢ (1 * E - x * (E * 1)) / E ^ 2 = (1 - x) / E
```

**W4: antitone from one `HasDerivAt` fact.** With `hd : ∀ x, HasDerivAt (fun y => -y) (-1) x`, R26 splits;
the first goal is R27 then R28 on `hd x`, the second is `intro x`, R29 on `hd x`, `norm_num`:

```lean-goal
⊢ Differentiable ℝ fun y => -y
⊢ ∀ (x : ℝ), deriv (fun y => -y) x ≤ 0
```

---

## Traps

- physlib already proves `dU/db = -Var` and the differentiability of `U`, `N`, `Z` with `deriv`; those
  lemmas are on the `BANNED:` line, because the exercise is the `HasDerivAt` plumbing. `try?` is banned
  only because it runs for many minutes on this file.
- `field_simp` before `generalize` rewrites **inside** the sums (`exp`, products), and the two sides stop
  matching. Name `Z b`, `N b`, `S₂ b` with R21 first (`at *` for `Z b`, so `hZ : 0 < Z` follows it).
- `generalize` matches the term as printed. After rewriting with Part 3, `U b` is
  `(fun x => N x / Z x) b`; run R25 first.
- `rw` cannot rewrite under `∑ i, …` when the pattern mentions `i`; use `simp only [e]` (R16).
- `convert … using 1` instead of R8 can leave an instance-equality side goal here; prefer `congr_deriv`.
- `mathematicalPartitionFunctionBetaReal_pos` needs `[Nonempty ι]`; the first three milestones do not.
- `hz.ne'` (`z ≠ 0`) versus `hz.ne` (`0 ≠ z`): R23 wants `d x ≠ 0`.
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES, "Structure"). After R26 or R32, use `·` bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see `Z`, `p`, `U` as sums | `unfold mathematicalPartitionFunctionBetaReal`, `simp only [meanEnergyBetaReal, probabilityBetaReal]` | R1, R12 |
| `-∑ f` → `∑ -f` | `rw [← Finset.sum_neg_distrib]` | R2 |
| derivative of a sum | `apply HasDerivAt.fun_sum; intro i _` | R3 |
| `(fun x => x)' = 1` | `hasDerivAt_id' x` | R4 |
| build `(c * rexp (-y * a))'` | `((hasDerivAt_id' x).neg.mul_const a).exp.const_mul c` | R5, R6, R7, R10 |
| right function, derivative off by algebra | `hf.congr_deriv (by simp; ring)` | R8, R9 |
| equation of functions | `funext x` | R11 |
| `(∑ f) / a ↔ ∑ f / a`, `a * b / c = a * (b / c)` | `Finset.sum_div`, `mul_div_assoc` | R13, R14 |
| `0 < Z t` | `𝓒.mathematicalPartitionFunctionBetaReal_pos t` | R15 |
| rewrite under `∑` | `simp only [e]` with `e : ∀ …, l = r` | R16 |
| split / factor sums | `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `← Finset.mul_sum` | R17–R19 |
| fold a definition back | `have hd : body = name := rfl` | R20 |
| name a big term | `generalize e = z at *` | R21 |
| clear denominators | `field_simp` then `ring` | R22 |
| quotient rule | `hc.div hd hz.ne'` | R23, R24 |
| `(fun x => …) b` → body | `beta_reduce` | R25 |
| antitone from `deriv ≤ 0` | `apply antitone_of_deriv_nonpos` | R26 |
| differentiable from `HasDerivAt` | `intro x; exact (hf x).differentiableAt` | R27, R28 |
| `deriv f x` → `f'` | `rw [hf.deriv]` | R29 |
| `-a ≤ 0` → `0 ≤ a` | `rw [neg_nonpos]` | R30 |
| sum / product / square ≥ 0 | `Finset.sum_nonneg`, `mul_nonneg`, `sq_nonneg` | R31–R33 |
| `0 < exp / Z`, `<` → `≤` | `div_pos (exp_pos _) hZ`, `h.le` | R34–R36 |
| see the state | infoview | |
