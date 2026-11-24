# H113 · Back in the initial state exactly after whole periods: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rw`, `rw … at h`, `simp`, `have`,
`constructor`, `refine`, `ring`, anonymous functions `fun x => …`. **New here:** Mathlib's real inner
products `⟪·,·⟫_ℝ`, `EuclideanSpace`, scalar multiplication `•`, `Real.cos`/`Real.sin`/`π`, integer
casts `↑n`, and the tactics `rcases`, `rintro`, `obtain`, `nlinarith`, `linarith`, `field_simp`,
`push_cast`, `linear_combination`; physlib's `HarmonicOscillator`, `InitialConditions`, its
`trajectory`, `Time` and the time derivative `∂ₜ`.

**The physics, in symbols.** A harmonic oscillator `S` has mass `m > 0`, spring constant `k > 0` and
angular frequency $\omega = \sqrt{k/m} > 0$ (`S.ω`). Initial conditions are the position $x_0$ and
velocity $v_0$ at time 0 (vectors of $\mathbb{R}^1$). Physlib's solution and its velocity are
$$x(t) = \cos(\omega t)\,x_0 + \tfrac{\sin(\omega t)}{\omega}\,v_0,\qquad
  \dot x(t) = -\omega\sin(\omega t)\,x_0 + \cos(\omega t)\,v_0 .$$
Write $c = \cos(\omega t)$, $s = \sin(\omega t)$, $x\!x = \langle x_0, x_0\rangle$, $v\!v = \langle v_0, v_0\rangle$,
$x\!v = \langle x_0, v_0\rangle$ (inner products; in $\mathbb{R}^1$ these are just products).
- (→) If $x(t) = x_0$ and $\dot x(t) = v_0$, take the inner product of the first with $x_0$ and of the
  second with $v_0$: $c\,x\!x + \tfrac{s}{\omega} x\!v = x\!x$ and $-\omega s\,x\!v + c\,v\!v = v\!v$.
  Multiply the first by $\omega^2$ and add: the $s\,x\!v$ terms cancel and
  $(v\!v + \omega^2 x\!x)(c - 1) = 0$. A non-trivial state has $v\!v + \omega^2 x\!x > 0$ (Part 1), so $c = 1$
  (Part 2), i.e. $\omega t = 2\pi n$ for some $n \in \mathbb{Z}$, i.e. $t = n \cdot 2\pi/\omega$.
- (←) If $t = n \cdot 2\pi/\omega$ then $\omega t = 2n\pi$, so $c = 1$, $s = 0$ and both formulas give back
  $x_0$, $v_0$ (Part 3).

The milestones are exactly these steps: Part 1 (positivity), Part 2 (→ up to `cos = 1`), Part 3 (←),
Part 4 assembles the `↔`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
  "closed" means no goal is left.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal or hypothesis.
- Placeholders are written as Lean binders. `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]`
  means "`E` is a real vector space with a norm and an inner product `⟪·,·⟫_ℝ`";
  `EuclideanSpace ℝ (Fin 1)` (where `IC.x₀`, `IC.v₀` live) and `ℝ` itself qualify.
- Fact-building entries are shown as `have h := …`, so the context gains `h` and you see its type.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `S : HarmonicOscillator` | a structure with fields `S.m`, `S.k : ℝ` and proofs `S.m_pos : 0 < S.m`, `S.k_pos : 0 < S.k` |
| `S.ω` | the angular frequency `√(S.k / S.m)`; facts `S.ω_pos : 0 < S.ω` (R2), `S.ω_ne_zero : S.ω ≠ 0` (R14) |
| `IC : InitialConditions` | a structure with `IC.x₀ IC.v₀ : EuclideanSpace ℝ (Fin 1)`: initial position and velocity |
| `EuclideanSpace ℝ (Fin 1)` | $\mathbb{R}^1$ with its dot product; a vector type, so `cos θ • IC.x₀` is scalar times vector |
| `t : Time` | a time; a structure wrapping one real number `t.val : ℝ` |
| `InitialConditions.trajectory S IC t` | how Lean prints `IC.trajectory S t`: the position $x(t)$ (R7) |
| `∂ₜ (InitialConditions.trajectory S IC) t` | the time derivative of the trajectory at `t`: the velocity $\dot x(t)$ (R8) |
| `r • v` | the real number `r` times the vector `v` |
| `-S.ω • sin θ • IC.x₀` | `(-S.ω) • (sin θ • IC.x₀)`: `•` groups to the right |
| `⟪x, y⟫_ℝ` | the real inner product of `x` and `y` (for $\mathbb{R}^1$: the product $x y$) |
| `cos`, `sin`, `π` | `Real.cos`, `Real.sin`, `Real.pi` (the file has `open Real`) |
| `↑n` | the integer `n : ℤ` cast into `ℝ` (`Int.cast`); `↑(2 * n)` is the cast of the integer `2 * n` |
| `∃ n, ↑n * (2 * π) = x` | there is an integer `n` with $2\pi n = x$; `n`'s type `ℤ` is not printed |
| `n_1` | Lean's rename of a bound `n` that would clash with an `n` already in the context |
| `(fun t => body) t` | a function applied to `t`, not yet simplified; R10 turns it into `body` |
| `case mp`, `case mpr` | the `→` and `←` directions of an `↔` after `constructor` (R27) |
| `case inl`, `case inr` | the left and right side of an `∨` after `rcases` (R4) |

---

## Part 1 · `det_pos` (milestone)

Statement: if `IC.x₀ ≠ 0 ∨ IC.v₀ ≠ 0` then `0 < ⟪IC.v₀, IC.v₀⟫_ℝ + S.ω ^ 2 * ⟪IC.x₀, IC.x₀⟫_ℝ`.
Both inner products are `≥ 0`, `S.ω ^ 2 > 0`, and the nonzero vector has a strictly positive one.

**R1 · `real_inner_self_nonneg`** changes the **context**. Lemma: `0 ≤ ⟪x, x⟫_ℝ`. `x` is implicit, so
write the type: `have hx : 0 ≤ ⟪IC.x₀, IC.x₀⟫_ℝ := real_inner_self_nonneg`.
Placeholders: `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E)`.

| Before | After `have h : 0 ≤ ⟪x, x⟫_ℝ := real_inner_self_nonneg` |
|---|---|
| `⊢ 0 ≤ ⟪x, x⟫_ℝ` | context gains `h : 0 ≤ ⟪x, x⟫_ℝ`; `⊢ 0 ≤ ⟪x, x⟫_ℝ` |

**R2 · `HarmonicOscillator.ω_pos`** changes the **context**. Lemma: `0 < S.ω` (dot notation `S.ω_pos`).
Placeholders: `(S : HarmonicOscillator)`.

| Before | After `have h := S.ω_pos` |
|---|---|
| `⊢ 0 < S.ω` | `h : 0 < S.ω ⊢ 0 < S.ω` |

**R3 · `pow_pos`** changes the **context**. Lemma: `pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n`. With R2:
`pow_pos S.ω_pos 2 : 0 < S.ω ^ 2`. Placeholders: `(a : ℝ) (ha : 0 < a) (n : ℕ)` (any ordered semiring).

| Before | After `have h := pow_pos ha n` |
|---|---|
| `ha : 0 < a ⊢ 0 < a ^ n` | `h : 0 < a ^ n ⊢ 0 < a ^ n` |

**R4 · `rcases hab with h | h`** changes the **goal list and the context**: one goal per side of the
`∨`, each with `h` the proof of that side; `hab` is gone. Placeholders: `(A B G : Prop) (hab : A ∨ B)`.
Work on the two goals with `·` (TACTIC_STATES, "Structure").

| Before | After |
|---|---|
| `hab : A ∨ B ⊢ G` | `h : A ⊢ G` (case `inl`), `h : B ⊢ G` (case `inr`) |

**R5 · `real_inner_self_pos`** changes the **context**. Lemma: `0 < ⟪x, x⟫_ℝ ↔ x ≠ 0`; `.mpr` reads
it right to left. Placeholders: `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) (hx : x ≠ 0)`.

| Before | After `have h := real_inner_self_pos.mpr hx` |
|---|---|
| `hx : x ≠ 0 ⊢ 0 < ⟪x, x⟫_ℝ` | context gains `h : 0 < ⟪x, x⟫_ℝ`; `⊢ 0 < ⟪x, x⟫_ℝ` |

**R6 · `nlinarith [p₁, p₂]`** **closes** a goal that is a polynomial (in)equality, from the
hypotheses in the context and the extra proofs `pᵢ` in brackets. Unlike `linarith` (R20) it also
multiplies pairs of these facts, so it can find `0 < b * c` from `0 < b`, `0 < c`; giving the product
yourself (as `mul_pos hb hc` here) makes it reliable. In the exercise, pass R5's fact
`0 < ⟪x, x⟫_ℝ` in the brackets; `nlinarith` multiplies it by `hω : 0 < S.ω ^ 2` itself. It treats
`⟪x, x⟫_ℝ` and `S.ω` as unknowns. Placeholders: `(a b c : ℝ)`.

| Before | After `nlinarith [mul_pos hb hc]` |
|---|---|
| `ha : 0 ≤ a, hb : 0 < b, hc : 0 < c ⊢ 0 < a + b * c` | closed |

---

## Part 2 · `cos_eq_one` (milestone)

Statement: for a non-trivial `IC`, from `hx : IC.trajectory S t = IC.x₀` and
`hv : ∂ₜ (IC.trajectory S) t = IC.v₀`, conclude `cos (S.ω * t.val) = 1`.

### The oscillator's formulas

**R7 · `rw [InitialConditions.trajectory_eq] at hx`** changes the **context**. Lemma (physlib):
`IC.trajectory S = fun t => cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀`. After the
rewrite `hx` holds the formula applied to `t`, not yet β-reduced (R10). It also works on a goal.
Placeholders: `(IC : InitialConditions) (S : HarmonicOscillator) (t : Time) (y : EuclideanSpace ℝ (Fin 1))`.

| Before | After |
|---|---|
| `hx : InitialConditions.trajectory S IC t = y ⊢ cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀ = y` | `hx : (fun t => cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀) t = y ⊢ cos (S.ω * t.val) • IC.x₀ + (sin (S.ω * t.val) / S.ω) • IC.v₀ = y` |

**R8 · `rw [InitialConditions.trajectory_velocity] at hv`** changes the **context**. Lemma (physlib):
`∂ₜ (IC.trajectory S) = fun t => -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀`.
Same placeholders as R7.

| Before | After |
|---|---|
| `hv : ∂ₜ (InitialConditions.trajectory S IC) t = y ⊢ -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ = y` | `hv : (fun t => -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀) t = y ⊢ -S.ω • sin (S.ω * t.val) • IC.x₀ + cos (S.ω * t.val) • IC.v₀ = y` |

### From a vector equation to scalar equations

**R9 · `congrArg (fun w => ⟪a, w⟫_ℝ) h`** changes the **context**. `congrArg f : u = v → f u = f v`
applies the same function to both sides; with `f = fun w => ⟪a, w⟫_ℝ` an equation of vectors becomes an
equation of real numbers. Placeholders: `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a u v : E) (h : u = v)`.

| Before | After `have h' := congrArg (fun w => ⟪a, w⟫_ℝ) h` |
|---|---|
| `h : u = v ⊢ ⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ` | context gains `h' : ⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ`; `⊢ ⟪a, u⟫_ℝ = ⟪a, v⟫_ℝ` |

**R10 · `simp only at h`** changes the **context**: β-reduction, `(fun x => body) a` becomes `body` with
`a` substituted. `simp only [R11, R12] at h` does this as part of its work; `rw` does not, and it cannot
find `y + z` inside an un-reduced `(fun t => … + …) t`. Placeholders: `{E : Type} (f : ℝ → E) (s : ℝ)`.

| Before | After |
|---|---|
| `h : P ((fun r => f r) s) ⊢ P (f s)` | `h : P (f s) ⊢ P (f s)` |

**R11 · `inner_add_right`** changes the **goal** (or `h`, with `at h`). Lemma:
`⟪x, y + z⟫_ℝ = ⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ`. Placeholders: `{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y z : E)`.

| Before | After `rw [inner_add_right]` |
|---|---|
| `⊢ P ⟪x, y + z⟫_ℝ` | `⊢ P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)` |

**R12 · `real_inner_smul_right`** changes the **goal** (or `h`). Lemma: `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ`.
On `⟪v₀, -S.ω • sin θ • x₀⟫_ℝ` it fires twice and gives `-S.ω * (sin θ * ⟪v₀, x₀⟫_ℝ)`.
Placeholders: `(x y : E) (r : ℝ)`, `E` as in R11.

| Before | After `rw [real_inner_smul_right]` |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℝ` | `⊢ P (r * ⟪x, y⟫_ℝ)` |

**R13 · `real_inner_comm x y`** changes the **goal** (or `h`). Lemma: `real_inner_comm x y : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ`.
The explicit arguments are in the order of the **right** side, so `rw [real_inner_comm IC.x₀ IC.v₀] at h2`
turns `⟪IC.v₀, IC.x₀⟫_ℝ` into `⟪IC.x₀, IC.v₀⟫_ℝ`. You need this because R9 on `hx` produces
`⟪x₀, v₀⟫` while R9 on `hv` produces `⟪v₀, x₀⟫`, and `linear_combination` (R16) treats them as different
unknowns. Placeholders: `(x y : E)`.

| Before | After `rw [real_inner_comm x y]` |
|---|---|
| `⊢ P ⟪y, x⟫_ℝ` | `⊢ P ⟪x, y⟫_ℝ` |

### Algebra with a nonzero denominator

**R14 · `HarmonicOscillator.ω_ne_zero`** changes the **context**. Lemma: `S.ω ≠ 0` (write `S.ω_ne_zero`).
`field_simp` (R15, R22) looks for exactly this fact. Placeholders: `(S : HarmonicOscillator)`.

| Before | After `have h := S.ω_ne_zero` |
|---|---|
| `⊢ S.ω ≠ 0` | `h : S.ω ≠ 0 ⊢ S.ω ≠ 0` |

**R15 · `field_simp at h`** changes the **context**: it multiplies `h` through by every denominator `c`
for which `c ≠ 0` is in the context, and puts the result in its own normal form (factor order is its
choice: read it off before you use it). Placeholders: `(a b c x y : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0, h : a * x + b / c * y = x ⊢ a * x * c + b * y = x * c` | `h : a * x * c + b * y = x * c ⊢ a * x * c + b * y = x * c` |

**R16 · `linear_combination e₁ * h₁ + h₂`** **closes** an equation `L = R` when `L - R` equals
`e₁ * (lhs₁ - rhs₁) + (lhs₂ - rhs₂)` as polynomials (it calls `ring` to check). The `eᵢ` are any terms,
for instance `S.ω`; any number of hypotheses, with `+`, `-` and coefficients. To find the coefficients,
write `L - R` and the `lhsᵢ - rhsᵢ` on paper and match the monomials. Placeholders: `(a b x : ℝ)`.

| Before | After `linear_combination h₁ - a * h₂` |
|---|---|
| `h₁ : a * x = b, h₂ : x = 1 ⊢ a = b` | closed |

### Using a product that is zero

**R17 · `mul_eq_zero`** changes the **context**. Lemma: `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp hab` reads it left
to right. Split the `∨` with R4: `rcases mul_eq_zero.mp key with h | h`. Placeholders: `(a b : ℝ)`.

| Before | After `have h := mul_eq_zero.mp hab` |
|---|---|
| `hab : a * b = 0 ⊢ a = 0 ∨ b = 0` | `h : a = 0 ∨ b = 0 ⊢ a = 0 ∨ b = 0` |

**R18 · `h.ne'`** (lemma `LT.lt.ne' : b < a → a ≠ b`) changes the **context**: from `h : 0 < a` it gives
`a ≠ 0` (the primed version flips the sides; `h.ne` gives `0 ≠ a`). With Part 1:
`(det_pos S IC non_trivial).ne'`. Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After `have h := ha.ne'` |
|---|---|
| `ha : 0 < a ⊢ a ≠ 0` | `h : a ≠ 0 ⊢ a ≠ 0` |

**R19 · `absurd h hne`** **closes** any goal. `absurd : A → ¬A → G`; `a ≠ 0` is by definition
`¬(a = 0)`. Placeholders: `(a : ℝ) (G : Prop)`.

| Before | After `exact absurd h hne` |
|---|---|
| `h : a = 0, hne : a ≠ 0 ⊢ G` | closed |

**R20 · `linarith`** **closes** a linear equality or inequality that follows from the hypotheses by
adding them with constant coefficients. Placeholders: `(c : ℝ)`.

| Before | After `linarith` |
|---|---|
| `h : c - 1 = 0 ⊢ c = 1` | closed |

---

## Part 3 · `state_at_period` (milestone)

Statement: if `hn : ↑n * (2 * π / S.ω) = t.val` then the trajectory and the velocity at `t` equal
`IC.x₀` and `IC.v₀`. Prove `S.ω * t.val = ↑(2 * n) * π` first; then `cos = 1`, `sin = 0` collapse both
formulas.

**R21 · `push_cast`** changes the **goal**: it moves casts `↑(…)` from `ℤ` into `ℝ` down to the variables,
using `↑(a * b) = ↑a * ↑b`, `↑(a + b) = ↑a + ↑b`, `↑3 = 3`. Do it before `ring` or `field_simp`,
which cannot see through a cast. Placeholders: `(n m : ℤ)`.

| Before | After |
|---|---|
| `⊢ P ↑(3 * n + m)` | `⊢ P (3 * ↑n + ↑m)` |

**R22 · `field_simp`** changes the **goal**: like R15, on the goal. The fact `c ≠ 0` can be in the context
or passed in brackets, `field_simp [S.ω_ne_zero]`. If what is left is trivial (`ring_nf` closes it),
the goal is closed. Placeholders: `(a b c : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ a * (b / c) = b` | `⊢ a * b = b * c` |

**R23 · `Real.cos_eq_one_iff`** changes the **goal**. Lemma: `Real.cos_eq_one_iff x : cos x = 1 ↔ ∃ n : ℤ, ↑n * (2 * π) = x`
(`x` is explicit). Use `rw` on a goal `cos x = 1`, then give the integer with `exact ⟨k, proof⟩`.
From a hypothesis `h : cos x = 1`, use `(Real.cos_eq_one_iff _).mp h : ∃ n : ℤ, ↑n * (2 * π) = x`.
Placeholders: `(x : ℝ) (k : ℤ)`.

| Before | After `rw [Real.cos_eq_one_iff]` |
|---|---|
| `⊢ cos x = 1` | `⊢ ∃ n, ↑n * (2 * π) = x` |

**R24 · `Real.sin_int_mul_pi`** changes the **goal**. Lemma: `Real.sin_int_mul_pi n : sin (↑n * π) = 0` for
`n : ℤ`; `exact Real.sin_int_mul_pi _` closes such a goal. Placeholders: `(n : ℤ)`.

| Before | After `rw [Real.sin_int_mul_pi]` |
|---|---|
| `⊢ P (sin (↑n * π))` | `⊢ P 0` |

**R25 · `simp only [hc, hs]`** changes the **goal**: the hypotheses `hc : cos θ = 1`, `hs : sin θ = 0`
are used as rewrite rules (it β-reduces too, like R10). Placeholders:
`{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ w : ℝ) (x v : E)`.

| Before | After |
|---|---|
| `hc : cos θ = 1, hs : sin θ = 0 ⊢ P ((sin θ / w) • x + cos θ • v)` | `⊢ P ((0 / w) • x + 1 • v)` |

**R26 · `simp`** **closes** what is left with its standard lemmas `zero_div : 0 / a = 0`,
`zero_smul : 0 • v = 0`, `one_smul : 1 • v = v`, `smul_zero : r • 0 = 0`, `zero_add`, `add_zero`,
`neg_zero`, `mul_zero`. In the exercise `simp [hc, hs]` does R25 and R26 in one call.

| Before | After `simp` |
|---|---|
| `⊢ (0 / w) • x + 1 • v = v` | closed |

---

## Part 4 · `returns_iff_whole_periods`

Statement: for non-trivial `IC`, `(IC.trajectory S t = IC.x₀ ∧ ∂ₜ (IC.trajectory S) t = IC.v₀) ↔ ∃ n : ℤ, ↑n * (2 * π / S.ω) = t.val`.
(→) is Part 2 plus R23 and an R22/R16 rearrangement; (←) is Part 3.

**R27 · `constructor` on `A ↔ B`** changes the **goal list**: the two directions, as implications.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B` (case `mp`), `⊢ B → A` (case `mpr`) |

**R28 · `rintro ⟨ha, hb⟩`** changes the **goal and the context**: it introduces the premise of an
implication and takes it apart at once. The same pattern opens an `∃`: `rintro ⟨n, hn⟩` on
`(∃ n, Q n) → C`. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → C` | `ha : A, hb : B ⊢ C` |

**R29 · `obtain ⟨n, hn⟩ := h`** changes the **context**: a hypothesis (or any proof term)
`h : ∃ n, Q n` is replaced by a witness `n` and its property `hn`. Use it on
`(Real.cos_eq_one_iff _).mp (…)`. Placeholders: `(Q : ℤ → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `h : ∃ n, Q n` and `⊢ G` | `n : ℤ, hn : Q n ⊢ G` (`h` is gone) |

Then `refine ⟨n, ?_⟩` (TACTIC_STATES, "Structure") leaves the equation for that witness. R23 gives
`hn : ↑n * (2 * π) = S.ω * t.val`; the goal has `/ S.ω`, so clear it with R22 and finish with R16 using `hn`.

### Worked combinations (W1–W4, on equations that are not the exercise's)

**W1: pair a vector equation with a vector.** From `h : a • x + b • y = y`, R9 with `fun w => ⟪y, w⟫_ℝ`
gives `h' : ⟪y, a • x + b • y⟫_ℝ = ⟪y, y⟫_ℝ`; then
`simp only [inner_add_right, real_inner_smul_right] at h'` (R10–R12 in one call) gives
`h' : a * ⟪y, x⟫_ℝ + b * ⟪y, y⟫_ℝ = ⟪y, y⟫_ℝ`, which is the goal:

```lean-goal
⊢ a * ⟪y, x⟫_ℝ + b * ⟪y, y⟫_ℝ = ⟪y, y⟫_ℝ
```

**W2: eliminate a cross term, factor, cancel a positive factor.** From `h₁ : c * p + r = p`,
`h₂ : c * q - r = q`, `hp : 0 < p`, `hq : 0 ≤ q`: `key : (p + q) * (c - 1) = 0` by
`linear_combination h₁ + h₂` (R16); `rcases mul_eq_zero.mp key with h | h` (R17, R4); in case `inl`,
`absurd h (add_pos_of_pos_of_nonneg hp hq).ne'` (R18, R19); in case `inr`, `linarith` (R20). Both cases
start from

```lean-goal
⊢ c = 1
```

**W3: `cos = 1` at a multiple of `4π`.** R23, then the witness `2 * k`, then R21 and `ring`:

```lean-goal
⊢ cos (↑k * (4 * π)) = 1
⊢ ∃ n, ↑n * (2 * π) = ↑k * (4 * π)
```

**W4: clear a denominator in the goal, then use an equation** `h : a * 3 = c * b` (R22, R16):

```lean-goal
⊢ a * (3 / c) = b
⊢ a * 3 = c * b
```

---

## Traps

- `rw [inner_add_right] at h1` fails right after R9: `h1` still contains `(fun t => …) t`. Use
  `simp only [inner_add_right, real_inner_smul_right] at h1 h2`, which β-reduces first (R10).
- `real_inner_comm x y` rewrites `⟪y, x⟫` to `⟪x, y⟫` (arguments in the order of the result). Without it,
  `⟪x₀, v₀⟫` and `⟪v₀, x₀⟫` are two different unknowns for `linear_combination` and `ring`.
- `field_simp` does nothing to `/ S.ω` unless `S.ω ≠ 0` is in the context (R14) or in its brackets.
  Its output order (`S.ω * cos … * ⟪…⟫`) is its own: read the new hypothesis before choosing the
  `linear_combination` coefficients.
- `-S.ω • sin θ • IC.x₀` is `(-S.ω) • (sin θ • IC.x₀)`, so R12 fires twice on it.
- `((2 * n : ℤ) : ℝ)` prints as `↑(2 * n)`. `ring` cannot match it with `2 * ↑n`; `push_cast` first (R21).
- `Real.cos_eq_one_iff` states `↑n * (2 * π) = x` with `n` first and `2 * π` in parentheses; the
  exercise's target is `↑n * (2 * π / S.ω) = t.val`, so a rearrangement (R22, R16) is needed.
- `Real.cos_eq_one_iff` takes `x` explicitly: write `(Real.cos_eq_one_iff _).mp h`, not `Real.cos_eq_one_iff.mp h`.
- BANNED: physlib's `HarmonicOscillator.return_time` (this theorem) and `trajectory_periodic`; also the
  search tactics `exact?`, `apply?`, `try?`, `hint`.
- Both equations are needed: position alone returns twice per period in general, so the ⇒ direction
  needs `hx` and `hv` together, combined as in Part 2.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 ≤ ⟪x, x⟫_ℝ` | `have hx : 0 ≤ ⟪x, x⟫_ℝ := real_inner_self_nonneg` | R1 |
| `0 < S.ω ^ 2` | `have hω := pow_pos S.ω_pos 2` | R2, R3 |
| split `A ∨ B` hypothesis | `rcases h with h \| h` | R4 |
| `x ≠ 0 → 0 < ⟪x, x⟫_ℝ` | `real_inner_self_pos.mpr h` | R5 |
| nonlinear inequality | `nlinarith [fact₁, fact₂]` | R6 |
| position / velocity formula | `rw [InitialConditions.trajectory_eq] at hx` / `rw [InitialConditions.trajectory_velocity] at hv` | R7, R8 |
| vector eq. → real eq. | `have h1 := congrArg (fun w => ⟪a, w⟫_ℝ) hx` | R9 |
| expand inner products | `simp only [inner_add_right, real_inner_smul_right] at h1 h2` | R10–R12 |
| `⟪y, x⟫ → ⟪x, y⟫` | `rw [real_inner_comm x y] at h` | R13 |
| clear `/ S.ω` | `have hω := S.ω_ne_zero; field_simp at h` / `field_simp [S.ω_ne_zero]` | R14, R15, R22 |
| equation from a linear combination | `linear_combination e * h1 + h2` | R16 |
| `a * b = 0` → cases | `rcases mul_eq_zero.mp key with h \| h` | R17, R4 |
| `0 < a` → `a ≠ 0`; contradiction | `h.ne'`; `absurd h hne` | R18, R19 |
| linear goal | `linarith` | R20 |
| integer casts | `push_cast` | R21 |
| `cos x = 1 ↔ ∃ n : ℤ, ↑n * (2 * π) = x` | `rw [Real.cos_eq_one_iff]` / `(Real.cos_eq_one_iff _).mp h` | R23 |
| `sin (↑n * π) = 0` | `Real.sin_int_mul_pi _` | R24 |
| collapse with `cos = 1`, `sin = 0` | `simp [hc, hs]` | R25, R26 |
| split `↔` | `constructor` | R27 |
| open `A ∧ B →` / `(∃ n, …) →` | `rintro ⟨ha, hb⟩` / `rintro ⟨n, hn⟩` | R28 |
| open an `∃` proof | `obtain ⟨n, hn⟩ := h` | R29 |
| give the witness | `refine ⟨n, ?_⟩` | TACTIC_STATES |
| see the state | infoview | |
