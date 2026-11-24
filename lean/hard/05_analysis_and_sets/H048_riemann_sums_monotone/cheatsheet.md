# H048 · Riemann sums of monotone functions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` as an ordered
field, finite sums `∑ k ∈ Finset.range n, …`, casts `ℕ → ℝ`, the interval integral `∫ x in a..b, f x`
(Lebesgue integral on `ℝ`) with its two basic facts (integral of a constant, monotonicity of the integral),
and an epsilon–N limit written by hand (`ConvergesTo`; Mathlib's `Tendsto` is banned here).

The mathematics. Write `N = n + 1` (a real number in the proof) and cut `[0, 1]` into the pieces
`[k/N, (k+1)/N]`, `k = 0, …, n`. Since `f` is monotone, on piece `k` it lies between the constants
`f (k/N)` and `f ((k+1)/N)`, so `f (k/N) / N ≤ ∫ piece ≤ f ((k+1)/N) / N` (`piece`). The pieces add up to
`∫₀¹ f` (`split_integral`). The lower bounds add up to `leftSum f n`; the upper bounds telescope to
`leftSum f n + (f 1 - f 0) / N` (`upper_sum`). So `∫₀¹ f` is squeezed between the two (`sandwich`), the gap
`(f 1 - f 0) / N` goes to `0`, and `|leftSum f n - ∫₀¹ f| < ε` once `N > (f 1 - f 0) / ε`
(`riemann_monotone`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`/`apply`/`have`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. All of them are real numbers `(a b c : ℝ)`, naturals `(m n : ℕ)`,
  sequences `(u : ℕ → ℝ)` or functions `(f g : ℝ → ℝ)`; the Mathlib lemmas hold more generally (ordered
  fields, normed spaces), and `ℝ` meets every requirement.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `↑k` (with `k : ℕ`) | the natural number `k` cast into `ℝ` (`Nat.cast`). `↑(k + 1)` and `↑k + 1` are equal but different terms (R14). In the source, `f (k / (n + 1))` with `k n : ℕ` is real division: `f` takes a real, so Lean casts `k` and `n` first and prints `↑k / (↑n + 1)` |
| `noncomputable def` | a definition Lean cannot compile to code (it uses real numbers / integrals); you can still unfold it and prove things about it |
| `x / c`, `c⁻¹` | real division and inverse. Lean sets `x / 0 = 0`, so lemmas about `/` need `c ≠ 0` or `0 < c` |
| `\|x\|` | absolute value |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` of naturals |
| `∑ k ∈ Finset.range n, u k` | the finite sum `u 0 + … + u (n - 1)`; the bound name (`k`, `i`, `x`) is irrelevant |
| `Monotone f` | `∀ ⦃a b⦄, a ≤ b → f a ≤ f b`. The `⦃⦄` binders are implicit, so `hf h : f a ≤ f b` for `h : a ≤ b` (R8) |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}`; `hx : x ∈ Set.Icc a b` is the pair `a ≤ x ∧ x ≤ b` (R7) |
| `∀ x ∈ S, P x` | `∀ x, x ∈ S → P x` |
| `MeasureTheory.volume` | Lebesgue measure on `ℝ` (length). All integrals here are against it |
| `∫ (x : ℝ) in a..b, f x` | the interval integral `∫ₐᵇ f(x) dx` against `volume` (and `-∫ᵇₐ` when `b < a`). Lean prints the type of the bound variable; the name (`x`, `u`) is irrelevant |
| `∫ (x : ℝ) in a..b, c` | the integral of the constant `c`, equal to `(b - a) • c` (R9) |
| `IntervalIntegrable f MeasureTheory.volume a b` | `f` is Lebesgue-integrable on the interval between `a` and `b`; constants (R5) and monotone functions (R6) are |
| `(b - a) • c` | scalar multiplication `•`; for two reals it is `*` (R10) |
| `∀ ε > 0, P ε` | `∀ ε, ε > 0 → P ε`; `ε > 0` is notation for `0 < ε` |
| `∀ n ≥ N, Q n` | `∀ n, n ≥ N → Q n` |
| `∃ N, …` | there is a natural `N` with …; Lean omits the type `ℕ` when printing |
| `leftSum f n` | the spec's `(∑ k ∈ Finset.range (n + 1), f (↑k / (↑n + 1))) / (↑n + 1)` |
| `ConvergesTo a L` | the spec's `∀ ε > 0, ∃ N, ∀ n ≥ N, \|a n - L\| < ε` |
| `case left`, `case right` | the two goals after `constructor` on `A ∧ B` |
| `case hab`, `case e_a` | goal names after `gcongr` (R1) and `congr 1` (R23); ignore them |

---

## Part 1 · `piece` (milestone)

Statement: for `0 < N` and `k : ℕ`, `f (↑k / N) / N ≤ ∫ x in ↑k/N..(↑k+1)/N, f x` and
`∫ x in ↑k/N..(↑k+1)/N, f x ≤ f ((↑k + 1) / N) / N`. Compare `f` with a constant on one piece, then integrate
the constant.

**R1 · `gcongr`** changes the **goal**: it reduces an inequality between two expressions of the same shape to
an inequality between the parts that differ. For `x / c ≤ y / c` that is `x ≤ y`; the side condition
`0 ≤ c` is discharged from `hc : 0 < c` in the context. Placeholders: `(x c : ℝ) (hc : 0 < c)`. In the
exercise: `↑k / N ≤ (↑k + 1) / N`.

| Before | After |
|---|---|
| `⊢ x / c ≤ (x + 1) / c` | `⊢ x ≤ x + 1` |

**R2 · `linarith`** **closes** a goal `t < s`, `t ≤ s`, `t = s` (or `False`) that follows from the
hypotheses by adding them up with nonnegative rational coefficients. Products of two variables are treated
as atoms. Placeholders: `(a b c : ℝ) (h1 : a ≤ b) (h2 : b < c)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b < c ⊢ a < c` | closed |

**R3 · `field_simp`** changes the **goal**: it multiplies out denominators it can prove nonzero (from
hypotheses such as `hc : 0 < c` or `hc : c ≠ 0`), leaving a polynomial identity for `ring`. Placeholders:
`(x c : ℝ) (hc : 0 < c)`. In the exercise: the width fact `hw : (↑k + 1) / N - ↑k / N = 1 / N`.

| Before | After `field_simp` |
|---|---|
| `⊢ (x + 2) / c - x / c = 2 / c` | `⊢ x + 2 - x = 2` (then `ring`) |

**R4 · `intervalIntegral.integral_mono_on`** changes the **goal list**. The lemma is
`a ≤ b → IntervalIntegrable f μ a b → IntervalIntegrable g μ a b → (∀ x ∈ Set.Icc a b, f x ≤ g x) →
∫ x in a..b, f x ∂μ ≤ ∫ x in a..b, g x ∂μ` (`∂μ` is omitted when `μ = volume`). With `apply` the goal
becomes its four hypotheses. In the exercise you use it forward,
`have h := intervalIntegral.integral_mono_on hle hint₁ hint₂ hpt`, which adds `h : ∫ f ≤ ∫ g`.
Placeholders: `(f g : ℝ → ℝ) (a b : ℝ)`; for the lower bound `f` is the constant `fun _ => f (↑k / N)` and
`g` is `f`; for the upper bound the other way round.

| Before | After |
|---|---|
| `⊢ ∫ (x : ℝ) in a..b, f x ≤ ∫ (x : ℝ) in a..b, g x` | `⊢ a ≤ b`, `⊢ IntervalIntegrable f MeasureTheory.volume a b`, `⊢ IntervalIntegrable g MeasureTheory.volume a b`, `⊢ ∀ x ∈ Set.Icc a b, f x ≤ g x` |

**R5 · `intervalIntegrable_const`** **closes** the integrability of a constant function. Inside the
`have h := …` of R4 nothing tells Lean the measure, so write `intervalIntegrable_const (μ := MeasureTheory.volume)`.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable (fun x => c) MeasureTheory.volume a b` | closed |

**R6 · `hu.intervalIntegrable`** (`Monotone.intervalIntegrable`) **closes** the integrability of a monotone
function on any interval. Placeholders: `(u : ℝ → ℝ) (hu : Monotone u) (a b : ℝ)`. In the exercise:
`hf.intervalIntegrable`.

| Before | After |
|---|---|
| `⊢ IntervalIntegrable u MeasureTheory.volume a b` | closed |

**R7 · `hx.1`, `hx.2`** change the **context** (with `have`): `hx : x ∈ Set.Icc a b` unfolds to
`a ≤ x ∧ x ≤ b`, so `.1` and `.2` are its two halves. Placeholders: `(a b x : ℝ)`. In the exercise this is
the pointwise bound `fun x hx => …` you pass as the fourth argument of R4.

| Before | After |
|---|---|
| `hx : x ∈ Set.Icc a b ⊢ G` | `h1 : a ≤ x ⊢ G` |

**R8 · `hu h`** changes the **context** (with `have`): a monotonicity hypothesis is a function from
`a ≤ b` to `u a ≤ u b`. Placeholders: `(u : ℝ → ℝ) (hu : Monotone u) (h : a ≤ b)`. With R7: `hf hx.1` is
`f (↑k / N) ≤ f x` for `x` in the piece.

| Before | After |
|---|---|
| `h : a ≤ b ⊢ G` | `hab : u a ≤ u b ⊢ G` |

**R9 · `rw [intervalIntegral.integral_const]`** changes the **goal** (or a hypothesis, with `at h`). The
lemma is `∫ x in a..b, c = (b - a) • c`. Placeholders: `(a b c : ℝ)`. In the exercise you rewrite the `h`
from R4: `rw [intervalIntegral.integral_const, smul_eq_mul, hw] at h`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, c)` | `⊢ P ((b - a) • c)` |

**R10 · `rw [smul_eq_mul] at h`** changes the **context**: `a • b = a * b` when `a` and `b` are numbers of
the same type. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : P (a • b) ⊢ P (a * b)` | `h : P (a * b) ⊢ P (a * b)` |

**R11 · `linarith [show T by tac]`** **closes** the goal like R2, after adding the fact `T` (proved on the
spot by `tac`) to the hypotheses. Use it when `linarith` needs a fact it cannot find: a nonlinear one, or a
rearrangement such as `f (↑k / N) / N = 1 / N * f (↑k / N)` (proved `by ring`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ 0 ≤ a + b ^ 2` | closed by `linarith [show (0 : ℝ) ≤ b ^ 2 by positivity]` |

---

## Part 2 · `split_integral` (milestone)

Statement: `∫ x in 0..1, f x = ∑ k ∈ Finset.range (n + 1), ∫ x in ↑k/(↑n+1)..(↑k+1)/(↑n+1), f x`. Instantiate
the adjacent-intervals lemma with the cut points `a k = ↑k / (↑n + 1)`, then clean the casts.

**R12 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from variables of a
known sign, casts `↑n` (nonnegative), numerals, `+`, `*`, `/`, `^`. For a variable it uses only a hypothesis
that bounds that variable directly (`hc : 0 < c`, `1 ≤ c`); it does no other reasoning. Placeholders: `(n : ℕ)`. In the exercise: `hN : (n + 1 : ℝ) ≠ 0` and `0 < (n : ℝ) + 1`; write the
type `ℝ`, or the fact is about naturals.

| Before | After |
|---|---|
| `⊢ 2 * ↑n + 3 ≠ 0` | closed |

**R13 · `intervalIntegral.sum_integral_adjacent_intervals`** changes the **goal list** (with `apply`). The
lemma is `(∀ k < m, IntervalIntegrable g μ (a k) (a (k + 1))) →
∑ k ∈ Finset.range m, ∫ x in a k..a (k + 1), g x ∂μ = ∫ x in a 0..a m, g x ∂μ`. Placeholders:
`(g : ℝ → ℝ) (a : ℕ → ℝ) (m : ℕ)`. In the exercise you use it forward, naming the implicit arguments:
`have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / (n + 1)) (n := n + 1) (fun k _ => …)`
(W4). The resulting `h` mentions `↑(k + 1)`, `↑0` and `↑(n + 1) / (↑n + 1)`: clean them with R14–R16.

| Before | After |
|---|---|
| `⊢ ∑ k ∈ Finset.range m, ∫ (x : ℝ) in a k..a (k + 1), g x = ∫ (x : ℝ) in a 0..a m, g x` | `⊢ ∀ k < m, IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1))` |

**R14 · `simp only [Nat.cast_add, Nat.cast_one]`** changes the **goal** (or `at h`). The lemmas are
`↑(m + n) = ↑m + ↑n` and `↑1 = 1`: they push the cast `ℕ → ℝ` inside. Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(m + 1)` | `⊢ P (↑m + 1)` |

**R15 · `simp only [Nat.cast_zero, zero_div]`** changes the **goal** (or `at h`): `↑0 = 0` and
`0 / c = 0`. Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑0 / c)` | `⊢ P 0` |

**R16 · `simp only [div_self hc]`** changes the **goal** (or `at h`). The lemma is `c ≠ 0 → c / c = 1`;
give it the proof `hc`. Placeholders: `(c : ℝ) (hc : c ≠ 0)`. In the exercise: `div_self hN` turns
`(↑n + 1) / (↑n + 1)` into `1`, after R14 has turned `↑(n + 1)` into `↑n + 1`. All of R14–R16 go in one
`simp only [...] at h`.

| Before | After |
|---|---|
| `⊢ P (c / c)` | `⊢ P 1` |

**R17 · `exact h.symm`** **closes** `b = a` from `h : a = b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a = b ⊢ b = a` | closed |

---

## Part 3 · `upper_sum` (milestone)

Statement: `∑ k ∈ Finset.range (n + 1), f ((↑k + 1) / (↑n + 1)) / (↑n + 1) = leftSum f n + (f 1 - f 0) / (↑n + 1)`.
The upper sum is the lower sum shifted by one index; the telescoping identity gives the difference.

**R18 · `Finset.sum_range_sub`** changes the **goal** (with `rw`). The lemma is
`∑ i ∈ Finset.range m, (u (i + 1) - u i) = u m - u 0`. Placeholders: `(u : ℕ → ℝ) (m : ℕ)`. In the exercise
you use it forward: `have tel := Finset.sum_range_sub (fun k : ℕ => f (k / (n + 1 : ℝ))) (n + 1)`, then
clean `tel` with R14–R16 (`↑(n + 1) / (↑n + 1)` becomes `1`, `↑0 / _` becomes `0`).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range m, (u (i + 1) - u i))` | `⊢ P (u m - u 0)` |

**R19 · `Finset.sum_sub_distrib`** changes the **goal** (or `at tel`). The lemma is
`∑ i ∈ s, (u i - v i) = ∑ i ∈ s, u i - ∑ i ∈ s, v i`. Placeholders: `(u v : ℕ → ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range m, (u i - v i))` | `⊢ P (∑ x ∈ Finset.range m, u x - ∑ x ∈ Finset.range m, v x)` |

**R20 · `unfold D`** changes the **goal**: it replaces the defined name `D` by its body. Placeholders: the
guide's `avg u m := (∑ i ∈ Finset.range m, u i) / ↑m`. In the exercise: `unfold leftSum`.

| Before | After |
|---|---|
| `⊢ P (avg u m)` | `⊢ P ((∑ i ∈ Finset.range m, u i) / ↑m)` |

**R21 · `rw [Finset.sum_div]`** changes the **goal**. The lemma is `(∑ i ∈ s, u i) / c = ∑ i ∈ s, u i / c`:
left to right it pushes the division into the sum (Part 4), and `rw [← Finset.sum_div]` pulls it out
(Part 3). Placeholders: `(u : ℕ → ℝ) (m : ℕ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ Finset.range m, u i) / c)` | `⊢ P (∑ i ∈ Finset.range m, u i / c)` |

**R22 · `rw [← add_div]`** changes the **goal**. The lemma is `add_div : (a + b) / c = a / c + b / c`, and
`←` uses it right to left, merging two fractions with the same denominator. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / c + b / c)` | `⊢ P ((a + b) / c)` |

**R23 · `congr 1`** changes the **goal**: for `F x = F y` with the same outer function it leaves `x = y`
(and closes the parts that are already equal). Here `F = (· / c)`. Placeholders: `(x y c : ℝ)`. After it, the
goal is linear in the two sums and `tel`: finish with R2.

| Before | After |
|---|---|
| `⊢ x / c = y / c` | `⊢ x = y` |

---

## Part 4 · `sandwich` (milestone)

Statement: `leftSum f n ≤ ∫ x in 0..1, f x ∧ ∫ x in 0..1, f x ≤ leftSum f n + (f 1 - f 0) / (↑n + 1)`.
Split the `∧`. In each half rewrite `∫₀¹` with `split_integral` (and, in the second half, the right side with
`← upper_sum`), so both sides are sums over the same range; then compare term by term with `piece`.

**R24 · `Finset.sum_le_sum`** changes the **goal**. The lemma is
`(∀ i ∈ s, u i ≤ v i) → ∑ i ∈ s, u i ≤ ∑ i ∈ s, v i`. Placeholders: `(u v : ℕ → ℝ) (m : ℕ)`. As a term:
`Finset.sum_le_sum fun k _ => (piece f hf _ hN k).1` (the `_` is the membership `k ∈ range`, unused; `.1` and
`.2` take the halves of `piece`).

| Before | After |
|---|---|
| `⊢ ∑ i ∈ Finset.range m, u i ≤ ∑ i ∈ Finset.range m, v i` | `⊢ ∀ i ∈ Finset.range m, u i ≤ v i` |

---

## Part 5 · `riemann_monotone`

Statement: `ConvergesTo (leftSum f) (∫ x in 0..1, f x)`: for every `ε > 0` some `N` makes
`|leftSum f n - ∫₀¹ f| < ε` for all `n ≥ N`. By `sandwich` the difference lies in `[-(f 1 - f 0)/(n+1), 0]`,
so it suffices that `(f 1 - f 0) / (n + 1) < ε`.

**R25 · `intro ε hε`** changes the **goal and the context**. `intro` sees through a definition whose body is a
`∀`, so `ConvergesTo …` needs no `unfold`. Placeholders: the guide's `Small u := ∀ ε > 0, ∃ N : ℕ, u N < ε`.

| Before | After |
|---|---|
| `⊢ Small u` | `ε : ℝ, hε : ε > 0 ⊢ ∃ N, u N < ε` |

**R26 · `obtain ⟨N, hN⟩ := exists_nat_gt x`** changes the **context**. The lemma is `∃ n : ℕ, x < ↑n` (the
reals are Archimedean). Placeholders: `(x : ℝ)`. In the exercise `x = (f 1 - f 0) / ε`.

| Before | After |
|---|---|
| `⊢ ∃ N, P N` | `N : ℕ, hN : x < ↑N ⊢ ∃ N, P N` |

**R27 · `refine ⟨N, fun n hn => ?_⟩`** changes the **goal and the context**: it supplies the witness `N`, and
the `fun` introduces `n` and `hn : n ≥ N`. Placeholders: `(Q : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ M, ∀ n ≥ M, Q n` | `n : ℕ, hn : n ≥ N ⊢ Q n` |

**R28 · `obtain ⟨h1, h2⟩ := h`** changes the **context**: `h : A ∧ B` is replaced by its two halves. In the
exercise: `obtain ⟨h1, h2⟩ := sandwich f hf n`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `h1 : A, h2 : B ⊢ G` |

**R29 · `sub_nonneg.mpr`** changes the **context** (with `have`). The lemma is `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`,
and `.mpr` is its right-to-left direction. With R8: `sub_nonneg.mpr (hf zero_le_one) : 0 ≤ f 1 - f 0`
(`zero_le_one : 0 ≤ 1`). Placeholders: `(u : ℝ → ℝ) (hu : Monotone u)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : 0 ≤ u 2 - u 1 ⊢ G` |

**R30 · `exact_mod_cast h`** **closes** a goal about casts from the same statement without casts. Here
`hn : n ≥ N` on `ℕ` gives `(N : ℝ) ≤ ↑n`. Placeholders: `(m n : ℕ) (h : m ≤ n)`.

| Before | After |
|---|---|
| `h : m ≤ n ⊢ ↑m ≤ ↑n` | closed |

**R31 · `rw [div_lt_iff₀ hc]`** changes the **goal** (or a hypothesis, `at h`). The lemma is
`0 < c → (b / c < a ↔ b < a * c)`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`. In the exercise: on the goal
with `(by positivity)` for `0 < ↑n + 1`, and `at hN` with `hε` (W5).

| Before | After |
|---|---|
| `⊢ b / c < a` | `⊢ b < a * c` |

**R32 · `nlinarith`** **closes** goals like R2, but first adds products of pairs of hypotheses (and squares),
so it can use `ε > 0` times `↑N ≤ ↑n`. Placeholders: `(a b c : ℝ) (ha : 0 ≤ a) (hbc : b ≤ c)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a, hbc : b ≤ c ⊢ a * b ≤ a * c` | closed |

**R33 · `rw [abs_sub_lt_iff]`** changes the **goal**. The lemma is `|a - b| < c ↔ a - b < c ∧ b - a < c`.
Placeholders: `(a b c : ℝ)`. Then `constructor <;> linarith` with `h1`, `h2` and the bound on the gap.

| Before | After |
|---|---|
| the goal `\|a - b\| < c` | `⊢ a - b < c ∧ b - a < c` |

```lean-goal
⊢ |a - b| < c
⊢ a - b < c ∧ b - a < c
```

---

## Worked combinations (W1–W5, on objects that are not the exercise's)

**W1: the integral of a constant.** R9, R10, then `norm_num`:

```lean-goal
⊢ ∫ (x : ℝ) in 1..3, 5 = 10
⊢ (3 - 1) • 5 = 10
⊢ (3 - 1) * 5 = 10
```

**W2: comparing with a constant.** `x ≤ 1` on `[0, 1]` (R7 gives `hx.2 : x ≤ 1`), `x ↦ x` is monotone
(`monotone_id`, R6), the constant is integrable (R5). R4 used forward gives `h`; R9, R10 at `h`; R2 closes:

```lean-goal
⊢ ∫ (x : ℝ) in 0..1, x ≤ 1
```

**W3: telescoping.** `Finset.sum_range_sub (fun i : ℕ => (i : ℝ) * 2) m` (R18 forward), then R14, R15 at
`tel` give exactly the goal:

```lean-goal
⊢ ∑ i ∈ Finset.range m, ((↑i + 1) * 2 - ↑i * 2) = ↑m * 2
```

**W4: `[0, 2]` in four pieces.** R13 forward with `(a := fun k : ℕ => (k : ℝ) / 2) (n := 4)`; R14, R15 at `h`
leave `↑4 / 2`, which `norm_num at h` turns into `2`:

```lean-goal
⊢ ∑ k ∈ Finset.range 4, ∫ (x : ℝ) in ↑k / 2..(↑k + 1) / 2, g x = ∫ (x : ℝ) in 0..2, g x
```

**W5: `c / (n + 2) < ε` for all large `n`** (`0 ≤ c`). R25, R26 with `x = c / ε`, R27, R30 for `hn'`, R31 on the goal (side goal by R12)
and at `hN`, R32:

```lean-goal
⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, c / (↑n + 2) < ε
⊢ ∃ N, ∀ n ≥ N, c / (↑n + 2) < ε
⊢ c / (↑n + 2) < ε
⊢ c < ε * (↑n + 2)
```

After `rw [div_lt_iff₀ hε] at hN` the hypothesis reads `hN : c < ↑N * ε`; `nlinarith` multiplies
`hn' : ↑N ≤ ↑n` by `ε > 0` and closes.

---

## Traps

- The integrals are against `MeasureTheory.volume`. In `have h := intervalIntegral.integral_mono_on …` nothing
  fixes the measure, so write `intervalIntegrable_const (μ := MeasureTheory.volume)` (R5).
- `Finset.sum_range_sub` and `sum_integral_adjacent_intervals` produce `↑(k + 1)`, `↑0` and `↑(n + 1)`, while
  the statements have `↑k + 1`, `0`, `↑n + 1`. `rw` and `exact` see these as different: clean with
  `simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hN] at h` (R14–R16) first.
- `div_self hN` needs `hN : (n + 1 : ℝ) ≠ 0` in `ℝ`. Write the type; `(n + 1) ≠ 0` alone is about `ℕ`.
- After `simp only … at h` the bound variable may be renamed (`∑ x ∈ …` for `∑ k ∈ …`). The terms are the
  same; `exact` accepts them.
- `linarith` does not multiply hypotheses. The step `(f 1 - f 0) / (n + 1) < ε` needs `nlinarith` (R32) after
  clearing both denominators (R31), plus `hd : 0 ≤ f 1 - f 0` (R29) and `hn' : (N : ℝ) ≤ ↑n` (R30) in context.
- `div_lt_iff₀` is stated with `b / c` on the left: `rw` fails on `a < b / c` (that is `lt_div_iff₀`).
- No limits library: `Tendsto`, `Filter`, `atTop`, continuity and Mathlib's ready-made Riemann-sum bounds
  (`MonotoneOn.sum_le_integral`, …) are banned. Everything is the hand-written `∀ ε > 0, ∃ N, …`.
- The four milestones are optional: you may change or delete them, but `sandwich` uses all three others.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `x / c ≤ y / c` from `x ≤ y` | `gcongr` | R1 |
| linear arithmetic | `linarith`, `linarith [show T by tac]` | R2, R11 |
| width of a piece | `field_simp; ring` | R3 |
| `∫ f ≤ ∫ g` | `intervalIntegral.integral_mono_on hab hint₁ hint₂ (fun x hx => …)` | R4 |
| integrability | `intervalIntegrable_const (μ := MeasureTheory.volume)`, `hf.intervalIntegrable` | R5, R6 |
| use `x ∈ Set.Icc a b`, `Monotone f` | `hx.1`, `hx.2`, `hf h` | R7, R8 |
| `∫ x in a..b, c` | `rw [intervalIntegral.integral_const, smul_eq_mul] at h` | R9, R10 |
| `0 < e`, `e ≠ 0` | `positivity` | R12 |
| cut `∫` into pieces | `intervalIntegral.sum_integral_adjacent_intervals (a := …) (n := …) …` | R13 |
| clean casts | `simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hN] at h` | R14–R16 |
| flip an equation | `h.symm` | R17 |
| telescope | `Finset.sum_range_sub u m` | R18 |
| split / pull `/` out of a sum | `Finset.sum_sub_distrib`, `rw [← Finset.sum_div, ← add_div]` | R19, R21, R22 |
| unfold a definition | `unfold leftSum` | R20 |
| `x / c = y / c` → `x = y` | `congr 1` | R23 |
| compare sums termwise | `Finset.sum_le_sum fun k _ => …` | R24 |
| ε–N skeleton | `intro ε hε`, `obtain ⟨N, hN⟩ := exists_nat_gt x`, `refine ⟨N, fun n hn => ?_⟩` | R25–R27 |
| split an `∧` hypothesis | `obtain ⟨h1, h2⟩ := h` | R28 |
| `0 ≤ a - b` | `sub_nonneg.mpr h` | R29 |
| `ℕ` fact → `ℝ` fact | `exact_mod_cast h` | R30 |
| clear a positive denominator in `<` | `rw [div_lt_iff₀ hc]` | R31 |
| products of hypotheses | `nlinarith` | R32 |
| `\|a - b\| < c` | `rw [abs_sub_lt_iff]; constructor` | R33 |
| see the state | infoview | |
