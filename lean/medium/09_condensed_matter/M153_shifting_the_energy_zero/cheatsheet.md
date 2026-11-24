# M153 · Shifting the energy zero: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` and its
finite-system quantities in terms of the inverse temperature `b` (with `k_B = 1`): the partition function
`Z(b)`, the Boltzmann probabilities `p_b(i)` and the mean energy `U(b)`; building a modified structure with
`{ 𝓒 with … }`; Mathlib's finite sums `∑` and their algebra; `Real.exp`.

The physics: with energies `E i`, `Z(b) = ∑ᵢ exp(-b Eᵢ)`, `p_b(i) = exp(-b Eᵢ) / Z(b)`,
`U(b) = ∑ᵢ Eᵢ p_b(i)`. Shifting every `Eᵢ` by `c` multiplies every Boltzmann weight by the same factor
`exp(-b c)`, which cancels in `p_b`, and adds `c · ∑ᵢ p_b(i) = c` to `U`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓔 : CanonicalEnsemble ι` is any ensemble (the guide never uses the exercise's `shift`); `double 𝓔` is the
  guide's own modified ensemble with every energy doubled.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`. Its field `energy : ι → ℝ` gives each microstate's energy; other fields (`dof`, `phaseSpaceunit`, the measure `μ`, …) do not matter here |
| `[MeasurableSpace ι]` | `ι` carries a σ-algebra (needed by the structure; ignore it) |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[Nonempty ι]` | `ι` has at least one element (so `Z(b) > 0`) |
| `𝓒.energy i` | `Eᵢ`, the energy of microstate `i` |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, rexp (-b * 𝓒.energy i)` (R1) |
| `𝓒.probabilityBetaReal b i` | `p_b(i) = rexp (-b * 𝓒.energy i) / Z(b)` (R8, R15) |
| `𝓒.probabilityBetaReal b` | the function `i ↦ p_b(i)`; equations between these are equations of functions |
| `𝓒.meanEnergyBetaReal b` | `U(b) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i` (R18) |
| `{ 𝓒 with energy := f, energy_measurable := pf }` | a copy of `𝓒` with `energy` replaced by `f`; `pf` proves the new `f` measurable (R2) |
| `rexp x` | `Real.exp x`, the real exponential |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over all elements of the finite type |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι` (in lemma statements; here `s` is always `Finset.univ`) |
| `∑ x, …` | the same sum; `simp` renames bound variables to `x` |
| `case e_f` | the goal `congr 1` made: the summand functions must be equal |
| `inst✝ : Fintype ι` | an unnamed instance hypothesis: a `[Fintype ι]` binder of the statement |
| `{ energy := fun i => 𝓒.energy i + c, dof := 𝓒.dof, …, hPos := ⋯, … }` | `shift 𝓒 c` written out field by field, what `simp only [shift]` leaves where no `.energy` is read off; `⋯` is a hidden proof |

---

## Part 1 · `shift_Z`

Statement: `Z_shift(b) = exp(-b c) · Z(b)`. Unfold both partition functions and the shifted energies, push
`exp(-b c)` into the sum, merge the exponentials, then compare the sums term by term.

**R1 · `simp only [mathematicalPartitionFunctionBetaReal]`** changes the **goal**: every `Z(b)` becomes its
defining sum. Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓔.mathematicalPartitionFunctionBetaReal b)` | `⊢ P (∑ i, rexp (-b * 𝓔.energy i))` |

**R2 · `simp only [D]` for a structure update** changes the **goal**. `D` is a definition whose body is
`{ 𝓔 with energy := …, energy_measurable := … }`; `simp only [D]` unfolds it and evaluates the projection
`.energy`, leaving the new value. In the guide `D` is `double`, with `energy := fun i => 2 * 𝓔.energy i`.
Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P ((double 𝓔).energy i)` | `⊢ P (2 * 𝓔.energy i)` |

**R3 · `rw [Finset.mul_sum]`** changes the **goal**. The lemma is
`Finset.mul_sum s f a : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`: a constant factor moves into the sum.
Placeholders: `{ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ)`; in Mathlib it holds in any
`[NonUnitalNonAssocSemiring R]` (`ℕ`, `ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R4 · `simp only [← Real.exp_add]`** changes the **goal**. The lemma is
`Real.exp_add x y : rexp (x + y) = rexp x * rexp y`; `←` uses it right to left, merging a product of
exponentials. Inside `∑ i, …` use `simp only`, not `rw`: `rw [← Real.exp_add]` fails with "did not find an
occurrence of the pattern" because the product mentions the bound variable `i`. Placeholders:
`{ι : Type} [Fintype ι] (u v : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, rexp (u i) * rexp (v i))` | `⊢ P (∑ x, rexp (u x + v x))` |

**R5 · `congr 1`** changes the **goal**: an equation of two sums over the same index set becomes an equation of
their summand functions (named `case e_f`). Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℝ)`. If a
hypothesis already proves the new goal, `congr 1` closes it by itself.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `⊢ f = g` |

**R6 · `funext i`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `{ι : Type} (f g : ι → ℝ)`. On `(fun x => …) = fun x => …` it also substitutes `i`.

| Before | After |
|---|---|
| `⊢ f = g` | `i : ι ⊢ f i = g i` |

**R7 · `ring_nf`** **closes** `rexp u = rexp v` when `u` and `v` are equal polynomials. It normalises every
subterm, including the arguments of `rexp`, and then both sides are the same term. `ring` fails here: it treats
`rexp (…)` as an unknown and does not look inside. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp (x * (y + 1)) = rexp (x + x * y)` | no goals |

**W1: doubling every energy doubles `b`.** R1 and R2 together (`simp only [mathematicalPartitionFunctionBetaReal, double]`),
then R5, R6, R7:

```lean-goal
⊢ (double 𝓔).mathematicalPartitionFunctionBetaReal b = 𝓔.mathematicalPartitionFunctionBetaReal (2 * b)
⊢ ∑ x, rexp (-b * (2 * 𝓔.energy x)) = ∑ i, rexp (-(2 * b) * 𝓔.energy i)
⊢ (fun x => rexp (-b * (2 * 𝓔.energy x))) = fun i => rexp (-(2 * b) * 𝓔.energy i)
⊢ rexp (-b * (2 * 𝓔.energy i)) = rexp (-(2 * b) * 𝓔.energy i)
```

---

## Part 2 · `shift_probability`

Statement: `(shift 𝓒 c).probabilityBetaReal b = 𝓒.probabilityBetaReal b`, an equation of functions `ι → ℝ`.
Go pointwise (R6), unfold both probabilities, replace `Z_shift` by Part 1, then split `exp(-b(E + c))` and
cancel the common factor `exp(-b c)`.

**R8 · `rw [probabilityBetaReal]`** changes the **goal**: one `p_b(i)` becomes `rexp (-b * E i) / Z(b)`. `rw`
fixes the ensemble at the first match, so it unfolds only that ensemble's probabilities; a second
`rw [probabilityBetaReal]` unfolds the other side. In between you can `rw [shift_Z]` (Part 1 is now a lemma).
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 𝓕 : CanonicalEnsemble ι) (b : ℝ) (i : ι)`,
`P : ℝ → ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P (𝓔.probabilityBetaReal b i) (𝓕.probabilityBetaReal b i)` | `⊢ P (rexp (-b * 𝓔.energy i) / 𝓔.mathematicalPartitionFunctionBetaReal b) (𝓕.probabilityBetaReal b i)` |

**R9 · `have hE : (D 𝓔).energy i = … := rfl`** changes the **context**. A field of a structure update equals the
new value by definition, so `rfl` proves it; then `rw [hE]` replaces the field in the goal (R2 does the same
with `simp only`). Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (i : ι) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hE : (double 𝓔).energy i = 2 * 𝓔.energy i ⊢ G` |

**R10 · `rw [show u = v by ring]`** changes the **goal**. `show u = v by ring` is a term: the equation `u = v`
together with its proof by `ring`. Use it to put an argument into the exact shape the next lemma needs (here:
`-b * (E + c)` into a sum `x + y` for R11). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x * (y + 1))` | `⊢ P (x * y + x)` |

**R11 · `rw [Real.exp_add]`** changes the **goal**: `rexp (x + y) = rexp x * rexp y`, left to right (R4 is the
other direction). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp (x + y))` | `⊢ P (rexp x * rexp y)` |

**R12 · `rw [mul_div_mul_left a b hc]`** changes the **goal**. The lemma is
`mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b`: cancel a common left factor. Write `_ _`
for `a b` to let `rw` find them. Placeholders: `{G₀ : Type} [CommGroupWithZero G₀] (a b c : G₀) (hc : c ≠ 0)`;
a *commutative group with zero* has `*`, `/` and inverses of nonzero elements: `ℝ`, `ℚ`, `ℂ` qualify.

| Before | After |
|---|---|
| `⊢ P (c * a / (c * b))` | `⊢ P (a / b)` |

**R13 · `(Real.exp_pos x).ne'`** **closes** `rexp x ≠ 0`. `Real.exp_pos x : 0 < rexp x`, and for `h : a < b`,
`h.ne' : b ≠ a` (`LT.lt.ne'`). It is the `hc` argument of R12. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp x ≠ 0` | no goals |

**W3: cancelling an exponential factor.** R11, then R12 with R13 as its argument:

```lean-goal
⊢ rexp (x + y) / (rexp x * z) = rexp y / z
⊢ rexp x * rexp y / (rexp x * z) = rexp y / z
```

---

## Part 3 · `shift_meanEnergy`

Statement: `U_shift(b) = U(b) + c`. First prove the normalisation `∑ i, p_b(i) = 1` for `𝓒` (it needs `Z(b) > 0`).
Then unfold `U`, replace the shifted probabilities by Part 2, unfold the shifted energies, and split
`∑ (E i + c) p i = ∑ E i p i + c ∑ p i`.

**R14 · `have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b`** changes the **context**: it adds `Z(b) > 0`.
The lemma needs `[Nonempty ι]`. Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι]
(𝓔 : CanonicalEnsemble ι) (b : ℝ) (G : Prop)`. `hZ.ne'` is then `Z(b) ≠ 0` (R13).

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓔.mathematicalPartitionFunctionBetaReal b ⊢ G` |

**R15 · `simp only [probabilityBetaReal]`** changes the **goal**: unlike `rw` (R8), it unfolds every `p_b(i)`,
also under `∑`. Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, 𝓔.probabilityBetaReal b i)` | `⊢ P (∑ x, rexp (-b * 𝓔.energy x) / 𝓔.mathematicalPartitionFunctionBetaReal b)` |

**R16 · `rw [← Finset.sum_div]`** changes the **goal**. The lemma is
`Finset.sum_div s f a : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; right to left it pulls a common divisor out.
Placeholders: `{ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ)`; in Mathlib any `[DivisionSemiring K]` (`ℚ`, `ℝ`, `ℂ`).
After R1 the numerator `∑ i, rexp (-b * E i)` is literally `Z(b)`, by definition, so R17 applies.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R17 · `exact div_self ha`** **closes** `a / a = 1`. The lemma is `div_self : a ≠ 0 → a / a = 1`. Placeholders:
`(a : ℝ) (ha : a ≠ 0)`. The two sides of `/` only need to agree by definition, not literally.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a / a = 1` | no goals |

**W2: normalised weights sum to one.** R16, then R17 with `hpos.ne'`:

```lean-goal
⊢ ∑ i, f i / ∑ j, f j = 1
⊢ (∑ i, f i) / ∑ j, f j = 1
```

**R18 · `simp only [meanEnergyBetaReal]`** changes the **goal**: every `U(b)` becomes `∑ i, E i * p_b(i)`.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓔.meanEnergyBetaReal b)` | `⊢ P (∑ i, 𝓔.energy i * 𝓔.probabilityBetaReal b i)` |

**R19 · `simp only [hF]` with `hF : F = G` between functions** changes the **goal**: every application `F x`
becomes `G x`, also under `∑`. Part 2 is such an equation (`F` = the shifted `probabilityBetaReal b`).
Placeholders: `{ι : Type} [Fintype ι] (F G w : ι → ℝ) (hF : F = G)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, w i * F i)` | `⊢ P (∑ x, w x * G x)` |

**R20 · `simp only [add_mul]`** changes the **goal**: `add_mul a b c : (a + b) * c = a * c + b * c`, applied
to every summand. As in R4, `rw [add_mul]` fails under `∑ i, …` when the product mentions `i`. Placeholders:
`{ι : Type} [Fintype ι] (f g w : ι → ℝ)`; `add_mul` holds in any type with `*`, `+` and right distributivity
(`ℕ`, `ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i) * w i)` | `⊢ P (∑ x, (f x * w x + g x * w x))` |

**R21 · `rw [Finset.sum_add_distrib]`** changes the **goal**: the sum of a sum splits,
`∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`. Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℝ)`;
in Mathlib any `[AddCommMonoid M]`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R22 · `rw [← Finset.mul_sum]`** changes the **goal**: R3 right to left, a constant factor moves out of the sum.
Placeholders: `{ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R23 · `rw [mul_one]`** changes the **goal**: `mul_one a : a * 1 = a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**W4: a weighted average of `f + c`.** With `hw : ∑ i, w i = 1`, the single call
`simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hw, mul_one]` (R20, R21, R22, `hw`, R23) closes

```lean-goal
⊢ ∑ i, (f i + c) * w i = ∑ i, f i * w i + c
```

---

## Traps

- `ring` cannot prove `rexp (-b * (E + c)) = rexp (-b * c + -b * E)`: it does not look inside `rexp`. Use
  `ring_nf` (R7), or rewrite the argument first with `rw [show … by ring]` (R10).
- `rw [probabilityBetaReal]` unfolds only one ensemble's probabilities (R8). If the goal still shows
  `probabilityBetaReal`, `rw` again, or use `simp only` (R15).
- `rw [Real.exp_add]` needs the argument to be literally a sum `x + y`. `-b * (E + c)` is a product: reshape it
  with R10 first.
- `mathematicalPartitionFunctionBetaReal_pos` needs `[Nonempty ι]`; `shift_Z` does not have it, but
  `shift_probability` and `shift_meanEnergy` do.
- `simp only [shift]` unfolds `shift` everywhere it appears. Do it in a later call than
  `simp only [shift_probability]` (R19), not in the same list: once `shift` is unfolded, the left side of
  `shift_probability` no longer appears literally, and the goal shows `{ energy := …, … }.probabilityBetaReal b x`.
- `rw` does not rewrite under `∑ i, …` when the pattern mentions `i` (R4, R20): use `simp only [lemma]` there.
  After `funext i` (R6) `i` is a free variable, and `rw` works again (R10, R11, R12).
- The normalisation `∑ i, p_b(i) = 1` is not a physlib lemma for `probabilityBetaReal`: prove it with `have`
  (R15 → R16 → R17).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `Z(b)`, `p_b(i)`, `U(b)` | `simp only [mathematicalPartitionFunctionBetaReal]`, `[probabilityBetaReal]`, `[meanEnergyBetaReal]` | R1, R15, R18 |
| unfold one side's `p_b(i)` | `rw [probabilityBetaReal]` | R8 |
| unfold a structure update's field | `simp only [shift]` / `have hE : … := rfl` | R2, R9 |
| `a * ∑ f` ↔ `∑ a * f` | `Finset.mul_sum` / `← Finset.mul_sum` | R3, R22 |
| `exp x * exp y` ↔ `exp (x + y)` | `simp only [← Real.exp_add]` (under `∑`) / `rw [Real.exp_add]` | R4, R11 |
| sums equal termwise | `congr 1; funext i` | R5, R6 |
| `exp` arguments equal as polynomials | `ring_nf` | R7 |
| reshape a subterm | `rw [show u = v by ring]` | R10 |
| cancel `c * a / (c * b)` | `rw [mul_div_mul_left _ _ hc]` | R12 |
| `exp x ≠ 0` | `(Real.exp_pos x).ne'` | R13 |
| `Z(b) > 0` | `𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R14 |
| `∑ f / a` → `(∑ f) / a`, then `a / a = 1` | `rw [← Finset.sum_div]`; `div_self h.ne'` | R16, R17 |
| use an equation of functions under `∑` | `simp only [hF]` | R19 |
| split `∑ (E + c) * p` | `simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]` | R20–R22 |
| `a * 1` | `mul_one` | R23 |
| use an earlier theorem | `rw [shift_Z]`, `simp only [shift_probability]` | TACTIC_STATES |
| see the state | infoview | |
