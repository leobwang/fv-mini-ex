# M160 · Mean energy from log Z: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` and its
finite-system quantities as functions of the inverse temperature `b` (with `k_B = 1`): the partition
function `Z(b)`, the Boltzmann probabilities `p_b(i)` and the mean energy `U(b)`; Mathlib's derivative
predicate `HasDerivAt` and its calculus rules (sum, negation, constant factor, `exp`, `log`); Mathlib's
finite sums `∑` and their algebra; `Real.exp`, `Real.log`.

The physics: with energies `Eᵢ`, `Z(b) = ∑ᵢ exp(-b Eᵢ)`, `p_b(i) = exp(-b Eᵢ) / Z(b)`,
`U(b) = ∑ᵢ Eᵢ p_b(i)`. Differentiating term by term, `Z'(b) = -∑ᵢ Eᵢ exp(-b Eᵢ)`; the chain rule gives
`(log Z)'(b) = Z'(b) / Z(b)`, and pulling `/ Z(b)` into the sum turns that into `-∑ᵢ Eᵢ p_b(i) = -U(b)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`/`refine`, or one lemma used with dot
notation to build a new fact (`hf.exp`). It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a context entry leaves alone.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓔 : CanonicalEnsemble ι` is any ensemble; the guide never differentiates the exercise's `log Z`.
- **Dot notation:** for `hf : HasDerivAt f f' x`, `hf.exp` means `HasDerivAt.exp hf`. Calls chain left to
  right: `((hasDerivAt_id' x).neg.mul_const c).exp` applies R7, then R8, then R9 to R6.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `HasDerivAt f f' x` | Mathlib: `f : ℝ → ℝ` is differentiable at the point `x` and its derivative there is the number `f'`. A `Prop`, so the derivative is *claimed*, and must match exactly (R10 relaxes that) |
| `HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal d b` | `Z'(b) = d`, about the function `Z` (no argument after the name) |
| `fun x => Real.log (Z x)` | the function `x ↦ log Z(x)` |
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`. Its field `energy : ι → ℝ` gives each microstate's energy; other fields (`dof`, the measure `μ`, …) do not matter here |
| `[MeasurableSpace ι]` | `ι` carries a σ-algebra (needed by the structure; ignore it) |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[Nonempty ι]` | `ι` has at least one element (so `Z(b) > 0`, R1) |
| `𝓒.energy i` | `Eᵢ`, the energy of microstate `i` |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, rexp (-b * 𝓒.energy i)` (R2) |
| `𝓒.probabilityBetaReal b i` | `p_b(i) = rexp (-b * 𝓒.energy i) / Z(b)` (R15) |
| `𝓒.meanEnergyBetaReal b` | `U(b) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal b i` (R14) |
| `rexp x`, `log x` | `Real.exp x`, `Real.log x` (`open Real` lets you write `log`) |
| `-b * E` | `(-b) * E`: unary minus binds tighter than `*` |
| `Finset.univ` | Mathlib: the finite set of all elements of a `[Fintype ι]` |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over all elements of the finite type |
| `∑ x, …` | the same sum; `rw`/`simp` rename the bound variable to `x` |
| `∀ i ∈ Finset.univ, Q i` | `∀ i, i ∈ Finset.univ → Q i` (two binders, R5) |
| `a✝ : i ∈ Finset.univ` | an inaccessible hypothesis, from `intro i _` |
| `-f`, `(-fun x => x) y` | the function `y ↦ -f y`; applied to `y`, it is `-y` by definition, but only `simp` (R11) shows it |

---

## Part 1 · `meanEnergy_eq_neg_dlogZ`

Statement: for a finite, nonempty system `𝓒` and any `b : ℝ`, the function `x ↦ log Z(x)` has derivative
`-U(b)` at `b`. Prove the milestone `hd : Z'(b) = -∑ i, Eᵢ exp(-b Eᵢ)` first (R2–R11), then apply the chain
rule for `log` (R12, R13) and turn the ratio into `-U(b)` (R14–R18).

### The partition function

**R1 · `have hZ := 𝓔.mathematicalPartitionFunctionBetaReal_pos b`** changes the **context**: it adds `0 < Z(b)`.
The lemma needs `[Nonempty ι]`. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓔.mathematicalPartitionFunctionBetaReal b ⊢ G` |

**R2 · `unfold mathematicalPartitionFunctionBetaReal`** changes the **goal**: the bare function name `Z` becomes
`fun b => ∑ i, rexp (-b * 𝓔.energy i)`. Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι]
(𝓔 : CanonicalEnsemble ι)`, `P : (ℝ → ℝ) → Prop` (the rest of the goal takes a function).

| Before | After |
|---|---|
| `⊢ P 𝓔.mathematicalPartitionFunctionBetaReal` | `⊢ P fun b => ∑ i, rexp (-b * 𝓔.energy i)` |

### Differentiating a finite sum term by term

**R3 · `rw [← Finset.sum_neg_distrib]`** changes the **goal**. The lemma is
`Finset.sum_neg_distrib f : ∑ x ∈ s, -f x = -∑ x ∈ s, f x`; right to left it moves a minus sign into the sum,
so the claimed derivative becomes a sum, as R4 needs. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ)`; it
holds in any `[SubtractionCommMonoid G]` (`ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (-∑ i, f i)` | `⊢ P (∑ x, -f x)` |

**R4 · `apply HasDerivAt.fun_sum`** changes the **goal**: the derivative of a finite sum is the sum of the
derivatives. The lemma is `(∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y => ∑ i ∈ u, A i y)
(∑ i ∈ u, A' i) x`. Placeholders: `{ι : Type} [Fintype ι] (A : ι → ℝ → ℝ) (A' : ι → ℝ) (x : ℝ)`: `A i` is the
`i`-th term as a function, `A' i` its claimed derivative.

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun y => ∑ i, A i y) (∑ i, A' i) x` | `⊢ ∀ i ∈ Finset.univ, HasDerivAt (A i) (A' i) x` |

**R5 · `intro i _`** changes the **goal and the context**: `∀ i ∈ s, Q i` has two binders (`i` and `i ∈ s`),
so `intro` takes two names; `_` leaves the membership proof unnamed. Placeholders: `(Q : ι → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ i ∈ Finset.univ, Q i` | `i : ι, a✝ : i ∈ Finset.univ ⊢ Q i` |

**R6 · `hasDerivAt_id' x`** is the fact `HasDerivAt (fun x => x) 1 x`: the identity has derivative `1`. Used with
`have`, it changes the **context**. Placeholders: `(x : ℝ)`. Start every chain from it.

| Before | After |
|---|---|
| `⊢ G` | `h1 : HasDerivAt (fun x => x) 1 x ⊢ G` |

**R7 · `hf.neg`** (`HasDerivAt.neg`) builds `HasDerivAt (-f) (-f') x` from `hf : HasDerivAt f f' x`; with `have`
it changes the **context**. Placeholders: `(f : ℝ → ℝ) (f' x : ℝ)`. `-f` is the function `y ↦ -f y`, so
`(hasDerivAt_id' x).neg` is about `-fun x => x` with derivative `-1`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h2 : HasDerivAt (-f) (-f') x ⊢ G` |

**R8 · `hf.mul_const c`** (`HasDerivAt.mul_const`) builds `HasDerivAt (fun y => f y * c) (f' * c) x`: a constant
factor on the right. Changes the **context** with `have`. Placeholders: `(f : ℝ → ℝ) (f' x c : ℝ)`. This is why
the exponent `-b * E` (that is, `(-b) * E`) is built as `(-id) * E`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h2 : HasDerivAt (fun y => f y * c) (f' * c) x ⊢ G` |

**R9 · `hf.exp`** (`HasDerivAt.exp`) is the chain rule for `exp`: from `hf : HasDerivAt f f' x` it builds
`HasDerivAt (fun x => rexp (f x)) (rexp (f x) * f') x`. Changes the **context** with `have`. Placeholders:
`(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ G` | `h2 : HasDerivAt (fun x => rexp (f x)) (rexp (f x) * f') x ⊢ G` |

**R10 · `refine hf.congr_deriv ?_`** (`HasDerivAt.congr_deriv`) changes the **goal**: a `HasDerivAt` goal whose
function matches `hf`'s becomes an equation between the two derivatives. The lemma is
`HasDerivAt f f' x → f' = g' → HasDerivAt f g' x`. The functions only need to agree up to unfolding:
`fun y => rexp ((-fun x => x) y * c)` matches `fun y => rexp (-y * c)`. Placeholders:
`(f : ℝ → ℝ) (f' g' x : ℝ)`. Term form: `hf.congr_deriv (by tac)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x ⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

**R11 · `simp`** on the derivative equation changes the **goal**: `(-fun x => x) y` becomes `-y`
(`Pi.neg_apply`), and `simp` also normalises signs (`-y * c` to `-(y * c)`, `-1 * c` to `-c`, cancels a minus
on both sides). `ring` cannot do this step: it treats `(-fun x => x) y` as an unknown different from `-y`.
Placeholders: `(y c : ℝ)`. Finish with `ring` (TACTIC_STATES).

| Before | After |
|---|---|
| `⊢ P ((-fun x => x) y * c)` | `⊢ P (-(y * c))` |

**W1: one exponential, the whole chain.** For `fun y => rexp (-y * 3)`, the term
`((hasDerivAt_id' x).neg.mul_const 3).exp` (R6 → R7 → R8 → R9), matched by R10, leaves the first line;
R11 gives the second; `ring` closes it:

```lean-goal
⊢ rexp ((-fun x => x) x * 3) * (-1 * 3) = -(3 * rexp (-x * 3))
⊢ rexp (-(x * 3)) * 3 = 3 * rexp (-(x * 3))
```

**W2: a sum, positive exponents.** R4 then R5 on `fun y => ∑ i, rexp (y * a i)` leave one term:

```lean-goal
⊢ ∀ i ∈ Finset.univ, HasDerivAt (fun y => rexp (y * a i)) (a i * rexp (x * a i)) x
⊢ HasDerivAt (fun y => rexp (y * a i)) (a i * rexp (x * a i)) x
```

and `(((hasDerivAt_id' x).mul_const (a i)).exp).congr_deriv (by ring)` closes it (no `-`, so no R11).

### The chain rule for `log`

**R12 · `hf.log hne`** (`HasDerivAt.log`) builds `HasDerivAt (fun y => log (f y)) (f' / f x) x` from
`hf : HasDerivAt f f' x` and `hne : f x ≠ 0`. Changes the **context** with `have`. Placeholders:
`(f : ℝ → ℝ) (f' x : ℝ)`.

| Before | After |
|---|---|
| `hf : HasDerivAt f f' x, hne : f x ≠ 0 ⊢ G` | `h2 : HasDerivAt (fun y => log (f y)) (f' / f x) x ⊢ G` |

**R13 · `hpos.ne'`** (`LT.lt.ne'`) turns `hpos : 0 < a` into `a ≠ 0`; `hpos.ne` would give `0 ≠ a`, the wrong
way round for R12. Changes the **context** with `have`. Placeholders: `(a : ℝ)`; it works in any order.

| Before | After |
|---|---|
| `hpos : 0 < a ⊢ G` | `hne : a ≠ 0 ⊢ G` |

**W3.** `refine (hf.log hpos.ne').congr_deriv ?_` (R12, R13, R10) on a goal claiming the derivative
`f' * (f x)⁻¹` leaves the equation of derivatives, closed by `ring`:

```lean-goal
⊢ f' / f x = f' * (f x)⁻¹
```

### The ratio is `-U(b)`

**R14 · `simp only [meanEnergyBetaReal]`** changes the **goal**: `U(b)` becomes its defining sum. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓔 : CanonicalEnsemble ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓔.meanEnergyBetaReal b)` | `⊢ P (∑ i, 𝓔.energy i * 𝓔.probabilityBetaReal b i)` |

**R15 · `simp only [probabilityBetaReal]`** changes the **goal**: every `p_b(i)` becomes
`rexp (-b * E i) / Z(b)`, also under `∑`. Placeholders: as R14, plus `(w : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, w i * 𝓔.probabilityBetaReal b i)` | `⊢ P (∑ x, w x * (rexp (-b * 𝓔.energy x) / 𝓔.mathematicalPartitionFunctionBetaReal b))` |

**R16 · `simp only [← mul_div_assoc]`** changes the **goal**. The lemma is `mul_div_assoc a b c : a * b / c = a * (b / c)`
(`a * b / c` is `(a * b) / c`); right to left it pulls the division outward. With `simp only` it works under `∑`.
Placeholders: `(a b c : ℝ)`; it holds in any `[DivInvMonoid G]` (`ℚ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (a * (b / c))` | `⊢ P (a * b / c)` |

**R17 · `simp only [← Finset.sum_div]`** changes the **goal**. The lemma is
`Finset.sum_div s f a : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; right to left a common denominator leaves the sum.
Placeholders: `{ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ)`; it holds in any `[DivisionSemiring K]` (`ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R18 · `ring`** **closes** a field identity in which `/ c` is read as `* c⁻¹` with `c` an unknown, such as
`-s / c = -(s / c)`. No `c ≠ 0` is needed. A sum `∑ …` and `Z(b)` are unknowns too. (TACTIC_STATES says `ring`
fails on `⁻¹` of variables; it does not, as long as no cancellation `c / c = 1` is needed.)

**W4: a common denominator out of a weighted sum.** R16 rewrites the right side; R17 then makes both sides equal:

```lean-goal
⊢ (∑ i, a i * w i) / s = ∑ i, a i * (w i / s)
⊢ (∑ i, a i * w i) / s = ∑ x, a x * w x / s
```

---

## Traps

- `simp only [mathematicalPartitionFunctionBetaReal]` makes no progress on the bare `Z` in `HasDerivAt Z …`: its
  equation is about `Z b` applied. Use `unfold` (R2).
- `apply HasDerivAt.fun_sum` fails while the claimed derivative is `-∑ …`: it is not syntactically a sum. Move the
  minus inside first (R3).
- `ring` alone fails on the per-term side goal: `(-fun x => x) b` is an unknown to it. `simp` first (R11).
- Use `congr_deriv` (R10), not `convert … using 1`: `convert` also compares the hidden type-class arguments and
  leaves an instance-equality side goal.
- `hZ.ne'`, not `hZ.ne` (R13): `log` needs `Z b ≠ 0`.
- `hd` is about the function `Z`, so state it with the bare name (`HasDerivAt 𝓒.mathematicalPartitionFunctionBetaReal …`);
  then `hd.log` produces exactly the function `fun y => log (Z y)` of the goal.
- In `have hd : T := by`, indent the proof further than `have`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < Z(b)` | `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R1 |
| unfold the bare function `Z` | `unfold mathematicalPartitionFunctionBetaReal` | R2 |
| `-∑ f → ∑ -f` | `rw [← Finset.sum_neg_distrib]` | R3 |
| derivative of a sum → each term | `apply HasDerivAt.fun_sum` then `intro i _` | R4, R5 |
| derivative of `y ↦ rexp (-y * c)` | `((hasDerivAt_id' b).neg.mul_const c).exp` | R6 → R7 → R8 → R9 |
| built derivative ≠ claimed one | `refine h.congr_deriv ?_` / `h.congr_deriv (by simp; ring)` | R10, R11 |
| `(-fun x => x) y → -y` | `simp` | R11 |
| derivative of `y ↦ log (f y)` | `hf.log hne` with `hne := hpos.ne'` | R12, R13 |
| unfold `U`, `p` | `simp only [meanEnergyBetaReal, probabilityBetaReal]` | R14, R15 |
| `a * (b / c) → a * b / c`, `∑ f / a → (∑ f) / a` | `simp only [← mul_div_assoc, ← Finset.sum_div]` | R16, R17 |
| `-s / c = -(s / c)` | `ring` | R18 |
| see the state | infoview | |
