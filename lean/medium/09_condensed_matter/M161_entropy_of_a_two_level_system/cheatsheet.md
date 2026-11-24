# M161 · Entropy of a two-level system: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` (a statistical
system with microstates `ι`), its temperature type `Temperature`, the Boltzmann probabilities, the partition
function and the two entropies (thermodynamic and Shannon); the two-level system `twoState E₀ E₁`; Mathlib's
`Real.exp`, `Real.log`, finite sums `∑`, and the tactics `generalize`, `positivity`, `linear_combination`,
`field_simp`.

The physics: a system with energies `Eᵢ` at temperature `T` has inverse temperature `β = 1 / (k_B T)`
(`k_B` the Boltzmann constant), Boltzmann weights `e^{-βEᵢ}`, partition function `Z = ∑ᵢ e^{-βEᵢ}` and
probabilities `pᵢ = e^{-βEᵢ} / Z`. For a finite system the entropy is the Shannon entropy
`S = -k_B ∑ᵢ pᵢ log pᵢ`. For `E₀ = 0`, `E₁ = ε`, write `x = βε` and `D = 1 + e^{-x}`: then `p₀ = 1/D`,
`p₁ = e^{-x}/D`, `log p₀ = -log D`, `log p₁ = -x - log D`, and
`S/k_B = (1/D) log D + (e^{-x}/D)(x + log D) = log D + x e^{-x}/D = log D + x/(e^{x} + 1)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : ℝ → ℝ → Prop` when two places matter). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓒 : CanonicalEnsemble ι` is any ensemble; `T : Temperature` any temperature. The guide never uses the
  exercise's `twoState 0 ε`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`. Its field `energy : ι → ℝ` gives each microstate's energy; the other fields (`dof`, `μ`, …) do not matter here |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]` | `ι` carries a σ-algebra in which single points are measurable; `Fin 2` has both. Ignore them |
| `[𝓒.IsFinite]` | `𝓒` is a finite system in physlib's sense: counting measure, no continuous degrees of freedom. `twoState E₀ E₁` has this instance |
| `twoState E₀ E₁` | the ensemble on `Fin 2 = {0, 1}` with `energy 0 = E₀`, `energy 1 = E₁` (R6) |
| `T : Temperature` | a temperature: a non-negative real `T.val` wrapped in a structure |
| `T.β`, `↑T.β` | `β = 1 / (kB * T)`, a non-negative real `ℝ≥0` (`NNReal`); `↑` casts it into `ℝ` |
| typing `↑T.β` yourself | write `(T.β : ℝ)` (or `↑T.β`) in a `have`, `show` or `generalize`; Lean prints both as `↑T.β`. `rexp` can be typed too (it is `Real.exp`, available after `open Real`) |
| `kB` | `Constants.kB`, Boltzmann's constant, a real number |
| `𝓒.thermodynamicEntropy T` | physlib's general entropy `S(T)`; for finite systems it equals the Shannon entropy (R1) |
| `𝓒.shannonEntropy T` | `-kB * ∑ i, p i * log (p i)` (R2) |
| `𝓒.probability T i` | `p i = rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T` (R3) |
| `𝓒.mathematicalPartitionFunction T` | `Z(T)`; for a finite system `∑ i, rexp (-↑T.β * 𝓒.energy i)` (R4) |
| `rexp x`, `log x` | `Real.exp x` and `Real.log x` (natural log; Mathlib sets `log 0 = 0` and `log (-x) = log x`) |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over all elements of the finite type |
| `-a * b` vs `-(a * b)` | different terms: `(-a) * b` and the negation of `a * b` (R7, R9) |

---

## Part 1 · `twoState_entropy`

Statement: `S(T) = kB * (log (1 + e^{-βε}) + βε / (e^{βε} + 1))` for `twoState 0 ε`. Switch to the Shannon
formula, compute both probabilities as `have` facts, rewrite with them, replace `βε` by one variable `x`, then
split the logarithms and do the algebra.

### Switching to the finite formula

**R1 · `rw [thermodynamicEntropy_eq_shannonEntropy]`** changes the **goal**: the thermodynamic entropy of a finite
ensemble is its Shannon entropy. Statement: `𝓒.thermodynamicEntropy T = 𝓒.shannonEntropy T`. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite]
(T : Temperature)`; `twoState E₀ E₁` on `Fin 2` meets every bracket.

| Before | After |
|---|---|
| `⊢ P (𝓒.thermodynamicEntropy T)` | `⊢ P (𝓒.shannonEntropy T)` |

**R2 · `rw [shannonEntropy]`** changes the **goal**: unfolds the definition. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.shannonEntropy T)` | `⊢ P (-kB * ∑ i, 𝓒.probability T i * log (𝓒.probability T i))` |

### Computing the probabilities

Each probability is one `have hp : (…).probability T i = … := by simp [probability,
mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]`. That `simp` call performs R3–R8 by itself
(R6–R8 are simp lemmas it knows without being told). The entries show what each piece does.

**R3 · `rw [probability]`** changes the **goal**: one Boltzmann probability becomes weight over partition
function. Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probability T i)` | `⊢ P (rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T)` |

**R4 · `rw [mathematicalPartitionFunction_of_fintype]`** changes the **goal**: for a finite ensemble `Z(T)`
is the sum of the Boltzmann weights. Statement: `𝓒.mathematicalPartitionFunction T = ∑ i, rexp (-↑T.β * 𝓒.energy i)`.
Placeholders: as R1.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunction T)` | `⊢ P (∑ i, rexp (-↑T.β * 𝓒.energy i))` |

**R5 · `rw [Fin.sum_univ_two]`** changes the **goal**: `∑ i : Fin 2, f i = f 0 + f 1`. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`; `ℝ` is an `AddCommMonoid` (it has `+` and `0`). You also need it
on the entropy sum itself, before `rw [hp0, hp1]`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R6 · `twoState_energy_fst`, `twoState_energy_snd`** change the **goal**: `(twoState E₀ E₁).energy 0 = E₀` and
`(twoState E₀ E₁).energy 1 = E₁`. Both are `@[simp]`. Placeholders: `(E₀ E₁ : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((twoState E₀ E₁).energy 0) ((twoState E₀ E₁).energy 1)` | `⊢ P E₀ E₁` |

**R7 · `neg_mul`** changes the **goal**: `-a * b = -(a * b)`. `simp` always uses it left to right, so after
`simp` every `-↑T.β * ε` reads `-(↑T.β * ε)`. Placeholders: `(a b : ℝ)`; any ring.

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

**R8 · `mul_zero`, `Real.exp_zero`** change the **goal**: `a * 0 = 0` and `rexp 0 = 1`; the weight of the
zero-energy level is `1`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp (-a * 0))` | `⊢ P 1` |

With R3–R8, `p 0 = rexp (-↑T.β * 0) / (rexp (-↑T.β * 0) + rexp (-↑T.β * ε))` becomes
`1 / (1 + rexp (-(↑T.β * ε)))`. Write the right side of each `have` in exactly this simp form.

**W1: the probability of state 0 in any 2-state finite ensemble.** R3, R4, R5 on a generic
`𝓔 : CanonicalEnsemble (Fin 2)` (the last `rw` closes the goal by `rfl`):

```lean-goal
⊢ 𝓔.probability T 0 = rexp (-↑T.β * 𝓔.energy 0) / (rexp (-↑T.β * 𝓔.energy 0) + rexp (-↑T.β * 𝓔.energy 1))
```

### One variable for `βε`

**R9 · `rw [show u = v by ring]`** changes the **goal**: `show u = v by ring` is the equation together with its
proof, and `rw` replaces every literal `u` by `v`. Here it turns the spec's `-↑T.β * ε` into simp's
`-(↑T.β * ε)`, so that all occurrences look alike. Placeholders: `(a b : ℝ)`. A plain `rw [neg_mul]` is not
enough: it rewrites the first match, which is `-kB * (…)`, not `-↑T.β * ε`.

| Before | After |
|---|---|
| `⊢ P (-a * b) (-(a * b))` | `⊢ P (-(a * b)) (-(a * b))` |

**R10 · `generalize e = x`** changes the **goal and the context**: every occurrence of the term `e` in the goal
becomes a new variable `x : ℝ`, about which nothing is known. Afterwards the goal is an identity in `x` alone,
which is what `ring` and `field_simp` handle best. Placeholders: `(a b : ℝ)`, `e = a * b`. `-a * b` is `(-a) * b` and does
not contain `a * b`, so it is not replaced: do R9 first.

| Before | After |
|---|---|
| `⊢ P (a * b) (-(a * b))` | `x : ℝ ⊢ P x (-x)` |

### Logarithms of quotients

**R11 · `positivity`** **closes** goals `0 < e`, `0 ≤ e` and `e ≠ 0` when `e` is built from positive pieces
(`rexp _ > 0`, numerals, `+`, `*`, `/`). Use it as `have hD : 0 < 1 + rexp (-x) := by positivity` and inside
side conditions: `(by positivity)`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < 1 + rexp (-x)` | no goals |

**R12 · `hD.ne'`** gives `D ≠ 0` from `hD : 0 < D` (the lemma `LT.lt.ne' : a < b → b ≠ a`), as a term to pass
to lemmas such as R13 and R17. With `have` it changes the **context**. Placeholders: `(D : ℝ) (hD : 0 < D)`.

| Before | After |
|---|---|
| `⊢ G` | `hD0 : D ≠ 0 ⊢ G` |

**R13 · `rw [Real.log_div hx hy]`** changes the **goal**. Statement:
`Real.log_div : x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y`. Placeholders: `(x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`.
For `log (1 / D)` pass `(by norm_num)` for `1 ≠ 0`; for `log (rexp (-x) / D)` pass `(by positivity)`.

| Before | After |
|---|---|
| `⊢ P (log (x / y))` | `⊢ P (log x - log y)` |

**R14 · `rw [Real.log_one]`** changes the **goal**: `log 1 = 0`.

| Before | After |
|---|---|
| `⊢ P (log 1)` | `⊢ P 0` |

**R15 · `rw [Real.log_exp]`** changes the **goal**: `log (rexp x) = x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (log (rexp x))` | `⊢ P x` |

**W2: a log of a Boltzmann ratio.** R13 with two `(by positivity)` arguments (R11), then R15 (which closes the
goal by `rfl`):

```lean-goal
⊢ log (rexp y / (2 + rexp y)) = y - log (2 + rexp y)
⊢ log (rexp y) - log (2 + rexp y) = y - log (2 + rexp y)
```

### Algebra with exponentials

After R13–R15 the right side still has `x / (rexp x + 1)` while the left side has denominators `1 + rexp (-x)`.
`ring` cannot relate `rexp x` and `rexp (-x)` (to it they are two unknowns), so supply
`he : rexp x * rexp (-x) = 1` and rewrite `x / (rexp x + 1)` into `x * rexp (-x) / (1 + rexp (-x))` by hand.

**R16 · `rw [← Real.exp_add]`** changes the **goal**. Statement: `Real.exp_add x y : rexp (x + y) = rexp x * rexp y`;
`←` merges a product. For `he`, `simp` then closes `rexp (x + -x) = 1` (it knows `x + -x = 0` and `rexp 0 = 1`, R8). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x * rexp y)` | `⊢ P (rexp (x + y))` |

**R17 · `rw [div_eq_div_iff hb hd]`** changes the **goal**: cross-multiply. Statement:
`b ≠ 0 → d ≠ 0 → (a / b = c / d ↔ a * d = c * b)`. Placeholders:
`{G₀ : Type} [CommGroupWithZero G₀] (a b c d : G₀)`; a *commutative group with zero* has `*`, `/` and inverses
of nonzero elements: `ℝ`, `ℚ`, `ℂ` qualify.

| Before | After |
|---|---|
| `⊢ a / b = c / d` | `⊢ a * d = c * b` |

**R18 · `linear_combination k * he`** **closes** `L = R` when `L - R - k * (he.lhs - he.rhs)` is `0` by `ring`.
It is "`ring`, allowed to use an equation `he` scaled by a coefficient `k`". Placeholders: `(u v k : ℝ)`,
`he : u * v = 1`. Find `k` by expanding: which multiple of `rexp x * rexp (-x) - 1` is `L - R`?

| Before | After |
|---|---|
| `⊢ k * u * v = k` | no goals |

**W3: moving `exp` from the denominator to the numerator.** `he` by R16 then `simp`; R17 with two
`(by positivity)`; R18 with `k = -2`:

```lean-goal
⊢ 2 / (rexp y + 1) = 2 * rexp (-y) / (1 + rexp (-y))
⊢ 2 * (1 + rexp (-y)) = 2 * rexp (-y) * (rexp y + 1)
```

**R19 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (it uses
hypotheses such as `hD : 0 < D` from the context, and `positivity`-style facts) and leaves a goal without `/`.
Placeholders: `(a b c D : ℝ) (hD : 0 < D)`. The exact shape it leaves (factor order) is not predictable; finish
with `ring` (R20).

| Before | After |
|---|---|
| `⊢ a / D + b / D = c` | `⊢ a + b = D * c` |

**R20 · `ring`** **closes** commutative-ring identities, treating `rexp (…)` and `log (…)` as unknowns.
Placeholders: `(k L y : ℝ)`.

| Before | After |
|---|---|
| `⊢ -(k * (0 - L + y * (-1 - L))) = k * ((1 + y) * L + y)` | no goals |

**W4: clear a positive denominator, then `ring`.** With `hD : 0 < 2 + rexp y` in the context (R11), R19 leaves

```lean-goal
⊢ k * y * (rexp y + 2) = k * (2 + rexp y) * y
```

and R20 closes it.

---

## Traps

- **`-β * ε` against `-(β * ε)`.** `simp` (R7) writes `-(↑T.β * ε)`, the spec writes `-↑T.β * ε`. Rewrite the
  spec's form into simp's with R9 *before* `generalize`. `-↑T.β * ε` is `(-↑T.β) * ε`, which does not contain
  `↑T.β * ε` at all, so `generalize` leaves it standing next to the new `x`, and the goal is no longer an identity
  in `x` alone.
- **`generalize`, not `set`.** `set x := ↑T.β * ε` introduces `x` as a *local definition* (`x : ℝ := ↑T.β * ε`),
  and `ring` treats `x` and the unfolded `↑T.β * ε` as different atoms if both show up. `generalize` makes `x` a
  genuinely new variable and removes `↑T.β * ε` from the goal.
- `rw [Fin.sum_univ_two]` must come before `rw [hp0, hp1]`: `hp0` mentions `probability T 0`, which does not appear
  literally until the sum over `Fin 2` is split.
- `Real.log_div` needs both side conditions (`1 ≠ 0` and `D ≠ 0`, `rexp (-x) ≠ 0` and `D ≠ 0`). Prove
  `hD : 0 < 1 + rexp (-x)` once and pass `hD.ne'` (R12).
- `ring` does not know `rexp x * rexp (-x) = 1`. Feed it in through `linear_combination` (R18).
- The banned lemmas (`twoState_probability_fst`, …) give the probabilities in `tanh` form; you do not need them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| entropy → `-kB ∑ p log p` | `rw [thermodynamicEntropy_eq_shannonEntropy, shannonEntropy]` | R1, R2 |
| a probability in closed form | `have hp : … := by simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]` | R3–R8 |
| split `∑ i : Fin 2` | `rw [Fin.sum_univ_two]` | R5 |
| make `-a * b` look like `-(a * b)` | `rw [show -a * b = -(a * b) by ring]` | R9, R7 |
| one variable for `βε` | `generalize (T.β : ℝ) * ε = x` | R10 |
| `0 < 1 + rexp (-x)`, `rexp (-x) ≠ 0` | `positivity` | R11 |
| `0 < D` → `D ≠ 0` | `hD.ne'` | R12 |
| `log (a / b)`, `log 1`, `log (rexp x)` | `rw [Real.log_div ha hb, Real.log_one, Real.log_exp]` | R13–R15 |
| `rexp x * rexp (-x) = 1` | `rw [← Real.exp_add]; simp` | R16 |
| cross-multiply `a / b = c / d` | `rw [div_eq_div_iff hb hd]` | R17 |
| ring identity plus one equation | `linear_combination k * he` | R18 |
| clear denominators, finish | `field_simp; ring` | R19, R20 |
| see the state | infoview | |
