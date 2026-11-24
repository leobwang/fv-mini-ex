# M157 · N independent spins: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Temperature` and
`CanonicalEnsemble` (the partition function of a finite system, the two-state system `twoState`, the
`N`-copy system `nsmul N 𝓒`, the Helmholtz free energy); Mathlib's `Real.cosh`, `Real.exp`, `Real.log`
and the lemma `Real.log_pow`.

The physics. One spin in a field `h` is the two-level system `twoState (-h) h`: state `0` has energy
`E₀ = -h`, state `1` has `E₁ = +h`. With `β = 1 / (k_B T)` its partition function is
`Z₁ = e^{-βE₀} + e^{-βE₁} = e^{βh} + e^{-βh} = 2 cosh(βh)`, using `cosh x = (eˣ + e⁻ˣ)/2`. For `N`
distinguishable, non-interacting spins a microstate is a function `f : Fin N → Fin 2` and the energy is
`∑ₖ E_{f(k)}`, so the Boltzmann sum factorises: `Z_N = Z₁^N`. The free energy is `F = -k_B T log Z`, so
`F_N = -k_B T log (Z₁^N) = -N k_B T log (2 cosh(βh))`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : ℝ → ℝ → Prop` for two spots). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓒 : CanonicalEnsemble ι` is any ensemble; the worked examples use `twoState 0 e`, never the
  exercise's `twoState (-h) h`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : Temperature` | a physlib structure holding a temperature `T.val : ℝ≥0` |
| `ℝ≥0` | `NNReal`, the type of real numbers `≥ 0` |
| `↑T.val` | the temperature `T` cast from `ℝ≥0` into `ℝ`; in the source it is `T.val` next to real numbers |
| `T.β`, `↑T.β` | the inverse temperature `β = 1 / (kB * T)`, of type `ℝ≥0`; `↑T.β` is its cast into `ℝ`, written `(T.β : ℝ)` in the source. Treat it as an atom: nothing here unfolds it |
| `kB` | `Constants.kB : ℝ`, Boltzmann's constant (with `open Constants`) |
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`; its field `energy : ι → ℝ` gives each microstate's energy |
| `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]` | `ι` carries a σ-algebra in which single points are measurable (needed by the definitions; `Fin 2` has both) |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[IsFinite 𝓒]`, `𝓒.IsFinite` | `𝓒` is a finite system: counting measure, no continuous degrees of freedom (R2) |
| `twoState a b` | physlib's two-state ensemble on `Fin 2`: state `0` has energy `a`, state `1` has energy `b` (R4) |
| `nsmul n 𝓒` | `n` distinguishable, non-interacting copies of `𝓒`: microstates `Fin n → ι`, energy `∑ k, 𝓒.energy (f k)` (R1) |
| `𝓒.energy i` | `Eᵢ`, the energy of microstate `i` |
| `𝓒.partitionFunction T` | the dimensionless partition function `Z`; for a finite system `Z = ∑ i, rexp (-↑T.β * 𝓒.energy i)` (R2) |
| `𝓒.helmholtzFreeEnergy T` | `F = -kB * ↑T.val * log Z` (R8) |
| `rexp x` | `Real.exp x`, the real exponential |
| `cosh x`, `log x` | `Real.cosh x`, `Real.log x` (with `open Real`); `log` is the natural log, `log 0 = 0` by convention |
| `∑ i, f i` | the sum over all elements of a finite type; `∑ i : Fin 2, f i = f 0 + f 1` (R3) |
| `↑N` | the natural number `N` cast into `ℝ` |
| `-↑T.β * x`, `-↑N * kB * …` | unary minus binds tighter than `*`: `(-↑T.β) * x`, `((-↑N) * kB) * …`; `*` associates to the left. The spec's `-N * kB * T.val * …` with `N : ℕ` is elaborated in `ℝ`, so it shows as `-↑N * kB * ↑T.val * …` |

---

## Part 1 · `paramagnet_Z`

Statement: `(nsmul N (twoState (-h) h)).partitionFunction T = (2 * cosh (↑T.β * h)) ^ N`: the partition
function of `N` spins is `(2 cosh (βh))^N`. First factorise (R1), then write the one-spin `Z` as a finite sum
(R2). Only then call `simp`: it expands the sum (R3), the energies (R4), the signs (R5) and, if you name it,
`cosh` (R6). `ring_nf` (R7) closes what is left.

**R1 · `rw [partitionFunction_nsmul]`** changes the **goal**. The lemma is
`(nsmul n 𝓒).partitionFunction T = 𝓒.partitionFunction T ^ n`: independent copies multiply their partition
functions. Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P ((nsmul n 𝓒).partitionFunction T)` | `⊢ P (𝓒.partitionFunction T ^ n)` |

**R2 · `rw [partitionFunction_of_fintype]`** changes the **goal**. The lemma is
`𝓒.partitionFunction T = ∑ i, rexp (-↑T.β * 𝓒.energy i)` for a finite system. In general `Z` is a
measure-theoretic integral divided by a phase-space volume; for an `IsFinite` system both reduce away.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
(𝓒 : CanonicalEnsemble ι) [IsFinite 𝓒] (T : Temperature)`. `twoState a b` meets every bracket (physlib
provides the `IsFinite` instance). Apply it after R1: then `𝓒` is the single spin.

| Before | After |
|---|---|
| `⊢ P (𝓒.partitionFunction T)` | `⊢ P (∑ i, rexp (-↑T.β * 𝓒.energy i))` |

**R3 · `rw [Fin.sum_univ_two]`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Fin 2 → M)` (`M` has `+` and `0`, as `ℝ` does).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R4 · `simp only [twoState_energy_fst, twoState_energy_snd]`** changes the **goal**. The lemmas are
`(twoState a b).energy 0 = a` and `(twoState a b).energy 1 = b`; both are `@[simp]`, so plain `simp` uses them.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((twoState a b).energy 0) ((twoState a b).energy 1)` | `⊢ P a b` |

**R5 · `simp only [neg_mul, mul_neg, neg_neg]`** changes the **goal**: signs move out of products and double
negations cancel. `neg_mul a b : -a * b = -(a * b)`, `mul_neg a b : a * -b = -(a * b)`, `neg_neg x : - -x = x`.
Plain `simp` uses all three by itself. In the exercise `-↑T.β * -h` becomes `↑T.β * h` and `-↑T.β * h`
becomes `-(↑T.β * h)`, the forms `cosh_eq` produces. Placeholders: `(a b : ℝ)`; in Mathlib any ring.

| Before | After |
|---|---|
| `⊢ P (-a * -b) (-a * b)` | `⊢ P (a * b) (-(a * b))` |

**R6 · `rw [Real.cosh_eq]`** changes the **goal**: `cosh x = (rexp x + rexp (-x)) / 2`. It is not a simp lemma:
name it, `simp [Fin.sum_univ_two, Real.cosh_eq]`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (cosh x)` | `⊢ P ((rexp x + rexp (-x)) / 2)` |

**R7 · `ring_nf`** **closes** a goal whose two sides have the same ring normal form. `2 * (a / 2)` normalises
to `a` (division by a numeral is multiplication by its inverse), even under `^ n` with a variable `n`.
Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ^ n = (2 * (a / 2)) ^ n` | no goals |

**W1: `N` copies of `twoState 0 e`.** R1 and R2 in one `rw`, then `simp [Fin.sum_univ_two]` closes it
(R3, R4, and `rexp (-↑T.β * 0) = 1`):

```lean-goal
⊢ (nsmul N (twoState 0 e)).partitionFunction T = (1 + rexp (-(↑T.β * e))) ^ N
⊢ (∑ i, rexp (-↑T.β * (twoState 0 e).energy i)) ^ N = (1 + rexp (-(↑T.β * e))) ^ N
```

**W3: `rexp x + rexp (-x) = 2 * cosh x`.** R6 turns the right side into exponentials; R7 cancels the `2`:

```lean-goal
⊢ rexp x + rexp (-x) = 2 * cosh x
⊢ rexp x + rexp (-x) = 2 * ((rexp x + rexp (-x)) / 2)
```

---

## Part 2 · `paramagnet_F`

Statement: `(nsmul N (twoState (-h) h)).helmholtzFreeEnergy T = -↑N * kB * ↑T.val * log (2 * cosh (↑T.β * h))`.
Unfold `F` (R8); the `Z` inside the `log` is exactly the left side of Part 1, so rewrite with the theorem
you just proved (R9); pull the exponent out of the `log` (R10); rearrange the product (R11).

**R8 · `rw [helmholtzFreeEnergy]`** changes the **goal**: it unfolds the definition
`𝓒.helmholtzFreeEnergy T = -kB * ↑T.val * log (𝓒.partitionFunction T)`. Placeholders:
`{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.helmholtzFreeEnergy T)` | `⊢ P (-kB * ↑T.val * log (𝓒.partitionFunction T))` |

**R9 · `rw [thm]` with an earlier theorem** changes the **goal**. A theorem proved earlier in the file, such
as `paramagnet_Z`, is a universally quantified equation `thm : ∀ x, f x = g x`; `rw [thm]` finds the
arguments by matching `f _` in the goal. Placeholders: `(f g : ℕ → ℝ) (thm : ∀ x, f x = g x) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (f k)` | `⊢ P (g k)` |

**R10 · `rw [Real.log_pow]`** changes the **goal**. The lemma is `Real.log_pow (x : ℝ) (n : ℕ) :
log (x ^ n) = ↑n * log x`. It holds for every real `x` (no `0 < x` side goal), because `log` is defined on
all of `ℝ`. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (log (x ^ n))` | `⊢ P (↑n * log x)` |

**R11 · `ring`** **closes** an identity of commutative rings. It treats `kB`, `↑T.val`, `↑N` and the whole
`log (…)` as unknowns. Placeholders: `(a b c : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ -a * b * (↑n * c) = -↑n * a * b * c` | no goals |

**W2: the free energy of `N` copies of `twoState 0 e`, reusing W1 (`Z_ground_zero`) by name.**
R8, R9, R10, then R11:

```lean-goal
⊢ (nsmul N (twoState 0 e)).helmholtzFreeEnergy T = -↑N * kB * ↑T.val * log (1 + rexp (-(↑T.β * e)))
⊢ -kB * ↑T.val * log ((nsmul N (twoState 0 e)).partitionFunction T) = -↑N * kB * ↑T.val * log (1 + rexp (-(↑T.β * e)))
⊢ -kB * ↑T.val * log ((1 + rexp (-(↑T.β * e))) ^ N) = -↑N * kB * ↑T.val * log (1 + rexp (-(↑T.β * e)))
⊢ -kB * ↑T.val * (↑N * log (1 + rexp (-(↑T.β * e)))) = -↑N * kB * ↑T.val * log (1 + rexp (-(↑T.β * e)))
```

---

## Traps

- Do the `rw` steps R1, R2 **before** any `simp`. `partitionFunction_def` is a simp lemma, so `simp` on the
  original goal unfolds `Z` into `mathematicalPartitionFunction T / phaseSpaceunit ^ (N * dof)` (the raw
  Boltzmann integral `∫ e^{-βE}` divided by the phase-space cell volume, `dof` = number of continuous degrees
  of freedom), and R1, R2 no longer match. If you see that goal, delete the `simp` and start with R1.
- `Real.cosh_eq` is not a simp lemma; name it in the `simp` call, or `rw [Real.cosh_eq]` on the right side.
- `twoState_partitionFunction_apply_eq_cosh`, `helmholtzFreeEnergy_nsmul` and the
  `twoState_helmholtzFreeEnergy_eq*` closed forms are banned: build `Z` from the finite sum (R2) and `F`
  from its definition (R8).
- You never need to unfold `T.β` or `T.val`. If you do: `(T.val : ℝ) = T.toReal` holds by `rfl`, and
  `Temperature.β_toReal : (T.β : ℝ) = 1 / (kB * T.toReal)`. Keep `↑T.β` as an atom instead.
- `T.β` has type `ℝ≥0`, not `ℝ`. In every `have` write `(T.β : ℝ)`, so your terms show `↑T.β` exactly as the
  goal does.
- In Part 2, `rw [paramagnet_Z]` must come after R8: before it, the goal shows `helmholtzFreeEnergy`, not
  `partitionFunction`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Z` of `N` copies → `Z₁ ^ N` | `rw [partitionFunction_nsmul]` | R1 |
| `Z` of a finite system as a sum | `rw [partitionFunction_of_fintype]` | R2 |
| `∑ i : Fin 2` → two terms | `Fin.sum_univ_two` | R3 |
| energies of `twoState a b` | `twoState_energy_fst`, `twoState_energy_snd` (simp lemmas) | R4 |
| normalise signs `-a * -b`, `-a * b` | `neg_mul`, `mul_neg`, `neg_neg` (simp does it) | R5 |
| `cosh` in exponentials | `Real.cosh_eq` (name it in `simp`) | R6 |
| sum + energies + signs + `cosh` | `simp [Fin.sum_univ_two, Real.cosh_eq]` | R3–R6 |
| `x ^ n = (2 * (x / 2)) ^ n` | `ring_nf` | R7 |
| unfold `F` | `rw [helmholtzFreeEnergy]` | R8 |
| reuse a proved theorem | `rw [thm]` | R9 |
| `log (x ^ n)` → `↑n * log x` | `rw [Real.log_pow]` | R10 |
| rearrange a product | `ring` | R11 |
| see the state | infoview | |
