# E116 · Two-state partition function: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble`, its
two-level system `twoState`, its `Temperature` type with inverse temperature `T.β`, and the
thermodynamic `partitionFunction`; Mathlib's finite sums `∑ i, f i`, the type `ℝ≥0` of non-negative
reals with its cast `↑` into `ℝ`, and `Real.exp`.

The physics: a canonical ensemble is a system with microstates `i` of energy `E_i` in contact with a heat
bath at temperature `T`, with inverse temperature `β = 1/(k_B T)` (`k_B` is Boltzmann's constant). For
finitely many states the partition function is the sum of Boltzmann weights `Z = ∑_i e^{-β E_i}`. A
two-level system has states `0, 1` with energies `E₀, E₁`, so `Z = e^{-βE₀} + e^{-βE₁}`; with the ground
state at `E₀ = 0` and the excited state at `E₁ = ε` this is `Z = 1 + e^{-βε}`. In Lean: turn `Z` into a
finite sum (R1), split the sum over `Fin 2` (R2), plug in the energies (R3, R4), and simplify `e^{-β·0}`
to `1` (R5, R6).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[MulZeroClass α]`
  is a requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | physlib structure: a system whose microstates are the elements of `ι`. Its field `energy : ι → ℝ` matters here; the others (`dof`, `phaseSpaceunit`, the measure `μ`) are fixed by `IsFinite` |
| `twoState E₀ E₁` | `CanonicalEnsemble (Fin 2)`: states `0, 1` (`Fin 2 = {0, 1}`) with energies `E₀`, `E₁` and the counting measure |
| `(twoState 0 ε).energy i` | `CanonicalEnsemble.energy (twoState 0 ε) i`, the energy of state `i` (dot notation, E017). Lean does not compute it for a variable `i`; R3/R4 evaluate it at `0` and `1` |
| `Temperature` | physlib structure wrapping one field `val : ℝ≥0`, the absolute temperature |
| `ℝ≥0` | `NNReal`, the type of real numbers `≥ 0` (a real together with a proof that it is non-negative) |
| `T.β` | `Temperature.β T : ℝ≥0`, the inverse temperature `1 / (kB * T)` |
| `↑T.β` | `T.β` cast into `ℝ` (`NNReal.toReal`). The statement writes it `(T.β : ℝ)` and Lean prints `↑T.β` |
| `𝓒.partitionFunction T` | physlib's thermodynamic `Z`. Its definition is `Z_math / phaseSpaceunit ^ dof` with `Z_math` an integral, so do not unfold it; R1 turns it into a finite sum |
| `𝓒.mathematicalPartitionFunction T` | that `Z_math`: the integral `∫ e^{-β E} dμ` over the states. You only see it if you unfold `partitionFunction` (see Traps); go back and use R1 |
| `𝓒.dof`, `𝓒.phaseSpaceunit` | fields of `CanonicalEnsemble`: degrees of freedom (`: ℕ`) and the phase-space cell size `h` (`: ℝ`); `IsFinite` makes them `0` and `1` |
| `𝓒.IsFinite` | type class: the measure is the counting measure, `dof = 0`, `phaseSpaceunit = 1`. physlib has an instance for `twoState E₀ E₁`, found automatically |
| `∑ i, f i` | `Finset.sum Finset.univ f`: the sum of `f i` over all `i : ι` |
| `Real.exp x` | `e^x` on the reals |
| `-↑T.β * ε` | `(-↑T.β) * ε`: negation binds tighter than `*` |

---

## Part 1 · `twoState_Z`

Statement: for `ε : ℝ` and `T : Temperature`,
`(twoState 0 ε).partitionFunction T = 1 + Real.exp (-↑T.β * ε)`, i.e. `Z = 1 + e^{-βε}`.

### From the partition function to a finite sum

**R1 · `rw [partitionFunction_of_fintype]`** changes the **goal**. The lemma is
`partitionFunction_of_fintype : 𝓒.partitionFunction T = ∑ i, Real.exp (-↑T.β * 𝓒.energy i)`.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
(𝓒 : CanonicalEnsemble ι) [𝓒.IsFinite] (T : Temperature)`. `[Fintype ι]`: finitely many states;
`[MeasurableSpace ι]`: a σ-algebra on `ι`, needed for the measure; `[MeasurableSingletonClass ι]`: every
single state `{i}` is measurable. `Fin 2` meets all three, and `twoState E₀ E₁` meets `IsFinite`; Lean finds
these instances itself, so you never name them.

| Before | After |
|---|---|
| `⊢ P (𝓒.partitionFunction T)` | `⊢ P (∑ i, Real.exp (-↑T.β * 𝓒.energy i))` |

**R2 · `rw [Fin.sum_univ_two]`** changes the **goal**. The lemma is `Fin.sum_univ_two : ∑ i, f i = f 0 + f 1`:
a sum over `Fin 2` is its two terms. Placeholders: `{M : Type} [AddCommMonoid M] (f : Fin 2 → M)`; `M` has a
commutative `+` with `0`, as `ℕ`, `ℝ`, `ℂ` do. In the exercise `f = fun i => Real.exp (-↑T.β * (twoState 0 ε).energy i)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

### The two energies

**R3 · `rw [twoState_energy_fst]`** changes the **goal**. The lemma is
`twoState_energy_fst : (twoState E₀ E₁).energy 0 = E₀`. Placeholders: `(E₀ E₁ : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((twoState E₀ E₁).energy 0)` | `⊢ P E₀` |

**R4 · `rw [twoState_energy_snd]`** changes the **goal**. The lemma is
`twoState_energy_snd : (twoState E₀ E₁).energy 1 = E₁`. Placeholders: `(E₀ E₁ : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((twoState E₀ E₁).energy 1)` | `⊢ P E₁` |

### Cleaning up the zero energy

**R5 · `rw [mul_zero]`** changes the **goal**. The lemma is `mul_zero : a * 0 = 0`. Placeholders:
`{α : Type} [MulZeroClass α] (a : α)`; `α` has `*` and a `0` that absorbs it, as `ℕ`, `ℝ`, `ℂ` do. In the
exercise `a = -↑T.β`.

| Before | After |
|---|---|
| `⊢ P (a * 0)` | `⊢ P 0` |

**R6 · `rw [Real.exp_zero]`** changes the **goal**. The lemma is `Real.exp_zero : Real.exp 0 = 1`. If the
goal becomes `x = x`, `rw` closes it by itself (it tries `rfl` at the end), so the proof ends here.

| Before | After |
|---|---|
| `⊢ P (Real.exp 0)` | `⊢ P 1` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: a sum over `Fin 2` with a zero term.** `f : Fin 2 → ℝ`, `x : ℝ`, `hf0 : f 0 = 0`. R2, then
`rw [hf0]` (the role R3 plays in the exercise), R5, and R6, which closes the goal:

```lean-goal
⊢ ∑ i, Real.exp (-x * f i) = 1 + Real.exp (-x * f 1)
⊢ Real.exp (-x * f 0) + Real.exp (-x * f 1) = 1 + Real.exp (-x * f 1)
⊢ Real.exp (-x * 0) + Real.exp (-x * f 1) = 1 + Real.exp (-x * f 1)
⊢ Real.exp 0 + Real.exp (-x * f 1) = 1 + Real.exp (-x * f 1)
```

**W2: reading off energies.** R3, R4, then `norm_num` on the numbers:

```lean-goal
⊢ (twoState 1 2).energy 0 + (twoState 1 2).energy 1 = 3
⊢ 1 + (twoState 1 2).energy 1 = 3
⊢ 1 + 2 = 3
```

---

## Traps

- Do not start with plain `simp`: it uses physlib's simp lemma `partitionFunction_def` and leaves
  `(twoState 0 ε).mathematicalPartitionFunction T / (twoState 0 ε).phaseSpaceunit ^ (twoState 0 ε).dof = …`,
  an integral you do not want. Rewrite with R1 first; after R1, `simp` alone finishes (it knows R2–R6).
- Order matters: R3/R4 need the literal `(twoState 0 ε).energy 0` / `… 1`. Right after R1 there is only
  `(twoState 0 ε).energy i` under the `∑` binder, and `rw [twoState_energy_fst]` fails with "did not find
  an occurrence". Split the sum (R2) first.
- `IsFinite` and the other instances are found automatically: never pass them by name.
- The banned lemmas `twoState_partitionFunction_apply` and `twoState_partitionFunction_apply_eq_cosh` state
  `Z` for `twoState` directly; the point is to derive it from R1.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `𝓒.partitionFunction T` → `∑ i, Real.exp (-↑T.β * 𝓒.energy i)` | `rw [partitionFunction_of_fintype]` | R1 |
| `∑ i : Fin 2, f i` → `f 0 + f 1` | `rw [Fin.sum_univ_two]` | R2 |
| `(twoState E₀ E₁).energy 0` → `E₀` | `rw [twoState_energy_fst]` | R3 |
| `(twoState E₀ E₁).energy 1` → `E₁` | `rw [twoState_energy_snd]` | R4 |
| `a * 0` → `0` | `rw [mul_zero]` | R5 |
| `Real.exp 0` → `1` | `rw [Real.exp_zero]` | R6 |
| everything after R1 | `simp` | Traps |
| see the state | infoview | |
