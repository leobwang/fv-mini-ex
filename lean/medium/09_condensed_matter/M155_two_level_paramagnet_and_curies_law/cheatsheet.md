# M155 · Two-level paramagnet and Curie's law: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Temperature` and
`CanonicalEnsemble` (the Boltzmann probabilities and the partition function of a finite system, the
two-state system `twoState`); Mathlib's hyperbolic functions `tanh`, `sinh`, `cosh` on `ℝ`; Mathlib's
derivative predicate `HasDerivAt` with its chain rule and quotient rule.

The physics. One spin in a field `h`: state `0` (up) has energy `E₀ = -h`, state `1` (down) has
`E₁ = +h`. With `β = 1 / (k_B T)` the Boltzmann weights are `wᵢ = exp(-β Eᵢ)`, the partition function
is `Z = w₀ + w₁ = e^{βh} + e^{-βh}`, and `pᵢ = wᵢ / Z`. The mean magnetisation is
`⟨M⟩ = p₀ - p₁ = (e^{βh} - e^{-βh}) / (e^{βh} + e^{-βh}) = tanh(βh)`. Curie's law: the zero-field
susceptibility `χ = d⟨M⟩/dh` at `h = 0` is `β · tanh'(0) = β · 1 = β`, i.e. `χ ∝ 1/T`. In Lean the
derivative goes through `tanh = sinh / cosh` and the quotient rule, because Mathlib has no
`hasDerivAt_tanh`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : ℝ → ℝ → Prop` for two spots). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal.
- `G : Prop` is an arbitrary goal; an entry that only adds a hypothesis leaves it unchanged.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓒 : CanonicalEnsemble ι` is any ensemble; `twoState a b` uses letters `a b`, never the exercise's `-h, h`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : Temperature` | a physlib structure holding a temperature `T.val : ℝ≥0` (a non-negative real) |
| `ℝ≥0` | `NNReal`, the type of real numbers `≥ 0` |
| `T.β` | the inverse temperature `β = 1 / (kB * T)`, of type `ℝ≥0`; `kB : ℝ` is physlib's Boltzmann constant (`Temperature.β_toReal` states this; not needed here) |
| `↑T.β` | `T.β` cast from `ℝ≥0` into `ℝ`; in the source it is written `(T.β : ℝ)` |
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`; its field `energy : ι → ℝ` gives each microstate's energy |
| `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]` | `ι` carries a σ-algebra in which single points are measurable (needed by the definitions; `Fin 2` has both) |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[IsFinite 𝓒]`, `𝓒.IsFinite` | `𝓒` is a finite system: counting measure, no continuous degrees of freedom (R2) |
| `twoState a b` | physlib's two-state ensemble on `Fin 2`: state `0` has energy `a`, state `1` has energy `b` (R4) |
| `𝓒.energy i` | `Eᵢ`, the energy of microstate `i` |
| `𝓒.probability T i` | `pᵢ = rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T` (R1) |
| `𝓒.mathematicalPartitionFunction T` | `Z`; for a finite system `Z = ∑ i, rexp (-↑T.β * 𝓒.energy i)` (R2) |
| `-a * b`, `-↑T.β * -h` | prefix `-` binds tighter than `*`: `(-a) * b`, `(-↑T.β) * (-h)` (R5 moves the signs out) |
| `rexp x` | `Real.exp x`, the real exponential |
| `tanh x`, `sinh x`, `cosh x` | `Real.tanh`, `Real.sinh`, `Real.cosh` (with `open Real`) |
| `∑ i, f i` | the sum over all elements of a finite type; `∑ i : Fin 2, f i = f 0 + f 1` (R3) |
| `HasDerivAt f f' x` | `f : ℝ → ℝ` is differentiable at `x` with derivative `f'` (a number, not a function) |
| `id` | the identity function `fun y => y` |
| `f ∘ g` | composition, `(f ∘ g) x = f (g x)` (R18) |
| `HMul.hMul c` | the function `fun y => c * y` (Lean prints it this way after `.comp`) |
| `c / d` with `c d : ℝ → ℝ` | the function `fun y => c y / d y` (R15) |
| `↑T.β * 0` inside `cosh`, `sinh` | the point `g 0` at which the chain rule evaluated the outer derivative (R14) |

---

## Part 1 · `mag_eq`

Statement: `mag T h = tanh (↑T.β * h)`, where `mag T h` is `p₀ - p₁` for `twoState (-h) h`. Unfold `mag`
(a plain definition: `simp [mag]`), then the two probabilities, the partition function as a two-term sum,
the two energies, and `tanh` in exponentials. After the signs are normalised both sides are the same term.
Stepping one entry at a time (`simp only [mag]`, R1, R2, R3, R4, R5, R6, R7) also works: the last `rw [sub_div]`
closes the goal itself, because `rw` tries `rfl` afterwards. A single `simp [...]` with R4 and R5 left out works
too, since they are simp lemmas.

**R1 · `simp only [probability]`** changes the **goal**: every `𝓒.probability T i` becomes the Boltzmann
weight over `Z`. Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)
(i : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probability T i)` | `⊢ P (rexp (-↑T.β * 𝓒.energy i) / 𝓒.mathematicalPartitionFunction T)` |

**R2 · `rw [mathematicalPartitionFunction_of_fintype]`** changes the **goal**. The lemma is
`𝓒.mathematicalPartitionFunction T = ∑ i, rexp (-↑T.β * 𝓒.energy i)` for a finite system. In general `Z`
is a measure-theoretic integral; this lemma turns it into a finite sum. Placeholders:
`{ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (𝓒 : CanonicalEnsemble ι)
[IsFinite 𝓒] (T : Temperature)`. `twoState a b` meets every bracket (physlib provides the `IsFinite`
instance). Inside `simp [...]` it rewrites every `Z`.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunction T)` | `⊢ P (∑ i, rexp (-↑T.β * 𝓒.energy i))` |

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
Plain `simp` uses all three by itself. Placeholders: `(a b : ℝ)`; in Mathlib any ring.

| Before | After |
|---|---|
| `⊢ P (-a * -b) (-a * b)` | `⊢ P (a * b) (-(a * b))` |

**R6 · `rw [Real.tanh_eq]`** changes the **goal**: `tanh x = (rexp x - rexp (-x)) / (rexp x + rexp (-x))`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (tanh x)` | `⊢ P ((rexp x - rexp (-x)) / (rexp x + rexp (-x)))` |

**R7 · `rw [sub_div]`** changes the **goal**: `sub_div a b c : (a - b) / c = a / c - b / c`. In `simp [...]` it
splits the `tanh` side into the same shape `p₀ - p₁` has. Placeholders: `(a b c : ℝ)`; in Mathlib any
`[DivisionRing α]` (`ℚ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P ((a - b) / c)` | `⊢ P (a / c - b / c)` |

**W1: the upper-state probability of `twoState a b`.** One `simp only` with R1, R2, R3, R4 closes

```lean-goal
⊢ (twoState a b).probability T 1 = rexp (-↑T.β * b) / (rexp (-↑T.β * a) + rexp (-↑T.β * b))
```

In the exercise the energies are `-h` and `h`, so R5 is also needed: `-↑T.β * -h` must become `↑T.β * h`, and
`-↑T.β * h` must become `-(↑T.β * h)`, the form R6 produces.

---

## Part 2 · `curie`

Statement: `HasDerivAt (mag T) (↑T.β) 0`: the function `h ↦ mag T h` has derivative `β` at `h = 0`. Never
differentiate `probability`: first replace `mag T` by `fun h => sinh (↑T.β * h) / cosh (↑T.β * h)`, using
Part 1 (`funext h`, `rw [mag_eq]`, R8). `funext h` turns the function equation `mag T = fun h => …` into the
equation of values `mag T h = sinh (↑T.β * h) / cosh (↑T.β * h)` with a new `h : ℝ` in the context (TACTIC_STATES,
`ext` row), so `rw [mag_eq]` now finds `mag T h`. Then build the derivative: the inner map `h ↦ β h` (R9 → R10 → R11),
chain rule for `sinh` and `cosh` (R12, R13, R14), quotient rule (R15 with R16), and fix the value (R17, then
`simp`, which uses R18, R19).

**R8 · `rw [Real.tanh_eq_sinh_div_cosh]`** changes the **goal**: `tanh x = sinh x / cosh x`. Placeholders:
`(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (tanh x)` | `⊢ P (sinh x / cosh x)` |

**R9 · `have h1 := hasDerivAt_id x`** changes the **context**: the identity function has derivative `1` at
every point. Placeholders: `(x : ℝ) (G : Prop)`. Write `(0 : ℝ)` for the point, or Lean cannot tell which type
`0` has.

| Before | After |
|---|---|
| `⊢ G` | `h1 : HasDerivAt id 1 x ⊢ G` |

**R10 · `have hc := hf.const_mul c`** changes the **context**. The lemma `HasDerivAt.const_mul` says: from
`hf : HasDerivAt f f' x`, get `HasDerivAt (fun y => c * f y) (c * f') x`. The dot notation `hf.const_mul c`
calls `HasDerivAt.const_mul c hf`. Placeholders: `(f : ℝ → ℝ) (f' x c : ℝ) (hf : HasDerivAt f f' x)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : HasDerivAt (fun y => c * f y) (c * f') x ⊢ G` |

**R11 · `simpa using e`** **closes** the goal when `simp` brings both the type of `e` and the goal to the same
form. Here it removes `id` (`id y = y`) and `* 1`. Placeholders: `(c x : ℝ)
(e : HasDerivAt (fun y => c * id y) (c * 1) x)`. R9, R10 as terms plus R11 give the inner derivative
`HasDerivAt (fun y => c * y) c 0` in one line (W2).

| Before | After |
|---|---|
| `⊢ HasDerivAt (fun y => c * y) c x` | no goals |

**R12 · `have hs := Real.hasDerivAt_sinh x`** changes the **context**: `sinh' = cosh`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : HasDerivAt sinh (cosh x) x ⊢ G` |

**R13 · `have hc := Real.hasDerivAt_cosh x`** changes the **context**: `cosh' = sinh`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : HasDerivAt cosh (sinh x) x ⊢ G` |

**R14 · `have hfg := hf.comp x hg`** changes the **context**: the chain rule `(f ∘ g)'(x) = f'(g x) · g'(x)`.
`hf` must be the derivative of the outer function **at `g x`**, so for `g = fun y => c * y` at `0` write
`Real.hasDerivAt_sinh (c * 0)`, not `Real.hasDerivAt_sinh 0`. Placeholders: `(f g : ℝ → ℝ) (f' g' x : ℝ)
(hf : HasDerivAt f f' (g x)) (hg : HasDerivAt g g' x)`. The result prints `g` as `HMul.hMul c` (W2).

| Before | After |
|---|---|
| `⊢ G` | `hfg : HasDerivAt (f ∘ g) (f' * g') x ⊢ G` |

**R15 · `have hq := hc.div hd hx`** changes the **context**: the quotient rule
`(c / d)'(x) = (c'(x) d(x) - c(x) d'(x)) / d(x)²`, valid when `hx : d x ≠ 0`. Placeholders:
`(c d : ℝ → ℝ) (c' d' x : ℝ) (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x) (hx : d x ≠ 0)`.
The function `c / d` is `fun y => c y / d y` by definition, so `exact` and R17 accept `hq` for a goal
written with `fun y => … / …` (W3), but `rw` would not see them as equal.

| Before | After |
|---|---|
| `⊢ G` | `hq : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x ⊢ G` |

**R16 · `(Real.cosh_pos x).ne'`** **closes** `cosh x ≠ 0`; it is the `hx` argument of R15. `Real.cosh_pos x :
0 < cosh x`, and for `h : a < b`, `h.ne' : b ≠ a` (`LT.lt.ne'`). Write `(Real.cosh_pos _).ne'` to let Lean
find `x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ cosh x ≠ 0` | no goals |

**R17 · `refine hf.congr_deriv ?_`** changes the **goal**: `HasDerivAt.congr_deriv` says `HasDerivAt f f' x →
f' = g' → HasDerivAt f g' x`. The rules R10–R15 produce an unsimplified value `f'`; this leaves only the
equation of numbers `f' = g'`. Placeholders: `(f : ℝ → ℝ) (f' g' x : ℝ) (hf : HasDerivAt f f' x)`. As a term:
`hf.congr_deriv (by simp)`.

| Before | After |
|---|---|
| `⊢ HasDerivAt f g' x` | `⊢ f' = g'` |

**R18 · `rw [Function.comp_apply]`** changes the **goal**: `(f ∘ g) x = f (g x)`. `simp` uses it by itself on
the values R14 and R15 produce. Placeholders: `(f g : ℝ → ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((f ∘ g) x)` | `⊢ P (f (g x))` |

**R19 · `simp only [mul_zero, Real.sinh_zero, Real.cosh_zero]`** changes the **goal**: `c * 0 = 0`,
`sinh 0 = 0`, `cosh 0 = 1`. `simp` uses them by itself and then finishes the arithmetic. Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (sinh (c * 0)) (cosh (c * 0))` | `⊢ P 0 1` |

**W2: chain rule, `y ↦ sinh (c * y)` at `0`.** Inner derivative `hl` by R9, R10, R11; then R12 at `c * 0`
with R14; then R17 and `simp` (R19):

```lean-goal
⊢ HasDerivAt (fun y => sinh (c * y)) c 0
⊢ cosh (c * 0) * c = c
```

with `hs : HasDerivAt (sinh ∘ HMul.hMul c) (cosh (c * 0) * c) 0` in the context before R17.

**W3: quotient rule, `y ↦ y / cosh y` at `0`.** R9 and R13 as terms, combined by R15 with R16; then R17 and
`simp`:

```lean-goal
⊢ HasDerivAt (fun y => y / cosh y) 1 0
⊢ (1 * cosh 0 - id 0 * sinh 0) / cosh 0 ^ 2 = 1
```

---

## Traps

- Mathlib has no `hasDerivAt_tanh`: rewrite `tanh` as `sinh / cosh` (R8) before differentiating.
- `deriv_tanh`, `contDiff_tanh` and the `twoState_probability_fst/snd` closed forms are banned; Part 1 is
  done from the definitions (R1–R7).
- `T.β` has type `ℝ≥0`, not `ℝ`. Next to a real number Lean inserts the cast `↑` itself, but in every
  `have` write it out, `(T.β : ℝ)`, so your terms show `↑T.β` exactly as the goal does.
- In `HasDerivAt (mag T) (↑T.β) 0` the function `mag T` is not applied to anything, so `rw [mag_eq]` finds
  no `mag T h`. Prove the function equation `hm : mag T = fun h => …` first (`funext h`, then
  `rw [mag_eq]`, R8), then `rw [hm]` on the `HasDerivAt` goal.
- The chain rule needs the outer derivative at `g 0` (R14): `Real.hasDerivAt_sinh ((T.β : ℝ) * 0)`.
- After `.comp` and `.div` the function is printed `sinh ∘ HMul.hMul ↑T.β / cosh ∘ HMul.hMul ↑T.β`, not
  `fun h => sinh (↑T.β * h) / cosh (↑T.β * h)`. They are equal by definition, so `exact` (and R17) works;
  do not try to `rw` one into the other.
- The value the quotient rule gives is not literally `↑T.β`: close it with R17 and `simp`, not `exact hq`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `pᵢ` | `simp only [probability]` | R1 |
| `Z` of a finite system as a sum | `mathematicalPartitionFunction_of_fintype` | R2 |
| `∑ i : Fin 2` → two terms | `Fin.sum_univ_two` | R3 |
| energies of `twoState a b` | `twoState_energy_fst`, `twoState_energy_snd` (simp lemmas) | R4 |
| normalise signs `-a * -b`, `-a * b` | `neg_mul`, `mul_neg`, `neg_neg` (simp does it) | R5 |
| `tanh` in exponentials / as `sinh / cosh` | `Real.tanh_eq` / `Real.tanh_eq_sinh_div_cosh` | R6, R8 |
| `(a - b) / c` → `a / c - b / c` | `sub_div` | R7 |
| all of Part 1 | `simp [mag, probability, …, Real.tanh_eq, sub_div]` | R1–R7 |
| derivative of `y ↦ c * y` | `simpa using (hasDerivAt_id (0 : ℝ)).const_mul c` | R9–R11 |
| `sinh' = cosh`, `cosh' = sinh` | `Real.hasDerivAt_sinh x`, `Real.hasDerivAt_cosh x` | R12, R13 |
| chain rule | `(hf : HasDerivAt f f' (g x)).comp x hg` | R14 |
| quotient rule | `hc.div hd (Real.cosh_pos _).ne'` | R15, R16 |
| right function, value not simplified | `hq.congr_deriv (by simp)` | R17–R19 |
| function equation for `rw` | `funext h` (TACTIC_STATES) | |
| see the state | infoview | |
