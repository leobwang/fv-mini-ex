# M156 · Two-level system freezes out: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` in the
β-parameterisation of a finite system (`meanEnergyBetaReal`, `probabilityBetaReal`,
`mathematicalPartitionFunctionBetaReal`) and its two-state system `twoState`; Mathlib's limits
`Filter.Tendsto` with the filters `atTop` and `𝓝`, and the limit lemmas for sums, products,
compositions and quotients; `field_simp`; function extensionality `funext`.

The physics. A two-level system with energies `E₀ = 0` (ground) and `E₁ = ε > 0` (excited) at inverse
temperature `b = 1 / (k_B T)` (here `k_B = 1`) has Boltzmann weights `wᵢ = e^{-b Eᵢ}`, partition
function `Z(b) = w₀ + w₁ = 1 + e^{-bε}`, probabilities `pᵢ(b) = wᵢ / Z(b)` and mean energy
`U(b) = Σᵢ Eᵢ pᵢ(b) = ε e^{-bε} / (1 + e^{-bε}) = ε / (e^{bε} + 1)`. As `T → 0`, i.e. `b → ∞`, the
denominator blows up and `U(b) → 0 = E₀`: the excited level is "frozen out". In Lean, `b` ranges over
all of `ℝ` (no `Temperature` structure), and "as `b → ∞`" is the filter `atTop`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`/`apply`/`exact`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : ℝ → ℝ → Prop` for two spots). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal.
- `G : Prop` is an arbitrary goal; an entry that only adds a hypothesis leaves it unchanged, and the
  hypothesis `k : … → G` only closes the example.
- Placeholders are written as Lean binders. `{ι : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on `ι` (a *type class*). Each entry says which familiar types meet it.
- `𝓒 : CanonicalEnsemble ι` is any ensemble; `twoState a b` uses letters `a b`, never the exercise's `0, ε`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | a physlib structure: a system with microstates `ι`; its field `energy : ι → ℝ` gives each microstate's energy |
| `[Fintype ι]` | `ι` is a finite type, so `∑ i, …` over all of `ι` makes sense |
| `[MeasurableSpace ι]` | `ι` carries a σ-algebra (needed by physlib's general definitions; `Fin 2` has one) |
| `twoState a b` | physlib's two-state ensemble on `Fin 2`: state `0` has energy `a`, state `1` has energy `b` (R5) |
| `𝓒.energy i` | `Eᵢ`, the energy of microstate `i` |
| `𝓒.mathematicalPartitionFunctionBetaReal x` | `Z(x) = ∑ i, rexp (-x * 𝓒.energy i)`, with `x : ℝ` the inverse temperature (R3) |
| `𝓒.probabilityBetaReal x i` | `pᵢ(x) = rexp (-x * 𝓒.energy i) / Z(x)` (R2) |
| `𝓒.meanEnergyBetaReal x` | `U(x) = ∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal x i` (R1); `𝓒.meanEnergyBetaReal` alone is the function `x ↦ U(x)` |
| `rexp x` | `Real.exp x`, the real exponential |
| `∑ i, f i` | the sum over all elements of a finite type; `∑ i : Fin 2, f i = f 0 + f 1` (R4) |
| `x⁻¹` | the inverse `1 / x` (in `ℝ`, `0⁻¹ = 0`) |
| `Filter α` | a "limit point" for functions on `α`: where the argument goes. You never build one by hand here |
| `atTop` | `Filter.atTop`: the argument goes to `+∞` (as a source) / the value goes to `+∞` (as a target) |
| `𝓝 L` | `nhds L`, the neighbourhood filter of `L`: the value goes to `L` (notation from `open Topology`) |
| `Tendsto f l l'` | `Filter.Tendsto`: `f(y)` goes to `l'` as `y` goes to `l`. `Tendsto f atTop (𝓝 L)` is `lim_{y→∞} f y = L`; `Tendsto f atTop atTop` is `f y → ∞` |
| `fun y => f y / g y` | the function `y ↦ f(y) / g(y)`; Lean may rename the bound variable (`fun x => …`) |
| `id` | the identity function `fun y => y` |
| `g ∘ f` | composition, `(g ∘ f) y = g (f y)` |

---

## Part 1 · `twoState_low_T`

Statement: for `ε > 0`, `Tendsto (twoState 0 ε).meanEnergyBetaReal atTop (𝓝 0)`, i.e. `U(b) → 0` as
`b → ∞`. Plan: prove the closed form `U(b) = ε / (rexp (b * ε) + 1)` for every `b` as a `have`
(R1–R10), swap the function in the goal for that closed form (R11, R12), then show the quotient tends to
`0` because the numerator is constant and the denominator grows without bound (R13–R19).

### Unfolding the mean energy

All of R1–R8 fit in **one** `simp [...]` call that names the three definitions and `Fin.sum_univ_two`:
R5–R8 are simp lemmas already. Afterwards the left side is `ε` times the excited-state fraction,
`ε * (rexp (-(b * ε)) / (1 + rexp (-(b * ε))))`, against your closed form on the right; R9 then rewrites
both `rexp (-(b * ε))` at once.

**R1 · `simp only [meanEnergyBetaReal]`** changes the **goal**: the mean energy becomes its defining sum.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.meanEnergyBetaReal x)` | `⊢ P (∑ i, 𝓒.energy i * 𝓒.probabilityBetaReal x i)` |

**R2 · `simp only [probabilityBetaReal]`** changes the **goal**: each probability becomes a Boltzmann weight
over `Z(x)`. Placeholders: as R1, plus `(i : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal x i)` | `⊢ P (rexp (-x * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal x)` |

**R3 · `simp only [mathematicalPartitionFunctionBetaReal]`** changes the **goal**: `Z(x)` becomes its sum.
Placeholders: as R1.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunctionBetaReal x)` | `⊢ P (∑ i, rexp (-x * 𝓒.energy i))` |

**R4 · `rw [Fin.sum_univ_two]`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Fin 2 → M)` (`M` has `+` and `0`; `ℝ` qualifies). Use it through
`simp` (`rw` rewrites one sum at a time; R1 and R3 each produce one).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R5 · `twoState_energy_fst`, `twoState_energy_snd`** change the **goal**: the energies of `twoState a b` are
`a` and `b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((twoState a b).energy 0) ((twoState a b).energy 1)` | `⊢ P a b` |

**R6 · `mul_zero`, `Real.exp_zero`** change the **goal**: the ground-state weight `rexp (-x * 0)` is `1`.
`mul_zero a : a * 0 = 0`, `Real.exp_zero : rexp 0 = 1`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp (-x * 0))` | `⊢ P 1` |

**R7 · `zero_mul`, `zero_add`** change the **goal**: a term weighted by the energy `0` drops out of the sum.
`zero_mul a : 0 * a = 0`, `zero_add a : 0 + a = a`. Placeholders: `(u v : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (0 * u + v)` | `⊢ P v` |

**R8 · `rw [neg_mul]`** changes the **goal**. The lemma is `neg_mul a b : -a * b = -(a * b)`; `simp` uses it,
so `-b * ε` shows up as `-(b * ε)`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

### Algebra with exponentials

**R9 · `rw [Real.exp_neg]`** changes the **goal**. The lemma is `Real.exp_neg y : rexp (-y) = (rexp y)⁻¹`;
it turns both `rexp (-(b * ε))` into `(rexp (b * ε))⁻¹`, so only one exponential is left. Placeholders:
`(y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp (-y))` | `⊢ P (rexp y)⁻¹` |

**R10 · `field_simp`** changes the **goal**: it multiplies out every fraction, given that each denominator is
nonzero, and on an equation between fractions usually closes it. It proves
`rexp y ≠ 0` and `1 + (rexp y)⁻¹ ≠ 0` on its own (exponentials are positive) and uses hypotheses such as
`hx : 0 < x` for variables. Placeholders: `(a x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ P (a / (1 + x⁻¹))` | `hx : 0 < x ⊢ P (a * x / (x + 1))` |

### Replacing the function by its closed form

**R11 · `funext h`** changes the **context** (used as `have hfg := funext h`): from pointwise equality
`h : ∀ y, f y = g y` it builds the equality of functions `f = g`. Placeholders: `(f g : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hfg : f = g ⊢ G` |

**R12 · `rw [show f = g from e]`** changes the **goal**: `show T from e` is the proof `e` with its type
stated as `T`, so `rw` rewrites `f` (unapplied) to the `fun` you wrote. Placeholders: `(f : ℝ → ℝ) (c : ℝ)
(P : (ℝ → ℝ) → Prop)`, `e := funext h`.

| Before | After |
|---|---|
| `⊢ P f` | `⊢ P fun y => c * y` |

### Limits

**R13 · `apply Tendsto.div_atTop hf`** changes the **goal**. The lemma is
`Tendsto.div_atTop : Tendsto f l (𝓝 a) → Tendsto g l atTop → Tendsto (fun x => f x / g x) l (𝓝 0)`
(for `ℝ` and other ordered fields). Giving the numerator's limit `hf` leaves the denominator's.
Placeholders: `{α : Type} (l : Filter α) (f g : α → ℝ) (a : ℝ) (hf : Tendsto f l (𝓝 a))`. In the exercise,
pass `tendsto_const_nhds` (R14) as `hf`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun y => f y / g y) l (𝓝 0)` | `⊢ Tendsto g l atTop` |

**R14 · `tendsto_const_nhds`** **closes** `Tendsto (fun _ => c) l (𝓝 c)`: a constant function tends to its
value. Its arguments are implicit, so Lean reads `c` off the goal it is checked against: use it for the
constant numerator `ε` (R13) and for the constant `1` added to the exponential (R19). Inside a `have`
with no stated type there is no goal to read `c` from; name it, `tendsto_const_nhds (x := 1)`. Placeholders: `{α : Type} (l : Filter α)
(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => c) l (𝓝 c)` | closed |

**R15 · `Real.tendsto_exp_atTop`** changes the **context**: `Tendsto rexp atTop atTop`, `eᵗ → ∞` as `t → ∞`.

| Before | After |
|---|---|
| `⊢ G` | `he : Tendsto rexp atTop atTop ⊢ G` |

**R16 · `tendsto_id`** changes the **context**: `Tendsto id l l` (the identity goes where its argument goes).
It is the starting point for "`y → ∞`" in R17. The filter is implicit; here it is fixed by the type
annotation `(id : ℝ → ℝ)` and `atTop`.

| Before | After |
|---|---|
| `⊢ G` | `hi : Tendsto id atTop atTop ⊢ G` |

**R17 · `hf.atTop_mul_const hr`** changes the **context**. The lemma is `Tendsto.atTop_mul_const :
0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop` (dot notation: `hf.atTop_mul_const hr` is
`Tendsto.atTop_mul_const hr hf`). This is where `0 < ε` is used. Placeholders: `{α : Type} (l : Filter α)
(f : α → ℝ) (r : ℝ) (hr : 0 < r) (hf : Tendsto f l atTop)`.

| Before | After |
|---|---|
| `hr : 0 < r, hf : Tendsto f l atTop ⊢ G` | `hm : Tendsto (fun x => f x * r) l atTop ⊢ G` |

**R18 · `hg.comp hf`** changes the **context**. The lemma is `Tendsto.comp : Tendsto g l' l'' → Tendsto f l l'
→ Tendsto (g ∘ f) l l''` (the outer function's limit comes first). Placeholders: `(f g : ℝ → ℝ)`, here with
all filters `atTop`.

| Before | After |
|---|---|
| `hf : Tendsto f atTop atTop, hg : Tendsto g atTop atTop ⊢ G` | `hc : Tendsto (g ∘ f) atTop atTop ⊢ G` |

**R19 · `hf.atTop_add hg`** changes the **context**. The lemma is `Tendsto.atTop_add : Tendsto f l atTop →
Tendsto g l (𝓝 C) → Tendsto (fun x => f x + g x) l atTop` (∞ plus something convergent is ∞).
Placeholders: `{α : Type} (l : Filter α) (f g : α → ℝ) (C : ℝ)`.

| Before | After |
|---|---|
| `hf : Tendsto f l atTop, hg : Tendsto g l (𝓝 C) ⊢ G` | `hs : Tendsto (fun x => f x + g x) l atTop ⊢ G` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a closed form by unfolding.** `simp only [probabilityBetaReal, mathematicalPartitionFunctionBetaReal,
Fin.sum_univ_two, twoState_energy_fst, twoState_energy_snd]` (R2–R5) closes

```lean-goal
⊢ (twoState a b).probabilityBetaReal x 0 = rexp (-x * a) / (rexp (-x * a) + rexp (-x * b))
```

**W2: swap the function, then take the limit** (R11 → R12, then R16, R17). With
`h : ∀ y, f y = y * 3`, `rw [h]` fails (the goal has `f`, never `f y`), but
`rw [show f = fun y => y * 3 from funext h]` gives

```lean-goal
⊢ Tendsto f atTop atTop
⊢ Tendsto (fun y => y * 3) atTop atTop
```

and `exact tendsto_id.atTop_mul_const (by norm_num)` closes it.

**W3: a composite limit** (R15, R16 → R17 → R18). `have hc := Real.tendsto_exp_atTop.comp
(tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2))` gives a statement about `rexp ∘ fun x => id x * 2`;
`exact hc` closes the goal about `fun y => rexp (y * 2)` because the two functions are definitionally equal.

| Before | After `have hc := …` |
|---|---|
| `⊢ Tendsto (fun y => rexp (y * 2)) atTop atTop` | `hc : Tendsto (rexp ∘ fun x => id x * 2) atTop atTop ⊢ Tendsto (fun y => rexp (y * 2)) atTop atTop` |

**W4: constant over something that grows** (R13 with R14, then R19 with R14). `apply Tendsto.div_atTop
tendsto_const_nhds` turns the quotient goal into the denominator goal:

```lean-goal
⊢ Tendsto (fun y => c / (y * r + 7)) atTop (𝓝 0)
⊢ Tendsto (fun x => x * r + 7) atTop atTop
```

and `exact (tendsto_id.atTop_mul_const hr).atTop_add tendsto_const_nhds` closes it. The exercise's
denominator adds one more layer, the exponential, through R18.

---

## Traps

- `rw [h]` / `simp_rw [h]` with `h : ∀ b, U b = …` cannot rewrite the bare function `U` in
  `Tendsto U atTop (𝓝 0)`: there is no `U b` in the goal. Turn `h` into `U = fun b => …` with `funext h`
  first (R11, R12).
- Prove the closed form as a `have` **before** touching the limit, with its own `intro b`: inside
  `Tendsto` there is no `b` to unfold at.
- Write `Real.exp` (or `rexp`) in the `have`, and make its right side match exactly what R13 expects:
  a `fun b => numerator / denominator`.
- `Tendsto.div_atTop` gives the limit `0` only; it needs the numerator's limit as its first argument
  (`tendsto_const_nhds`), and `apply` then leaves the denominator.
- `hg.comp hf` puts the **outer** function first: for `rexp (b * ε)` it is
  `Real.tendsto_exp_atTop.comp (…b * ε → ∞…)`, not the other way round.
- Build the denominator's limit as **one** term given to `exact`, so every implicit argument is read
  off the goal. Step by step, `have hs := hc.atTop_add tendsto_const_nhds` fails with "don't know how to
  synthesize implicit argument `C`": write `tendsto_const_nhds (x := 1)` there. The final `exact hs` then
  works although `hs` mentions `rexp ∘ fun x => id x * ε` (definitional equality, as in W3).
- `Tendsto.atTop_mul_const` multiplies on the **right** (`f x * r`), matching `b * ε`; `ε * b` would need
  `Tendsto.const_mul_atTop`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `U(b)`, `pᵢ(b)`, `Z(b)` and the two terms | `simp [meanEnergyBetaReal, probabilityBetaReal, mathematicalPartitionFunctionBetaReal, Fin.sum_univ_two]` | R1–R8 |
| `rexp (-y) → (rexp y)⁻¹` | `rw [Real.exp_neg]` | R9 |
| clear fractions, close the equation | `field_simp` | R10 |
| `∀ y, f y = g y` → `f = g` | `funext h` | R11 |
| replace an unapplied function | `rw [show f = fun y => … from funext h]` | R12 |
| `f / g → 0` from `g → ∞` | `apply Tendsto.div_atTop hf` | R13 |
| constant tends to itself | `tendsto_const_nhds` | R14 |
| `eᵗ → ∞` | `Real.tendsto_exp_atTop` | R15 |
| `y → ∞` | `tendsto_id` | R16 |
| `f → ∞`, `0 < r` ⇒ `f * r → ∞` | `hf.atTop_mul_const hr` | R17 |
| limit of `g ∘ f` | `hg.comp hf` | R18 |
| `f → ∞`, `g → C` ⇒ `f + g → ∞` | `hf.atTop_add hg` | R19 |
| see the state | infoview | |
