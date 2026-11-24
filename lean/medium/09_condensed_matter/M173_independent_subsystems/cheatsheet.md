# M173 · Independent subsystems: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` (finite
ensembles, the product system `𝓒 + 𝓒'`, `Temperature` and `β`), Mathlib's finite sums `∑` over
`Fintype`s and the `Finset` lemmas that split, multiply, swap and factor them.

The physics. A finite system has microstates `i : ι` with energies `E i`. At temperature `T`, with
`β = 1 / (k_B T)` (`k_B` is Boltzmann's constant), the partition function is `Z = ∑ i, exp (-β E i)`,
the probability of `i` is `p i = exp (-β E i) / Z`, and the mean energy is `U = ∑ i, E i * p i`. Two
non-interacting systems form one system with microstates `(i, j) : ι × ι'` and energy `E i + E' j`.
Because `exp` turns that sum into a product, `Z = Z₁ Z₂`, `p (i, j) = p₁ i * p₂ j`, and `U = U₁ + U₂`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types,
then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : R → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing R]` is
  a requirement on `R` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A
  hypothesis whose text contains a comma (`h1 : ∑ i, …`) is written next to the table, not in a cell.

## Reading the goals

| You see | It means |
|---|---|
| `CanonicalEnsemble ι` | physlib: a system with microstates `ι`, `energy : ι → ℝ`, a measure on `ι`, and the constants `dof`, `phaseSpaceunit` |
| `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]` | measure-theory bookkeeping on `ι`; for a finite `ι` they only say every set of states can be measured. Never used by hand here |
| `[Fintype ι]` | `ι` is finite, with a list of all its elements; this is what makes `∑ i, f i` meaningful |
| `[𝓒.IsFinite]` | `𝓒`'s measure is the counting measure, `dof = 0`, `phaseSpaceunit = 1`: integrals over `ι` are finite sums |
| `[Nonempty ι]` | `ι` has at least one element (so `Z > 0` and probabilities sum to `1`) |
| `𝓒.energy i` | `E i`, the energy of microstate `i` |
| `𝓒 + 𝓒'` | the product system: microstates `ι × ι'`, energy `𝓒.energy x.1 + 𝓒'.energy x.2` (R5) |
| `(i, j)`, `x.1`, `x.2` | a pair, and the first and second component of `x : ι × ι'` |
| `T : Temperature` | physlib's temperature, a wrapper around a nonnegative real |
| `T.β` | `1 / (k_B T)`, of type `ℝ≥0` (nonnegative reals, `NNReal`) |
| `↑T.β` | `T.β` cast from `ℝ≥0` into `ℝ` |
| `rexp x` | `Real.exp x`, the real exponential |
| `𝓒.partitionFunction T` | `Z(T)`; for a finite ensemble it is `∑ i, rexp (-↑T.β * 𝓒.energy i)` (R1) |
| `𝓒.mathematicalPartitionFunction T` | `Z(T)` before dividing by `phaseSpaceunit ^ dof`; for a finite ensemble the same sum (R9) |
| `𝓒.probability T i` | `p i = rexp (-↑T.β * E i) / mathematicalPartitionFunction T` (R8) |
| `𝓒.meanEnergy T` | `U(T)`; for a finite ensemble `∑ i, 𝓒.energy i * 𝓒.probability T i` (R11) |
| `∑ i, f i` | the sum of `f i` over all `i` of a `Fintype`; it is `∑ i ∈ Finset.univ, f i` |
| `∑ i ∈ s, f i` | the sum over the `Finset` (finite set) `s` |
| `Finset.univ` | the Finset of all elements of a `Fintype` |
| `∑ x, ∑ y, f (x, y)` | a double sum; Lean names bound variables `x`, `y`, `x_1` as it likes |
| `inst✝ : 𝓒.IsFinite` | an unnamed instance hypothesis, from a `[…]` binder |
| `x✝ : i ∈ Finset.univ` | an unnamed hypothesis (introduced with `_`, R4) |
| `case e_a` | a goal produced by `congr` (R15) |

---

## Part 1 · `Z_mul`

Statement: `(𝓒 + 𝓒').partitionFunction T = 𝓒.partitionFunction T * 𝓒'.partitionFunction T`, i.e.
`Z = Z₁ Z₂`. Rewrite the three `Z`s as sums (R1), turn the left into a double sum (R2) and the right into a
double sum (R3), match them summand by summand (R4), and factor the exponential (R5 → R6 → R7).

**R1 · `rw [partitionFunction_of_fintype]`** changes the **goal**. The lemma is
`𝓐.partitionFunction T = ∑ i, rexp (-↑T.β * 𝓐.energy i)` for a finite ensemble. One `rw` fixes `𝓐` to the
first ensemble it meets; repeat it once per ensemble. Placeholders: `{α : Type} [Fintype α]
[MeasurableSpace α] [MeasurableSingletonClass α] (𝓐 : CanonicalEnsemble α) [𝓐.IsFinite] (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓐.partitionFunction T)` | `⊢ P (∑ i, rexp (-↑T.β * 𝓐.energy i))` |

**R2 · `rw [Fintype.sum_prod_type]`** changes the **goal**: a sum over pairs becomes a double sum,
`∑ x, f x = ∑ x, ∑ y, f (x, y)`. Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M]
(f : α × β → M)`; `[AddCommMonoid M]` means `M` has `+` and `0` with the usual laws (`ℕ`, `ℤ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R3 · `rw [Finset.sum_mul_sum]`** changes the **goal**: a product of two sums becomes a double sum of
products, `(∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`. Right to left
(`← Finset.sum_mul_sum`) it factors a double sum of products. Placeholders: `{α β R : Type} [Fintype α]
[Fintype β] [CommRing R] (f : α → R) (g : β → R)`; `[CommRing R]` means `+`, `-`, `*` with the usual laws
(`ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) * ∑ j, g j)` | `⊢ P (∑ i, ∑ j, f i * g j)` |

**R4 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. With `rfl` for the index
sets, what is left is one summand for an arbitrary `i`. For a double sum nest it:
`fun i _ => Finset.sum_congr rfl fun j _ => ?_`. Placeholders: `{α M : Type} [Fintype α] [AddCommMonoid M]
(f g : α → M)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : α, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R5 · `rw [energy_add_apply]`** changes the **goal**: the energy of the product system is the sum of the
two energies, `(𝓐 + 𝓑).energy x = 𝓐.energy x.1 + 𝓑.energy x.2`. On a pair `(i, j)` it leaves
`(i, j).1`, which is `i` by definition (`rfl` and `simp` see this; `simp only` cleans it up). Placeholders:
`{α β : Type} [MeasurableSpace α] [MeasurableSpace β] (𝓐 : CanonicalEnsemble α) (𝓑 : CanonicalEnsemble β)
(x : α × β)`.

| Before | After |
|---|---|
| `⊢ P ((𝓐 + 𝓑).energy x)` | `⊢ P (𝓐.energy x.1 + 𝓑.energy x.2)` |

**R6 · `rw [mul_add]`** changes the **goal**: `a * (b + c) = a * b + a * c`. Here it distributes `-↑T.β`
over the two energies. Placeholders: `{R : Type} [CommRing R] (a b c : R)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R7 · `rw [Real.exp_add]`** changes the **goal**: `rexp (x + y) = rexp x * rexp y`. This is the
physics: independent energies give a factorised Boltzmann weight. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp (x + y))` | `⊢ P (rexp x * rexp y)` |

**W1** (R2, R3 on plain functions `f : α → ℝ`, `g : β → ℝ`). After R2 the left side is a double sum of
`f (x, y).1 * g (x, y).2`; after R3 the right side is `∑ i, ∑ j, f i * g j`, and the closing `rfl` of `rw`
sees that the two agree:

```lean-goal
⊢ ∑ x, f x.1 * g x.2 = (∑ a, f a) * ∑ b, g b
⊢ ∑ x, ∑ y, f (x, y).1 * g (x, y).2 = (∑ a, f a) * ∑ b, g b
```

In `Z_mul` the summands do not agree on the nose (one side has `(𝓒 + 𝓒').energy (i, j)`), so you need R4
to reach a single summand and R5 → R6 → R7 there.

---

## Part 2 · `U_add`

Statement: `(𝓒 + 𝓒').meanEnergy T = 𝓒.meanEnergy T + 𝓒'.meanEnergy T`, i.e. `U = U₁ + U₂`. It needs
`[Nonempty ι] [Nonempty ι']` because it uses `∑ p = 1`.

### Milestone first: the probability factorises

Prove a helper lemma **before** `U_add` (outside the spec; any name, e.g. `prob_mul`), with the binders of
`Z_mul` plus `(i : ι) (j : ι')`:
`(𝓒 + 𝓒').probability T (i, j) = 𝓒.probability T i * 𝓒'.probability T j`.
It is one `simp only [...]` listing R8, R9, R2, R5, R6, R7, `← Finset.sum_mul_sum` (R3 backwards), R10 in
that order: unfold `p`, write both `Z`s as sums, factor numerator and denominator, split the quotient.
Use `simp only`, not `rw`: the energies sit under `∑` binders, where `rw` cannot rewrite.

**R8 · `simp only [probability]`** changes the **goal**: it unfolds the definition
`probability T i = rexp (-↑T.β * energy i) / mathematicalPartitionFunction T`. Placeholders:
`{α : Type} [MeasurableSpace α] (𝓐 : CanonicalEnsemble α) (T : Temperature) (i : α)`.

| Before | After |
|---|---|
| `⊢ P (𝓐.probability T i)` | `⊢ P (rexp (-↑T.β * 𝓐.energy i) / 𝓐.mathematicalPartitionFunction T)` |

**R9 · `mathematicalPartitionFunction_of_fintype`** changes the **goal**:
`𝓐.mathematicalPartitionFunction T = ∑ i, rexp (-β T * 𝓐.energy i)` (Lean prints `β T` as `↑T.β`).
Placeholders: as in R1.

| Before | After |
|---|---|
| `⊢ P (𝓐.mathematicalPartitionFunction T)` | `⊢ P (∑ i, rexp (-↑T.β * 𝓐.energy i))` |

**R10 · `div_mul_div_comm`** changes the **goal**: `a / b * (c / d) = a * c / (b * d)`. In the helper it
turns the right side `p₁ i * p₂ j` into the same quotient as the left. Placeholders: `{K : Type} [Field K]
(a b c d : K)`; `[Field K]` means `+ - * /` with the usual laws (`ℚ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (a / b * (c / d))` | `⊢ P (a * c / (b * d))` |

**W4** (R7, then R10 right to left, on plain reals):

```lean-goal
⊢ rexp (x + y) / (A * B) = rexp x / A * (rexp y / B)
⊢ rexp x * rexp y / (A * B) = rexp x / A * (rexp y / B)
```

### The main proof

**R11 · `rw [meanEnergy_of_fintype]`** changes the **goal**:
`𝓐.meanEnergy T = ∑ i, 𝓐.energy i * 𝓐.probability T i`. Repeat once per ensemble, then R2 on the left.
Placeholders: as in R1.

| Before | After |
|---|---|
| `⊢ P (𝓐.meanEnergy T)` | `⊢ P (∑ i, 𝓐.energy i * 𝓐.probability T i)` |

Then `simp only [your_helper, energy_add_apply]` (milestone, R5) turns each summand into
`(𝓒.energy x + 𝓒'.energy x_1) * (𝓒.probability T x * 𝓒'.probability T x_1)`.

**R12 · `add_mul`** changes the **goal**: `(a + b) * c = a * c + b * c`. Placeholders: `{R : Type}
[CommRing R] (a b c : R)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R13 · `Finset.sum_add_distrib`** changes the **goal**: `∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x`.
With `simp only` it applies at both levels of the double sum, giving two double sums. Placeholders:
`{α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, (f x + g x))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R14 · `have h1 := sum_probability_eq_one 𝓐 T`** changes the **context**: it adds
`h1 : ∑ i, 𝓐.probability T i = 1`. It needs `[Nonempty α]` and `[𝓐.IsFinite]`; the ensemble and the
temperature are explicit arguments. Placeholders: as in R1, plus `[Nonempty α]`, and `(G : Prop)` for
the goal. The new hypothesis contains a comma, so it is written here rather than in the table.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with `h1 : ∑ i, 𝓐.probability T i = 1` (above) added to the context |

**R15 · `congr 1`** changes the **goal list**: `a + b = c + d` becomes `a = c` and `b = d` (both named
`case e_a`). Each half of the sum is then a separate goal; focus each with `·`. `congr` closes a new goal on
its own when it is `rfl` or a hypothesis. Placeholders: `{R : Type} [CommRing R] (a b c d : R)`.

| Before | After |
|---|---|
| `⊢ a + b = c + d` | `⊢ a = c`, `⊢ b = d` |

**Goal 1** (the energy depends on the **outer** index): regroup (R16), pull the factor out of the inner
sum (R17), use `h2`, then R18.

**R16 · `simp only [← mul_assoc]`** changes the **goal**: `mul_assoc : a * b * c = a * (b * c)`; right to
left it regroups to the left. `*` groups to the left, so `a * b * c` is `(a * b) * c`. Placeholders:
`{R : Type} [CommRing R] (a b c : R)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R17 · `simp only [← Finset.mul_sum]`** changes the **goal**: `Finset.mul_sum : a * ∑ i ∈ s, f i =
∑ i ∈ s, a * f i`; right to left it pulls out a factor that does not depend on the summation index. It only
fires when the summand has the shape `a * f i` with `a` free of `i`, hence R16 first. Placeholders:
`{α R : Type} [Fintype α] [CommRing R] (a : R) (f : α → R)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R18 · `mul_one`** changes the **goal**: `a * 1 = a`. Placeholders: `{R : Type} [CommRing R] (a : R)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**W2** (R16, R17, then `simp only [hq, mul_one]`, with `hq : ∑ j, q j = 1`):

```lean-goal
⊢ ∑ i, ∑ j, a i * (p i * q j) = ∑ i, a i * p i
⊢ ∑ x, ∑ x_1, a x * p x * q x_1 = ∑ i, a i * p i
⊢ ∑ x, a x * p x * ∑ i, q i = ∑ i, a i * p i
```

**Goal 2** (the energy depends on the **inner** index): swap the two sums first (R19), so the index of the
energy is outer; then move `𝓒.probability` to the end of the product (R20) and finish as goal 1 with `h1`.

**R19 · `rw [Finset.sum_comm]`** changes the **goal**: `∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`.
Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∑ y, f x y)` | `⊢ P (∑ y, ∑ x, f x y)` |

**R20 · `simp only [mul_comm (f _)]`** changes the **goal**: `mul_comm a b : a * b = b * a`, with the first
factor's shape fixed to `f _`, so only products starting with `f …` are swapped, also under `∑`. A bare
`simp only [mul_comm]` would swap products you did not mean. Placeholders: `{α R : Type} [Fintype α]
[CommRing R] (f g : α → R)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x * g x)` | `⊢ P (∑ x, g x * f x)` |

**W3** (R19, R20, then R16, R17, `hp`, R18 in one `simp only`, with `hp : ∑ i, p i = 1`):

```lean-goal
⊢ ∑ i, ∑ j, b j * (p i * q j) = ∑ j, b j * q j
⊢ ∑ y, ∑ x, b y * (p x * q y) = ∑ j, b j * q j
⊢ ∑ x, ∑ x_1, b x * (q x * p x_1) = ∑ j, b j * q j
```

---

## Traps

- `rw [partitionFunction_of_fintype]` rewrites only the ensemble it meets first; `Z_mul` needs it three
  times (`rw [l, l, l]`), and `U_add` needs `meanEnergy_of_fintype` three times.
- The `IsFinite` instance of `𝓒 + 𝓒'` is anonymous (physlib proves it, unnamed). Never try to name or pass
  it; `rw`/`simp` find it by instance search.
- `↑T.β` is `1 / (k_B T)` (`Temperature.β_toReal`), but you never need to unfold it: `β` appears the same
  way on both sides of every equation here. Treat `-↑T.β` as a constant `a` in R6.
- `rw` cannot rewrite under a binder such as `∑ x, …` when the term mentions `x`. Inside sums use
  `simp only [...]` (or R4 to get a single summand first).
- `simp only [mul_comm]` with no argument can swap the wrong products; give the first factor (R20).
- `sum_probability_eq_one` needs `[Nonempty ι]`; that is why `U_add` has it and `Z_mul` does not.
- The `BANNED` names (physlib's own `…_add` lemmas for these exact facts, and `try?`) are rejected by the
  checker; the point is to derive them from the finite-sum formulas.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Z`, `Z_math`, `U` of a finite ensemble → sum | `rw [partitionFunction_of_fintype]`, `mathematicalPartitionFunction_of_fintype`, `meanEnergy_of_fintype` | R1, R9, R11 |
| sum over `ι × ι'` → double sum | `rw [Fintype.sum_prod_type]` | R2 |
| `(∑ f) * (∑ g)` ↔ `∑ ∑ f * g` | `rw [Finset.sum_mul_sum]` / `simp only [← Finset.sum_mul_sum]` | R3 |
| equal sums, summand by summand | `refine Finset.sum_congr rfl fun i _ => ?_` | R4 |
| energy of `𝓒 + 𝓒'` | `energy_add_apply` | R5 |
| distribute | `mul_add`, `add_mul` | R6, R12 |
| `exp (x + y)` | `Real.exp_add` | R7 |
| unfold `p` | `simp only [probability]` | R8 |
| `a / b * (c / d)` | `div_mul_div_comm` | R10 |
| `∑ (f + g)` → `∑ f + ∑ g` | `Finset.sum_add_distrib` | R13 |
| `∑ p = 1` | `have h := sum_probability_eq_one 𝓒 T` | R14 |
| split `a + b = c + d` | `congr 1` | R15 |
| regroup / pull a factor out of `∑` | `simp only [← mul_assoc, ← Finset.mul_sum]` | R16, R17 |
| `a * 1` | `mul_one` | R18 |
| swap a double sum | `rw [Finset.sum_comm]` | R19 |
| swap one kind of product | `simp only [mul_comm (f _)]` | R20 |
| see the state | infoview | |
