# H094 · Thermal quantum oscillator (Planck): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` and
`Temperature`; Mathlib's real exponential, the counting measure and its integral, infinite sums (`tsum`) and
`Summable`, geometric series; the tactics `linarith`, `nlinarith`, `positivity`, `field_simp`,
`linear_combination`, `generalize`, `set`, `simp_rw`, `simpa`.

**The physics.** A canonical ensemble is a set of microstates `i` with energies `E_i`, in contact with a heat
bath at temperature `T`. With `β = 1 / (k_B T)` (`k_B` Boltzmann's constant), the *Boltzmann weight* of `i` is
$e^{-\beta E_i}$, the *partition function* is $Z = \sum_i e^{-\beta E_i}$, and the *mean energy* is
$\langle E\rangle = \sum_i E_i e^{-\beta E_i} / Z$. For the oscillator, $E_n = \varepsilon(n + \tfrac12)$. Put
$x = \beta\varepsilon$, $c = e^{-x/2}$, $r = e^{-x} = c^2$; then $e^{-\beta E_n} = c\,r^n$ and

$$Z = \sum_{n\ge0} c\,r^n = \frac{c}{1-r} = \frac{1}{e^{x/2} - e^{-x/2}} = \frac{1}{2\sinh(x/2)},\qquad
\langle E\rangle = \frac{\varepsilon c \sum n r^n + \tfrac{\varepsilon c}{2}\sum r^n}{c\sum r^n}
= \frac{\varepsilon r}{1-r} + \frac{\varepsilon}{2} = \frac{\varepsilon}{e^{x}-1} + \frac{\varepsilon}{2},$$

using $\sum_{n\ge0} r^n = (1-r)^{-1}$ and $\sum_{n\ge0} n r^n = r/(1-r)^2$ for $0 \le r < 1$.

**How physlib encodes it.** `CanonicalEnsemble ι` is a structure: a type of microstates `ι` with a measure
`μ` on it (sums over a discrete set are integrals against the *counting measure*, which gives every point mass
1), `energy : ι → ℝ`, and `dof`, `phaseSpaceunit` (which make `Z` dimensionless: `Z = Z_math / phaseSpaceunit ^ dof`;
here `dof = 0`). `Temperature` is a structure with one field `val : ℝ≥0`; `T.β : ℝ≥0` is `1 / (k_B T)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` with `g : … → G` is an arbitrary goal for entries that only add a fact.
- Placeholders are written as Lean binders. `{ι : Type} [MeasurableSpace ι]` is any type of microstates with a
  σ-algebra (the bracket is a *type class* requirement; `ℕ` meets it with "every set is measurable").
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `rexp x` | `Real.exp x = eˣ`, the real exponential (Lean prints `Real.exp` as `rexp`) |
| `sinh x`, `cosh x` | `Real.sinh`, `Real.cosh` (with `open Real`) |
| `ℝ≥0` | `NNReal`, the nonnegative reals: a real number bundled with a proof that it is `≥ 0` |
| `T.val`, `T.β` | the temperature and `β = 1/(k_B T)`, both in `ℝ≥0` |
| `↑T.β` | `(T.β : ℝ)`, the cast `ℝ≥0 → ℝ` (it forgets the proof). `↑n` for `n : ℕ` is the cast `ℕ → ℝ` |
| `CanonicalEnsemble ℕ` | physlib's structure type of canonical ensembles whose microstates are `n : ℕ` |
| `Temperature` | physlib's structure of temperatures, with one field `val : ℝ≥0` |
| `𝓒.partitionFunction T`, `𝓒.meanEnergy T` | `Z` and `⟨E⟩` of the ensemble `𝓒` at temperature `T` (unfold with R18, R35) |
| `𝓒.mathematicalPartitionFunction T` | `Z_math = ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ` (R19); `Z = Z_math / 𝓒.phaseSpaceunit ^ 𝓒.dof` |
| `(qho ε).energy n` | field `energy` of the structure `qho ε`, applied to `n` |
| `(qho ε).μ` | its measure; it is `Measure.count` by definition (`rfl`), but `rw` will not see that (R26) |
| `Measure.count` | the counting measure: `count S` = number of elements of `S` (possibly `∞`) |
| `Measure ℕ` | the type of measures on `ℕ`; `(Measure.count : Measure ℕ)` fixes which counting measure is meant |
| `μ.real S` | the measure of `S` as a real number (`(μ S).toReal`); `Measure.count.real {x} = 1` |
| `∫ (i : ℕ), f i ∂μ` | the (Bochner) integral of `f` against `μ`; against `count` it is a sum (R5) |
| `Integrable f μ` | `f` is measurable and `∫ ‖f‖ ∂μ < ∞`; for `count`: `∑ ‖f n‖` converges (R6) |
| `∑' (n : ℕ), f n` | `tsum f`, the sum of the series. **It is `0` when `f` is not summable**, so every lemma needs `Summable` |
| `Summable f` | the series `∑ f n` converges (unconditionally; for real series: absolutely) |
| `‖r‖`, `\|r\|` | norm and absolute value; for `r : ℝ` they are equal (R9) |
| `a • y` | scalar multiplication; for `a y : ℝ` it is `a * y` |
| `b⁻¹` | the inverse `1 / b` (for `b : ℝ`, Mathlib sets `0⁻¹ = 0`) |
| `-x / 2`, `-(x / 2)` | `(-x) / 2` and `-(x / 2)`: equal numbers, different terms, so `rw` treats them as different (R30) |
| `?_` (in a term) | a hole you fill later: it becomes a new goal after the current one (R5) |
| `r : ℝ := e` (context) | a local definition made by `set` (R36): `r` is `e`, by definition |
| `x✝`, `inst✝` | names Lean made up; you cannot refer to them |

---

## Part 1 · `weight_eq` (milestone)

Statement: `exp (-β E_n) = e^{-βε/2} · (e^{-βε})ⁿ`. Fold the right side into one exponential, unfold the
energy, and compare the arguments.

**R1 · `rw [← Real.exp_nat_mul]`** changes the **goal**. The lemma is `Real.exp_nat_mul : rexp (↑n * x) = rexp x ^ n`;
`←` folds a power of `rexp` into one `rexp`. Note the `↑n *` comes first. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x ^ n)` | `⊢ P (rexp (↑n * x))` |

**R2 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is `Real.exp_add : rexp (x + y) = rexp x * rexp y`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x * rexp y)` | `⊢ P (rexp (x + y))` |

**R3 · `simp only [D]`** changes the **goal**: for a definition `D` built with `where`, `(D a).field` becomes that
field's body. Placeholders: the guide's toy ensemble `ladder a` (energy `a * n`), `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((ladder a).energy n)` | `⊢ P (a * ↑n)` |

**R4 · `ring_nf`** **closes** `rexp A = rexp B` when `A` and `B` are equal as ring expressions: it normalises
the ring subterms inside `rexp (…)` on both sides, and identical sides close the goal. (When they do not become
identical, it leaves the normalised goal: TACTIC_STATES.) Placeholders: `(x y : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ rexp (-(x * (↑n + y))) = rexp (-(y * x) + ↑n * -x)` | no goals |

**W1** (guide): the weight of `ladder a` is a power, by R1, R3, R4:

```lean-goal
⊢ rexp (-b * (ladder a).energy n) = rexp (-(b * a)) ^ n
⊢ rexp (-b * (ladder a).energy n) = rexp (↑n * -(b * a))
⊢ rexp (-b * (a * ↑n)) = rexp (↑n * -(b * a))
```

---

## Part 2 · `integral_count_eq_tsum` (milestone)

Statement: for `f : ℕ → ℝ` with `Summable f`, `∫ n, f n ∂count = ∑' n, f n`.

**R5 · `rw [integral_countable hi]`** changes the **goal**. The lemma is
`MeasureTheory.integral_countable : Integrable f μ → ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x` (on a countable type
where points are measurable, such as `ℕ`). Pass `(… ?_)` instead of `hi` to prove integrability later: the `?_`
becomes an extra goal after the main one. Placeholders: `(f : ℕ → ℝ) (hi : Integrable f Measure.count)`.

| Before | After |
|---|---|
| `hi : Integrable f Measure.count ⊢ P (∫ (n : ℕ), f n ∂Measure.count)` | `⊢ P (∑' (x : ℕ), Measure.count.real {x} • f x)` |

**R6 · `integrable_count_iff.mpr`** changes the **goal**. The lemma is
`MeasureTheory.integrable_count_iff : Integrable f Measure.count ↔ Summable fun x => ‖f x‖`; `.mpr` is the `←`
direction of the `↔`. Placeholders: `(f : ℕ → ℝ)`.

| Before | After `apply integrable_count_iff.mpr` |
|---|---|
| `⊢ Integrable f Measure.count` | `⊢ Summable fun x => ‖f x‖` |

**R7 · `simp [Measure.real]`** changes the **goal**: unfolding `μ.real S = (μ S).toReal`, `simp` knows
`count {x} = 1` and `1 • y = y`. Placeholders: `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), Measure.count.real {n} • f n)` | `⊢ P (∑' (n : ℕ), f n)` |

**R8 · `have ha := hf.abs`** changes the **context**. The lemma is `Summable.abs : Summable f → Summable fun x => |f x|`;
`hf.abs` is `Summable.abs hf` (dot notation: `hf : Summable f`, so Lean looks in namespace `Summable`). The
context gains `ha : Summable fun x => |f x|`; the goal stays. Placeholders: `(f : ℕ → ℝ) (hf : Summable f)`.

| Before | After |
|---|---|
| `hf : Summable f ⊢ G` | `⊢ G` (plus `ha`) |

**R9 · `rw [Real.norm_eq_abs]`** changes the **goal**. The lemma is `Real.norm_eq_abs : ‖r‖ = |r|`.
Placeholders: `(r : ℝ)`.

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

**R10 · `simpa [l] using e`** **closes** the goal: it simplifies both the goal and the type of `e` with `simp [l]`
and closes the goal when they agree. Here it turns `‖·‖` into `|·|` (R9) in the goal so that `ha` fits.
Placeholders: `(f : ℕ → ℝ)`, `ha : Summable fun n => |f n|`.

| Before | After `simpa [Real.norm_eq_abs] using ha` |
|---|---|
| `⊢ Summable fun n => ‖f n‖` | no goals |

**W2** (guide): `∫ n, rⁿ ∂count = (1 - r)⁻¹` by R5 with R6 as `?_`, then R7 + R15 on the first goal and
R8, R10 on the second:

```lean-goal
⊢ ∫ (n : ℕ), r ^ n ∂Measure.count = (1 - r)⁻¹
⊢ ∑' (x : ℕ), Measure.count.real {x} • r ^ x = (1 - r)⁻¹
⊢ Summable fun x => ‖r ^ x‖
```

---

## Part 3 · `tsum_weight` (milestone)

Statement: for `x > 0`, `∑' n, e^{-x/2} (e^{-x})ⁿ = e^{-x/2} / (1 - e^{-x})`.

**R11 · `Real.exp_lt_one_iff.mpr`** changes the **goal**. The lemma is `Real.exp_lt_one_iff : rexp x < 1 ↔ x < 0`.
Write `Real.exp_lt_one_iff.mpr (by linarith)` to prove a fact `rexp (-x) < 1` in one line. Placeholders: `(x : ℝ)`.

| Before | After `apply Real.exp_lt_one_iff.mpr` |
|---|---|
| `⊢ rexp x < 1` | `⊢ x < 0` |

**R12 · `linarith`** **closes** a goal `t < 0`, `t ≤ s`, `t = s`, `t ≠ s` (or `False`) that follows from the
hypotheses by adding up linear (in)equalities with nonnegative coefficients. Products of unknowns count as atoms.
`linarith [t₁]` also uses the fact `t₁` (R43).

| Before | After |
|---|---|
| `hx : 0 < x ⊢ -x < 0` | no goals |

**R13 · `Real.exp_pos`** changes the **context** (as a `have`). The lemma is `Real.exp_pos x : 0 < rexp x`;
`.le` turns `a < b` into `a ≤ b`. Placeholders: `(x : ℝ)`.

| Before | After `have h0 := (Real.exp_pos x).le` |
|---|---|
| `⊢ G` | `h0 : 0 ≤ rexp x ⊢ G` |

**R14 · `rw [tsum_mul_left]`** changes the **goal**. The lemma is `tsum_mul_left : ∑' n, a * f n = a * ∑' n, f n`.
It needs no summability (both sides are `0` when the series diverges and `a ≠ 0`). Placeholders: `(a : ℝ) (f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), a * f n)` | `⊢ P (a * ∑' (x : ℕ), f x)` |

**R15 · `rw [tsum_geometric_of_lt_one h0 h1]`** changes the **goal**. The lemma is
`tsum_geometric_of_lt_one : 0 ≤ r → r < 1 → ∑' n, r ^ n = (1 - r)⁻¹`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `h0 : 0 ≤ r, h1 : r < 1 ⊢ P (∑' (n : ℕ), r ^ n)` | `⊢ P (1 - r)⁻¹` |

**R16 · `div_eq_mul_inv`** changes the **goal**. The lemma is `div_eq_mul_inv a b : a / b = a * b⁻¹`.
`(div_eq_mul_inv a b).symm : a * b⁻¹ = a / b` closes such a goal with `exact`. Placeholders: `(a b : ℝ)`.

| Before | After `rw [div_eq_mul_inv]` |
|---|---|
| `⊢ P (a / b)` | `⊢ P (a * b⁻¹)` |

---

## Part 4 · `qho_partitionFunction`

Statement: `(qho ε).partitionFunction T = 1 / (2 sinh (βε / 2))` for `ε > 0`, `T > 0`.

### Unfolding `Z`

**R17 · `Temperature.beta_pos`** changes the **context**. The lemma is
`Temperature.beta_pos T : 0 < T.val → 0 < ↑T.β`. Placeholders: `(T : Temperature) (hT : 0 < T.val)`.

| Before | After `have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT` |
|---|---|
| `hT : 0 < T.val ⊢ G` | `hβ : 0 < ↑T.β ⊢ G` |

**R18 · `rw [partitionFunction_def]`** changes the **goal**. The lemma is
`CanonicalEnsemble.partitionFunction_def : 𝓒.partitionFunction T = 𝓒.mathematicalPartitionFunction T / 𝓒.phaseSpaceunit ^ 𝓒.dof`.
Placeholders: `{ι : Type} [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (T : Temperature)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.partitionFunction T)` | `⊢ P (𝓒.mathematicalPartitionFunction T / 𝓒.phaseSpaceunit ^ 𝓒.dof)` |

**R19 · `rw [mathematicalPartitionFunction_eq_integral]`** changes the **goal**. The lemma is
`CanonicalEnsemble.mathematicalPartitionFunction_eq_integral : 𝓒.mathematicalPartitionFunction T = ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ`.
Placeholders as in R18.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunction T)` | `⊢ P (∫ (i : ι), rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)` |

**R20 · `rw [show (D a).dof = 0 from rfl]`** changes the **goal**: `show t from e` is the term `e` with its type
stated as `t`; here `rfl` proves that a field of a concrete structure equals its value, and `rw` substitutes it.
Placeholders: `ladder a`, `(P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (ladder a).dof` | `⊢ P 0` |

**R21 · `rw [pow_zero]`, then `rw [div_one]`** change the **goal**: `pow_zero b : b ^ 0 = 1`, `div_one a : a / 1 = a`.
Placeholders: `(a b : ℝ)`.

| Before | After `rw [pow_zero]` | After `rw [div_one]` |
|---|---|---|
| `⊢ P (a / b ^ 0)` | `⊢ P (a / 1)` | `⊢ P a` |

### Naming `x = βε`, summability facts

**R22 · `generalize hx : e = x`** changes the **goal and the context**: every occurrence of the term `e` in the
goal becomes a fresh variable `x`, and `hx : e = x` remembers what it was. Use `rw [← hx]` to go back when
proving a fact about `x`. Placeholders: `(b a : ℝ)`.

| Before | After `generalize hx : b * a = x` |
|---|---|
| `⊢ P (b * a)` | `x : ℝ, hx : b * a = x ⊢ P x` |

**R23 · `positivity`** **closes** `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from `+`, `*`, `/`, `^`, `rexp`,
casts, … of atoms it knows to be positive (numerals, `rexp _`, or an atom `a` with `0 < a` in the context).
Placeholders: `(b a : ℝ)`.

| Before | After |
|---|---|
| `hb : 0 < b, ha : 0 < a ⊢ 0 < b * a` | no goals |

**R24 · `summable_geometric_of_lt_one`** changes the **context**. The lemma is
`summable_geometric_of_lt_one : 0 ≤ r → r < 1 → Summable fun n => r ^ n`. Placeholders: `(r : ℝ)`.

| Before | After `have hs := summable_geometric_of_lt_one h0 h1` |
|---|---|
| `⊢ G` | `hs : Summable fun n => r ^ n ⊢ G` |

**R25 · `hf.mul_left a`** changes the **context**. The lemma is
`Summable.mul_left a : Summable f → Summable fun i => a * f i`. Placeholders: `(a : ℝ) (f : ℕ → ℝ)`.

| Before | After `have hs := hf.mul_left a` |
|---|---|
| `hf : Summable f ⊢ G` | `hs : Summable fun i => a * f i ⊢ G` |

### Rewriting the weight inside the integral

**R26 · `show G'`** changes the **goal** to `G'`, which must be equal to it *by definition*. Here it replaces
`∂(ladder a).μ` by `∂Measure.count` (the field's value), which `rw [integral_count_eq_tsum …]` needs to see
literally. A `_` in `G'` stands for the part you do not retype. Placeholders: `(a : ℝ) (f : ℕ → ℝ) (y : ℝ)`.

| Before | After `show ∫ n, f n ∂Measure.count = _` |
|---|---|
| `⊢ ∫ (n : ℕ), f n ∂(ladder a).μ = y` | `⊢ ∫ (n : ℕ), f n ∂Measure.count = y` |

**R27 · `simp_rw [hw]`** changes the **goal**: it rewrites with `hw : ∀ n, f n = g n` *under binders* such as
`∫ n, …` or `∑' n, …`. `rw [hw]` fails there, because the `n` inside `∫ n, f n` is bound and `rw` must pick one
value for it. `simp_rw [h₁, h₂]` rewrites with each in turn. Placeholders: `(f g : ℕ → ℝ)`, with
`hw : ∀ (n : ℕ), f n = g n` in the context.

| Before | After `simp_rw [hw]` |
|---|---|
| `⊢ P (∫ (n : ℕ), f n ∂Measure.count)` | `⊢ P (∫ (n : ℕ), g n ∂Measure.count)` |

**R28 · `rw [Real.sinh_eq]`** changes the **goal**. The lemma is `Real.sinh_eq x : sinh x = (rexp x - rexp (-x)) / 2`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (sinh x)` | `⊢ P ((rexp x - rexp (-x)) / 2)` |

### The algebra at the end

**R29 · `simp`** **closes** `rexp 0 = 1` (simp lemma `Real.exp_zero`). The usual way to prove
`rexp a * rexp b = 1` when `a + b = 0`: R2, then `ring_nf` (turns `rexp (a + b)` into `rexp 0`), then `simp`.

| Before | After |
|---|---|
| `⊢ rexp 0 = 1` | no goals |

**R30 · `rw [show a = b by ring]`** changes the **goal**: it replaces the subterm `a` by the ring-equal `b`, to make
the goal's text match a hypothesis (`rw [h]` needs a literal match: `-(x / 2)` and `-x / 2` are different text).
Placeholders: `(x : ℝ)`.

| Before | After `rw [show -(x / 2) = -x / 2 by ring]` |
|---|---|
| `⊢ P (-(x / 2))` | `⊢ P (-x / 2)` |

**R31 · `generalize e = c at h₀ ⊢`** changes the **goal and the context**: `e` becomes a fresh `c` in the goal
and in the listed hypotheses; no equation is kept, so state every fact you need about `e` *before*. Turning
`rexp (-x / 2)` into a plain `c` lets `field_simp` and `ring` treat it as a variable. Placeholders: `(x : ℝ)`.
The guide runs `generalize rexp x = c at h0 ⊢`:

| Before | After |
|---|---|
| `h0 : 0 < rexp x ⊢ P (rexp x)` | `c : ℝ, h0 : 0 < c ⊢ P c` |

**R32 · `nlinarith`** **closes** what `linarith` (R12) closes, after also adding pairwise products of hypotheses
(and squares), so it handles `c * c`, `c ^ 2`. `nlinarith [t₁, t₂]` adds facts. A `≠` goal works too
(`1 - c ^ 2 ≠ 0` from `0 < c < 1`). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h0 : 0 < a, h1 : a < 1 ⊢ a * a < 1` | no goals |

**R33 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (from
`≠ 0` hypotheses, or numerals) and leaves a goal without `/`. It may reorder factors and write `c * c` as `c ^ 2`.
Placeholders: `(a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0)`.

| Before | After |
|---|---|
| `hb : b ≠ 0, hd : d ≠ 0 ⊢ a / b = c / d` | `⊢ a * d = b * c` |

**R34 · `linear_combination e`** **closes** `L = R` when `L - R - k·(lhs - rhs) = 0` holds by `ring`, for
`e = k * h` with `h : lhs = rhs`. Placeholders: `(a b : ℝ) (h : a * b = 1)`.

| Before | After `linear_combination b * h` |
|---|---|
| `h : a * b = 1 ⊢ a * b * b = b` | no goals |

**W3** (guide, `cosh` instead of `sinh`): `e^{-y} / (1 + e^{-y}e^{-y}) = 1 / (2 cosh y)` by `Real.cosh_eq`,
`hcc : rexp y * rexp (-y) = 1` (R2, R29), R31, `positivity` for the `≠ 0` facts, R33, R34:

```lean-goal
⊢ rexp (-y) / (1 + rexp (-y) * rexp (-y)) = 1 / (2 * cosh y)
⊢ rexp (-y) / (1 + rexp (-y) * rexp (-y)) = 1 / (2 * ((rexp y + rexp (-y)) / 2))
⊢ c / (1 + c * c) = 1 / (2 * ((rexp y + c) / 2))
⊢ c * (rexp y + c) = 1 + c ^ 2
```

---

## Part 5 · `qho_meanEnergy`

Statement: `(qho ε).meanEnergy T = ε / 2 + ε / (e^{βε} - 1)`. Same start as Part 4 (R17, R26, R27, R22, R23),
then a ratio of two series.

**R35 · `rw [meanEnergy_eq_ratio_of_integrals]`** changes the **goal**. The lemma is
`CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals : 𝓒.meanEnergy T = (∫ i, 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) / ∫ i, rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ`.
Placeholders as in R18.

| Before | After |
|---|---|
| `⊢ P (𝓒.meanEnergy T)` | `⊢ P ((∫ (i : ι), 𝓒.energy i * rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ) / ∫ (i : ι), rexp (-↑T.β * 𝓒.energy i) ∂𝓒.μ)` |

**R36 · `set r := e with hr`** changes the **goal and the context**: every `e` in the goal (and context) is shown as
`r`; the context gains the local definition `r : ℝ := e` and `hr : r = e`. Unlike R22, `r` still *is* `e`, so
lemmas about `e` apply to `r` directly (`Real.exp_pos _ : 0 < r`). Placeholders: `(x : ℝ)`.

| Before | After `set r := rexp (-x) with hr` |
|---|---|
| `⊢ P (rexp (-x))` | `r : ℝ := rexp (-x), hr : r = rexp (-x) ⊢ P r` |

**R37 · `rw [abs_of_nonneg ha]`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ a → |a| = a`.
Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

```lean-goal
⊢ P |a|
⊢ P a
```

**R38 · `rwa [l]`** **closes** the goal: `rw [l]`, then `assumption` (a hypothesis that is exactly the new goal).
With `h1 : a < 1`, `rwa [abs_of_nonneg ha]` closes the goal below. For `‖r‖ < 1`: `rwa [Real.norm_eq_abs, abs_of_nonneg hr0]`.

```lean-goal
⊢ |a| < 1
```

**R39 · `summable_pow_mul_geometric_of_norm_lt_one`**: the lemma is
`summable_pow_mul_geometric_of_norm_lt_one k : ‖r‖ < 1 → Summable fun n => ↑n ^ k * r ^ n`. With `k = 1`,
`simpa using …` (R10) removes the `^ 1` and **closes** the goal. Placeholders: `(r : ℝ) (hr : ‖r‖ < 1)`.

| Before | After `simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr` |
|---|---|
| `hr : ‖r‖ < 1 ⊢ Summable fun n => ↑n * r ^ n` | no goals |

**R40 · `hf.add hg`** changes the **context**. The lemma is
`Summable.add : Summable f → Summable g → Summable fun b => f b + g b`. Placeholders: `(f g : ℕ → ℝ)`.

| Before | After `have hs := hf.add hg` |
|---|---|
| `hf : Summable f, hg : Summable g ⊢ G` | `hs : Summable fun b => f b + g b ⊢ G` |

**R41 · `rw [hf.tsum_add hg]`** changes the **goal**. The lemma is
`Summable.tsum_add : Summable f → Summable g → ∑' b, (f b + g b) = ∑' b, f b + ∑' b, g b`. Placeholders: `(f g : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), (f n + g n))` | `⊢ P (∑' (b : ℕ), f b + ∑' (b : ℕ), g b)` |

**R42 · `rw [tsum_coe_mul_geometric_of_norm_lt_one hr]`** changes the **goal**. The lemma is
`tsum_coe_mul_geometric_of_norm_lt_one : ‖r‖ < 1 → ∑' n, ↑n * r ^ n = r / (1 - r) ^ 2`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑' (n : ℕ), ↑n * r ^ n)` | `⊢ P (r / (1 - r) ^ 2)` |

**R43 · `linarith [Real.add_one_lt_exp hx.ne']`** **closes** the goal. The lemma is
`Real.add_one_lt_exp : x ≠ 0 → x + 1 < rexp x`; `hx.ne'` turns `hx : 0 < x` into `x ≠ 0`
(`.ne` would give `0 ≠ x`). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ 0 < rexp x - 1` | no goals |

**W4** (guide): `∑' (a·n rⁿ + b rⁿ)` split and summed, by R24, R39, R25, R41, R14, then R42, R15:

```lean-goal
⊢ ∑' (n : ℕ), (a * (↑n * r ^ n) + b * r ^ n) = a * (r / (1 - r) ^ 2) + b * (1 - r)⁻¹
⊢ a * ∑' (x : ℕ), ↑x * r ^ x + b * ∑' (x : ℕ), r ^ x = a * (r / (1 - r) ^ 2) + b * (1 - r)⁻¹
```

---

## Traps

- `∑' n, f n` is `0` when `f` is not summable, so `tsum` lemmas that change the value (R15, R41, R42) and R5 take a
  `Summable`/`Integrable` argument. State those facts as `have`s first (R24, R25, R39, R40).
- `(qho ε).μ` is `Measure.count` only *by definition*: `rw [integral_count_eq_tsum …]` does not see it. Restate the
  goal with `show … ∂Measure.count …` (R26). The same holds for `(qho ε).energy n` (`fun n => rfl` proves its value)
  and `(qho ε).dof` (R20).
- `rw` cannot rewrite inside `∫ n, …` or `∑' n, …` with a hypothesis `∀ n, …`; use `simp_rw` (R27).
- `rw [h]` needs a literal match: `-(x / 2)` vs `-x / 2`, `rexp (↑n * a)` vs `rexp (a * ↑n)`. Fix with
  `rw [show a = b by ring]` (R30). `Real.sinh_eq` produces `rexp (-(x / 2))`.
- `generalize` keeps no equation unless you name one (`generalize hx : …`), and replaces only the goal and the
  hypotheses you list after `at`. Prove `0 < c`, `c < 1`, `rexp (x / 2) * c = 1` before naming `c` (R31).
- `simp` rewrites numerals inside sums: `(1 / 3) ^ n` becomes `(3 ^ n)⁻¹`, and then R15 no longer matches. Name
  the ratio first (R22, R36) and keep it a variable.
- `field_simp` needs every denominator's `≠ 0` fact in the context (`1 - c ^ 2 ≠ 0`, `rexp x - 1 ≠ 0` or `0 < …`);
  without it, the fraction stays.
- `linarith` treats `c * c` as an unknown; for facts that need products of hypotheses use `nlinarith` (R32).
- `↑T.β` is a cast from `ℝ≥0`: `positivity` knows `0 ≤ ↑T.β` but needs `hβ : 0 < ↑T.β` (R17) for `<`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `rexp a ^ n`, `rexp a * rexp b` → one `rexp` | `rw [← Real.exp_nat_mul, ← Real.exp_add]` | R1, R2 |
| unfold `(qho ε).energy n` | `simp only [qho]` or `fun n => rfl` | R3 |
| `rexp A = rexp B`, `A`, `B` ring-equal | `ring_nf` | R4 |
| `∫ · ∂count` → `∑'` | `rw [integral_countable (integrable_count_iff.mpr ?_)]` | R5, R6 |
| drop `count.real {x} •` | `simp [Measure.real]` | R7 |
| `Summable fun x => ‖f x‖` from `hf` | `simpa [Real.norm_eq_abs] using hf.abs` | R8–R10 |
| `rexp t < 1` | `Real.exp_lt_one_iff.mpr (by linarith)` | R11, R12 |
| `0 < rexp t`, `0 ≤ rexp t` | `Real.exp_pos t`, `(Real.exp_pos t).le` | R13 |
| constant out of a sum | `rw [tsum_mul_left]` | R14 |
| `∑' rⁿ`, `∑' n rⁿ` | `tsum_geometric_of_lt_one h0 h1`, `tsum_coe_mul_geometric_of_norm_lt_one hn` | R15, R42 |
| `a * b⁻¹ = a / b` | `(div_eq_mul_inv _ _).symm` | R16 |
| `0 < ↑T.β` | `Temperature.beta_pos T hT` | R17 |
| unfold `Z`, `Z_math`, `⟨E⟩` | `rw [partitionFunction_def, mathematicalPartitionFunction_eq_integral]`, `rw [meanEnergy_eq_ratio_of_integrals]` | R18, R19, R35 |
| `dof = 0` and `/ b ^ 0` | `rw [show (qho ε).dof = 0 from rfl, pow_zero, div_one]` | R20, R21 |
| name a subterm | `generalize hx : e = x`, `set r := e with hr`; in hypotheses too: R31's form | R22, R36, R31 |
| `0 < product` | `positivity` | R23 |
| summability | `summable_geometric_of_lt_one`, `.mul_left`, `.add`, `summable_pow_mul_geometric_of_norm_lt_one 1` | R24, R25, R40, R39 |
| `∂(qho ε).μ` → `∂Measure.count` | `show … = _` | R26 |
| rewrite under `∫ n,` / `∑' n,` | `simp_rw [h]` | R27 |
| `sinh` → exponentials | `rw [Real.sinh_eq]` | R28 |
| `rexp 0 = 1` | `simp` | R29 |
| match text up to ring laws | `rw [show a = b by ring]` | R30 |
| `≠ 0`, nonlinear bounds | `nlinarith [facts]` | R32 |
| clear denominators | `field_simp` | R33 |
| close with an equation | `linear_combination k * h`, or `nlinarith [h]` | R34, R32 |
| split `∑' (f + g)` | `rw [hf.tsum_add hg]` | R41 |
| `‖r‖ < 1` from `0 ≤ r < 1` | `rwa [Real.norm_eq_abs, abs_of_nonneg hr0]` | R9, R37, R38 |
| `0 < rexp x - 1` | `linarith [Real.add_one_lt_exp hx0.ne']` | R43 |
| see the state | infoview | |
