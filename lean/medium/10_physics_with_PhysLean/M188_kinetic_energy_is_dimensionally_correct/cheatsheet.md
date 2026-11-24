# M188 · Kinetic energy is dimensionally correct: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). E125 (momentum) is the same question where the types
do the work; it is not needed here. **New here:** physlib's dimensions (`Dimension`, `M𝓭 L𝓭 T𝓭`),
quantities tagged with a dimension (`WithDim d ℝ`), unit systems (`LTMCTUnitChoices`), unit conversion
(`scaleUnit`) and its scale factors (`dimScale`); Mathlib's non-negative reals `NNReal`, monoid
homomorphisms `→*`, and the tactics `field_simp`, `linear_combination`.

The physics: a unit system `u` fixes a unit of length, time, mass, charge and temperature. A quantity of
dimension `d = M^a L^b T^c …` measured as the number `x` in `u1` is the number `s · x` in `u2`, where the
scale factor is `s = (u1.dimScale u2) d = (ℓ₁/ℓ₂)^b (τ₁/τ₂)^c (μ₁/μ₂)^a ⋯ > 0` (`ℓᵢ, τᵢ, μᵢ`: the length,
time and mass units of `uᵢ`, each measured in one fixed reference unit). A relation between raw numbers is
*dimensionally correct* when it holds in one unit system iff it holds in every other. For
`E = ½ m v²` with `E : M L² T⁻²`, `m : M`, `v : L T⁻¹`, both sides pick up the same factor
`s_M s_L² s_T⁻²` (`s_X := (u2.dimScale u1) X`), which can be cancelled because it is nonzero.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[UnitDependent M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`); `1/2 : ℝ` is real division, not `Nat` division |
| `Dimension LTMCTDimensionBase` | a physical dimension: a rational exponent for each base (Length, Time, Mass, Charge, Temperature). Dimensions form a commutative group under `*`. `Dimension B` (in R7, R10) is the same for any type `B` of base dimensions |
| `d * e`, `d⁻¹` (on dimensions) | add, negate the exponents: `L𝓭 * T𝓭⁻¹` is length per time |
| `M𝓭`, `L𝓭`, `T𝓭` | the base dimensions mass, length, time; `L𝓭 * T𝓭⁻¹` is velocity, `M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹` is energy |
| `WithDim d ℝ` | a real number tagged with dimension `d`; a structure with one field `val : ℝ` |
| `x.val`, `x.1` | the raw number inside `x : WithDim d ℝ` (`.1` is the same field) |
| `x * y` (on `WithDim`) | the product quantity: values multiply, dimensions multiply (`WithDim d1 ℝ → WithDim d2 ℝ → WithDim (d1 * d2) ℝ`) |
| `LTMCTUnitChoices` | a unit system: a choice of length, time, mass, charge and temperature unit |
| `UnitDependent M` | type class: `M` has a unit conversion `scaleUnit`. Met by `WithDim d ℝ`, by functions between such types, and (only on the input side) by functions into `Prop` |
| `scaleUnit u1 u2 x` | `x` converted from unit system `u1` to `u2` |
| `IsDimensionallyCorrect f` | `∀ u1 u2, scaleUnit u1 u2 f = f`: converting `f` changes nothing |
| `u1.dimScale u2` | dot notation for `LTMCTUnitChoices.dimScale u1 u2`, a monoid homomorphism `Dimension LTMCTDimensionBase →* NNReal`: dimension `d` ↦ its scale factor |
| `(u2.dimScale u1) M𝓭` | the scale factor `s_M` for mass from `u2` to `u1`; it is a positive `NNReal` |
| `M →* N` | a monoid homomorphism: `f (x * y) = f x * f y`, `f 1 = 1` (R11) |
| `NNReal`, `ℝ≥0` | the non-negative reals `{r : ℝ // 0 ≤ r}` (two spellings of one type) |
| `↑s` | `s : NNReal` cast to `ℝ` |
| `c • x` | scalar action: the `NNReal` number `c` times the real `x` (R13 makes it `↑c * x`) |
| `2⁻¹` | `simp`'s spelling of `1/2` (R6) |
| `x_1` | an auto-generated binder name after `simp`; `intro` gives it your name |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` |

---

## Part 1 · `kineticEnergy_isDimensionallyCorrect`

Statement: `IsDimensionallyCorrect KineticEnergy`, where `KineticEnergy m v E` is the proposition
`E.1 = 1/2 * m.1 * v.1 ^ 2` on the raw numbers. In words: for all unit systems `u1 u2` and quantities
`m v E`, the relation holds for the numbers converted `u2 → u1` iff it holds for the original numbers.

### Dimensional correctness → "rescaled relation ↔ relation"

`simp [funext_iff, KineticEnergy]` applies R1–R8 by itself (W1 shows the result on another relation).
Without `funext_iff` it stops after R1.

**R1 · `rw [isDimensionallyCorrect_fun_iff]`** changes the **goal**. The lemma is
`IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m`: convert the input
back to `u1`, apply `f`, convert the output to `u2`. Placeholders:
`{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)`. `KineticEnergy` is such an `f` with
`M1 = WithDim M𝓭 ℝ` and `M2` the type of functions of `v` and `E`.

| Before | After |
|---|---|
| `⊢ IsDimensionallyCorrect f` | `⊢ ∀ (u1 u2 : LTMCTUnitChoices) (m : M1), scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m` |

**R2 · `rw [funext_iff]`** changes the **goal**: `funext_iff : f = g ↔ ∀ x, f x = g x`. After R1 the two
sides are functions of `v` (then of `E`), so this is used twice. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `⊢ ∀ (x : α), f x = g x` |

**R3 · `rw [scaleUnit_apply_fun]`** changes the **goal**:
`scaleUnit u1 u2 f m = scaleUnit u1 u2 (f (scaleUnit u2 u1 m))` when the output type also has units.
Placeholders: `{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices) (f : M1 → M2) (m : M1)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 f m)` | `⊢ P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))` |

**R4 · `rw [scaleUnit_apply_fun_left]`** changes the **goal**: the same for a function into a type with no
units, such as `Prop`: `scaleUnit u1 u2 f m = f (scaleUnit u2 u1 m)`. This is the last argument `E` of
`KineticEnergy`. Placeholders: `{M1 : Type} [UnitDependent M1] (f : M1 → Prop) (m : M1)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 f m)` | `⊢ P (f (scaleUnit u2 u1 m))` |

**R5 · `rw [eq_iff_iff]`** changes the **goal**: `eq_iff_iff : (p = q) ↔ (p ↔ q)` for propositions. After
R1–R4 the goal is an equation between two `Prop`s. Placeholders: `(p q : Prop)`.

| Before | After |
|---|---|
| `⊢ p = q` | `⊢ p ↔ q` |

**R6 · `rw [one_div]`** changes the **goal**: `one_div : 1 / a = a⁻¹`. This is why `1/2` appears as `2⁻¹`.
Placeholders: `{α : Type} [DivInvMonoid α] (a : α)` (α has `*`, `/` and `⁻¹`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (1 / a)` | `⊢ P a⁻¹` |

**R7 · `rw [val_pow_two_eq_mul]`** changes the **goal**: `x.val ^ 2 = (x * x).val`, a square of a raw
number becomes the value of a product quantity, which `scaleUnit` can then act on. Placeholders:
`{B : Type} {d : Dimension B} (x : WithDim d ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x.val ^ 2)` | `⊢ P (x * x).val` |

**R8 · `rw [DMul.hMul_scaleUnit]`** changes the **goal**:
`scaleUnit u1 u2 x * scaleUnit u1 u2 y = scaleUnit u1 u2 (x * y)` (converting commutes with products).
Placeholders: `(d1 d2 : Dimension LTMCTDimensionBase) (x : WithDim d1 ℝ) (y : WithDim d2 ℝ)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 x * scaleUnit u1 u2 y)` | `⊢ P (scaleUnit u1 u2 (x * y))` |

After `simp [funext_iff, KineticEnergy]` and `intro u1 u2 m v E` the goal is
`(scaleUnit u2 u1 E).val = 2⁻¹ * (scaleUnit u2 u1 m).val * (scaleUnit u2 u1 (v * v)).val ↔ E.val = 2⁻¹ * m.val * (v * v).val`.

### Rescaled values → real numbers times scale factors

Pass R9–R16 together to one `simp only [...]`. Afterwards every rescaled value is a product of real casts
`↑((u2.dimScale u1) X)` and their inverses, times a raw value.

**R9 · `rw [WithDim.scaleUnit_val]`** changes the **goal**:
`(scaleUnit u1 u2 x).val = (u1.dimScale u2) d • x.val`. Placeholders:
`(d : Dimension LTMCTDimensionBase) (u1 u2 : LTMCTUnitChoices) (x : WithDim d ℝ)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 x).val` | `⊢ P ((u1.dimScale u2) d • x.val)` |

**R10 · `rw [WithDim.withDim_hMul_val]`** changes the **goal**: `(x * y).val = x.val * y.val`.
Placeholders: `{B : Type} {d1 d2 : Dimension B} (x : WithDim d1 ℝ) (y : WithDim d2 ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x * y).val` | `⊢ P (x.val * y.val)` |

**R11 · `rw [map_mul]`** changes the **goal**: `f (x * y) = f x * f y` for a monoid hom. With
`f = u2.dimScale u1` it splits the factor of `M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹` into five factors.
Placeholders: `{M N : Type} [MulOneClass M] [MulOneClass N] (f : M →* N) (x y : M)` (`MulOneClass`: a `*`
with unit `1`; `Dimension _` and `NNReal` qualify).

| Before | After |
|---|---|
| `⊢ P (f (x * y))` | `⊢ P (f x * f y)` |

**R12 · `rw [map_inv]`** changes the **goal**: `f a⁻¹ = (f a)⁻¹` for a monoid hom out of a group.
Placeholders: `{G H : Type} [Group G] [DivisionMonoid H] (f : G →* H) (a : G)` (`Dimension _` is a group;
`NNReal` is a `DivisionMonoid`, a monoid with an inverse satisfying `(a * b)⁻¹ = b⁻¹ * a⁻¹`).

| Before | After |
|---|---|
| `⊢ P (f a⁻¹)` | `⊢ P (f a)⁻¹` |

**R13 · `rw [NNReal.smul_def]`** changes the **goal**: `c • x = ↑c • x`, the `NNReal` scalar becomes a real.
Placeholders: `(c : NNReal) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (c • x)` | `⊢ P (↑c • x)` |

**R14 · `rw [smul_eq_mul]`** changes the **goal**: `a • b = a * b` when scalar and vector are in the same
type. Placeholders: `{α : Type} [Mul α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R15 · `rw [NNReal.coe_mul]`** changes the **goal**: `↑(r * s) = ↑r * ↑s`. Placeholders: `(r s : NNReal)`.

| Before | After |
|---|---|
| `⊢ P ↑(r * s)` | `⊢ P (↑r * ↑s)` |

**R16 · `rw [NNReal.coe_inv]`** changes the **goal**: `↑r⁻¹ = (↑r)⁻¹`. Placeholders: `(r : NNReal)`.

| Before | After |
|---|---|
| `⊢ P ↑r⁻¹` | `⊢ P (↑r)⁻¹` |

### Scale factors are nonzero

**R17 · `have hpos := dimScale_pos u1 u2 d`** changes the **context**: `dimScale_pos : 0 < (u1.dimScale u2) d`
(full name `LTMCTUnitChoices.dimScale_pos`; the `open` line lets you drop the prefix).
Placeholders: `(u1 u2 : LTMCTUnitChoices) (d : Dimension LTMCTDimensionBase)`. In this exercise the factors
are `(u2.dimScale u1) X`, so the arguments are `u2 u1`, in that order.

| Before | After |
|---|---|
| `⊢ G` | `hpos : 0 < (u1.dimScale u2) d ⊢ G` |

**R18 · `have h := hs.ne'`** changes the **context**: `LT.lt.ne' : a < b → b ≠ a`, so `0 < s` gives `s ≠ 0`.
Combine with R17: `have hM := (dimScale_pos u2 u1 M𝓭).ne'`. Placeholders: `(s : NNReal) (hs : 0 < s)`.

| Before | After |
|---|---|
| `hs : 0 < s ⊢ G` | `h : s ≠ 0 ⊢ G` |

### Proving the `↔`

**R19 · `constructor`** on `A ↔ B` changes the **goal list**: two goals, the forward and the backward
implication. Follow with `<;> intro h` to name the assumption in both. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R20 · `field_simp at h`** changes the **context**: it cancels factors it knows are nonzero from both sides
of `h`, clears inverses, and normalises. It uses the `≠ 0` facts in the context; a fact `s ≠ 0` about
`s : NNReal` also covers the cast `↑s : ℝ`. It also writes `a * a` as `a ^ 2` and moves numerals such as
`2` to the other side, so check the new `h` in the infoview before the next step. Placeholders: `(s : NNReal) (hs : s ≠ 0) (x y : ℝ)`.

| Before | After |
|---|---|
| `h : ↑s * x = 2⁻¹ * (↑s * y) ⊢ G` | `h : x * 2 = y ⊢ G` |

**R21 · `linear_combination h / 2`** **closes** the goal `a = b` when `a - b - (lhs(h) - rhs(h)) / 2 = 0` is a
ring identity (checked by `ring`). Use it when `field_simp at h` left `h` in a different but equivalent
form: `ring` treats `a ^ 2` and `a * a` as equal, so the leftover `v.val * v.val` in the goal is no obstacle.
Placeholders: `(x y : ℝ) (h : x * 2 = y)`.

| Before | After |
|---|---|
| `⊢ x = 2⁻¹ * y` | closed |

**R22 · `field_simp`** **closes** a goal that becomes an identity after cancelling nonzero factors. In the
backward direction, `rw [h]` first replaces `E.val` by the right side of `h`; then `field_simp` finishes.
Placeholders: `(s t : NNReal) (ht : t ≠ 0) (y : ℝ)`.

| Before | After |
|---|---|
| `⊢ ↑s * (↑t)⁻¹ * (2⁻¹ * y) = 2⁻¹ * (↑s * y) * (↑t)⁻¹` | closed |

### Worked combination (W1, on an object that is not the exercise's)

**W1.** `Distance v t x := x.1 = v.1 * t.1` with `v : L T⁻¹`, `t : T`, `x : L`. The states after
`simp [funext_iff, Distance]` (R1–R8), `intro u1 u2 v t x`, `simp only [R9–R16]`, and in case `mp` after
R17–R20:

```lean-goal
⊢ IsDimensionallyCorrect Distance
⊢ ∀ (u1 u2 : LTMCTUnitChoices) (m : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (x : WithDim T𝓭 ℝ) (x_1 : WithDim L𝓭 ℝ), (scaleUnit u2 u1 x_1).val = (scaleUnit u2 u1 (m * x)).val ↔ x_1.val = (m * x).val
⊢ (scaleUnit u2 u1 x).val = (scaleUnit u2 u1 (v * t)).val ↔ x.val = (v * t).val
⊢ ↑((u2.dimScale u1) L𝓭) * x.val = ↑((u2.dimScale u1) L𝓭) * (↑((u2.dimScale u1) T𝓭))⁻¹ * ↑((u2.dimScale u1) T𝓭) * (v.val * t.val) ↔ x.val = v.val * t.val
⊢ x.val = v.val * t.val
```

Here `field_simp at h` already makes `h` the goal. In the exercise it leaves `h` as a multiple of the goal
(the `2⁻¹` is cleared), so R21 finishes instead of `exact h`.

---

## Traps

- `simp [KineticEnergy]` without `funext_iff` stops at an equation between functions and reports
  `KineticEnergy` as unused. Give it both.
- The factors in the goal are `(u2.dimScale u1) X`, not `(u1.dimScale u2) X`: `isDimensionallyCorrect_fun_iff`
  converts the inputs with `scaleUnit u2 u1`. A fact `dimScale_pos u1 u2 _` is about a different number and
  `field_simp` cannot use it.
- Record the nonzero facts for all three bases `M𝓭`, `L𝓭`, `T𝓭` before `field_simp`; one missing fact and
  that factor stays in `h`.
- Do `field_simp` after the `simp only [R9–R16]` step: while a factor is still `(u2.dimScale u1) (L𝓭 * T𝓭⁻¹)`
  or a cast of a product, your facts about `L𝓭` and `T𝓭` do not match it.
- `simp` writes `1/2` as `2⁻¹` and `v.1 ^ 2` as `(v * v).val`; state your own `have`s in that form or
  `rw` will not find them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `IsDimensionallyCorrect f` → rescaled `↔` original | `simp [funext_iff, f]` | R1–R8 |
| name the quantities | `intro u1 u2 m v E` | |
| rescaled values → factors × values | `simp only [WithDim.scaleUnit_val, WithDim.withDim_hMul_val, map_mul, map_inv, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]` | R9–R16 |
| factor is nonzero | `have hM := (dimScale_pos u2 u1 M𝓭).ne'` | R17, R18 |
| split `↔` | `constructor <;> intro h` | R19 |
| cancel nonzero factors in `h` | `field_simp at h` | R20 |
| goal = scalar multiple of `h` | `linear_combination h / 2` | R21 |
| substitute, then cancel | `rw [h]; field_simp` | R22 |
| see the state | infoview | |
