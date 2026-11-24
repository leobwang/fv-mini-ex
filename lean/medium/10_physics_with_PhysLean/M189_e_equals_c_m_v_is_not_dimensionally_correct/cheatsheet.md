# M189 · E = c·m·v is not dimensionally correct: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's units library: dimensions
(`Dimension LTMCTDimensionBase`, `M𝓭 L𝓭 T𝓭`), dimension-tagged numbers (`WithDim d ℝ`), unit systems
(`LTMCTUnitChoices`, `SI`, `SIPrimed`), unit conversion (`scaleUnit`, `dimScale`) and
`IsDimensionallyCorrect`; Mathlib's `NNReal`, `not_forall`, `funext_iff`, `norm_num`, `linarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[UnitDependent M]`
  is a requirement on `M` (a *type class*). Each entry says which types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

The physics, as physlib encodes it:

- A **dimension** `d : Dimension LTMCTDimensionBase` is a vector of five rational exponents
  (length ℓ, time t, mass m, charge q, temperature θ). `M𝓭`, `L𝓭`, `T𝓭` are plain `def`s:
  `M𝓭 = ofLTMCTDimensionBase 0 0 1 0 0`, `L𝓭 = ofLTMCTDimensionBase 1 0 0 0 0`,
  `T𝓭 = ofLTMCTDimensionBase 0 1 0 0 0`. Dimensions multiply by adding exponents, `d⁻¹` negates them, and
  `d.length`, `d.time`, `d.mass`, … read them off. So `M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹` (energy) is
  `(ℓ, t, m) = (2, −2, 1)` and `L𝓭 * T𝓭⁻¹` (velocity) is `(1, −1, 0)`.
- A **unit system** `u : LTMCTUnitChoices` picks a unit of length, time, mass, charge and temperature.
  `SI` is metres, seconds, kilograms, coulombs, kelvin. `SIPrimed` is SI with each unit scaled by a prime:
  length unit 2 m, time unit 3 s, mass unit 5 kg (charge 7 C, temperature 11 K).
- `WithDim d ℝ` is a real number tagged with dimension `d`: a structure with one field `val : ℝ`.
  `⟨a⟩` builds one; Lean prints it `{ val := a }`; `m.1` and `m.val` are its number.
- `scaleUnit u1 u2 m` takes the number of `m` in units `u1` and returns its number in units `u2`. For
  `m : WithDim d ℝ` it multiplies by the factor
  $\text{dimScale}\,u_1\,u_2\,d = (\ell_1/\ell_2)^{d.\text{length}}\,(t_1/t_2)^{d.\text{time}}\,(m_1/m_2)^{d.\text{mass}}\cdots$,
  where $\ell_i, t_i, m_i$ are the sizes of the units of `u_i`. This factor lives in `NNReal`
  (the reals `≥ 0`, often written `ℝ≥0`) and acts on `ℝ` by `•`.
- `IsDimensionallyCorrect x` means `∀ u1 u2, scaleUnit u1 u2 x = x`. For a function `f`, `scaleUnit`
  converts the inputs one way and the output back (R4), so a correct `f` "commutes with a change of
  units". A relation `M1 → M2 → M3 → Prop` has an output `Prop` with no units (R8): it is correct iff its
  truth value never changes when all its arguments are converted to another unit system.

Notation in the infoview:

| You see | It means |
|---|---|
| `Dimension LTMCTDimensionBase` | a dimension: five rational exponents (length, time, mass, charge, temperature) |
| `M𝓭`, `L𝓭`, `T𝓭` | the dimensions mass, length, time (`def`s; unfold with R11) |
| `d * d'`, `d⁻¹` | product of dimensions (exponents add), inverse (exponents negate) |
| `d.length`, `d.time`, `d.mass`, … | the exponent of that base in `d`, a `ℚ` (R12) |
| `WithDim d ℝ` | a real number tagged with dimension `d` |
| `{ val := a }` | the tagged number `⟨a⟩` |
| `m.val`, `m.1` | the number inside `m` |
| `LTMCTUnitChoices` | a choice of units (length, time, mass, charge, temperature) |
| `SI`, `SIPrimed` | SI units; SI units scaled by 2, 3, 5, 7, 11 |
| `scaleUnit u1 u2 x` | `x` given in units `u1`, re-expressed in units `u2` |
| `IsDimensionallyCorrect x` | `∀ u1 u2, scaleUnit u1 u2 x = x` (R1 for functions) |
| `UnitDependent M` | type class: `scaleUnit` is defined on `M` |
| `(u1.dimScale u2) d` | the conversion factor for dimension `d`, an `NNReal` |
| `NNReal` | real numbers `≥ 0`; `↑c : ℝ` is `c : NNReal` cast to `ℝ` |
| `c • x` | scalar `c` acting on `x` (here: multiplication after a cast) |
| `ofLTMCTDimensionBase ℓ t m q θ` | the dimension with those five exponents |
| `2 ^ ↑d.length` | `NNReal` power with a real exponent (the rational exponent cast to `ℝ`) |
| `∃ x x_1 x_2 …` | the witnesses `simp` names after pushing `¬` through `∀ u1 u2 m …` |
| `A = B` with `A B : Prop` | an equation of propositions: `A ↔ B` (R15) |
| `case h` | the goal left after `use` |

---

## Part 1 · `wrong_not_isDimensionallyCorrect`

Statement: for `c : ℝ` with `hc : c ≠ 0`, the relation `Wrong c m v E := (E.1 = c * m.1 * v.1)` is not
dimensionally correct. So you must exhibit two unit systems and values `m, v, E` where the relation's
truth value changes under conversion.

### From "dimensionally correct" to a counterexample goal

**R1 · `isDimensionallyCorrect_fun_iff`** changes the **goal**: correctness of a function becomes a
statement about all unit systems and all inputs. Lemma:
`IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m`. Placeholders:
`{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)`; `UnitDependent` means "`scaleUnit`
is defined on it": `WithDim d ℝ`, functions into a `UnitDependent` type, and functions into `Prop` qualify.

| Before | After |
|---|---|
| `⊢ ¬IsDimensionallyCorrect f` | `⊢ ¬∀ (u1 u2 : LTMCTUnitChoices) (m : M1), scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m` |

**R2 · `not_forall`** changes the **goal**: `(¬ ∀ x, p x) ↔ ∃ x, ¬ p x`. Placeholders:
`{α : Type} (p : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∀ (x : α), p x` | `⊢ ∃ x, ¬p x` |

**R3 · `funext_iff`** changes the **goal**: `f = g ↔ ∀ x, f x = g x`. Here `f m` is itself a function of the
next argument, so this exposes one more argument. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ ¬f = g` | `⊢ ¬∀ (x : α), f x = g x` |

**R4 · `scaleUnit_apply_fun`** changes the **goal**: a rescaled function applied to `m` is "rescale `m` back,
apply, rescale the result". Lemma: `scaleUnit u1 u2 f m = scaleUnit u1 u2 (f (scaleUnit u2 u1 m))`.
Placeholders: `{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices) (f : M1 → M2) (m : M1)`.
With three arguments you need it to get past the middle one (`Wrong c m'` is a function of `v` whose
values are functions of `E`).

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 f m)` | `⊢ P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))` |

Apply R1–R4 **in one** `simp only [...]`: `simp` repeats them until none applies, giving one `∃` over
`u1, u2` and all three arguments (W1 shows the two-argument shape).

### Choosing the counterexample

**R5 · `use a, b`** changes the **goal**: it fills the leading `∃` witnesses left to right, then tries
`rfl`/`assumption` on the rest. Placeholders: `{α β γ : Type} (P : α → β → γ → Prop) (a : α) (b : β)`.
The witness order is the binder order: unit systems `u1, u2` first, then `m, v, E`.

| Before | After |
|---|---|
| `⊢ ∃ x y z, P x y z` | `⊢ ∃ z, P a b z` |

**R6 · `⟨a⟩ : WithDim d ℝ`** builds a tagged number (the expected type supplies `d`). `{ val := a }.val`
reduces to `a` (`dsimp only`, `simp`, `norm_num` all do it). Placeholders:
`{d : Dimension LTMCTDimensionBase} (a : ℝ)`.

| Before | After `dsimp only` |
|---|---|
| `⊢ P { val := a }.val` | `⊢ P a` |

**R7 · `unfold D`** changes the **goal**: a defined name applied to arguments is replaced by its body.
Placeholders: `def Rel (k x y : ℝ) : Prop := y = k * x`, `(k a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Rel k a b)` | `⊢ P (b = k * a)` |

### Computing the rescaled numbers

One `norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]` does R8–R15: you pass the names that are
not `simp` lemmas (R9, R11, R13); it finds R8, R10, R12, R14, R15 itself.

**R8 · `scaleUnit_apply_fun_left`** changes the **goal**: `Prop` has no units, so rescaling a `Prop`-valued
function only rescales its input. Lemma: `scaleUnit u1 u2 f m = f (scaleUnit u2 u1 m)`. Placeholders:
`{M1 : Type} [UnitDependent M1] (u1 u2 : LTMCTUnitChoices) (f : M1 → Prop) (m : M1)`.

| Before | After |
|---|---|
| `⊢ scaleUnit u1 u2 f m` | `⊢ f (scaleUnit u2 u1 m)` |

**R9 · `WithDim.scaleUnit_val`** changes the **goal**: the number of a rescaled quantity is the conversion
factor times the number. Lemma: `(scaleUnit u1 u2 m).val = (u1.dimScale u2) d • m.val`. Placeholders:
`{d : Dimension LTMCTDimensionBase} (u1 u2 : LTMCTUnitChoices) (m : WithDim d ℝ)`. Not a `simp` lemma: name it.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 m).val` | `⊢ P ((u1.dimScale u2) d • m.val)` |

**R10 · `dimScale_SIPrimed_SI`** changes the **goal**: the factor from `SIPrimed` to `SI` is
`2^ℓ · 3^t · 5^m · 7^q · 11^θ` (a length of 1 SIPrimed unit is 2 m). `dimScale_SI_SIPrimed` is the reverse
(`2⁻¹, 3⁻¹, …`). Both are `simp` lemmas. Placeholders: `(d : Dimension LTMCTDimensionBase)`.

| Before | After |
|---|---|
| `⊢ P ((SIPrimed.dimScale SI) d)` | `⊢ P (2 ^ ↑d.length * 3 ^ ↑d.time * 5 ^ ↑d.mass * 7 ^ ↑d.charge * 11 ^ ↑d.temperature)` |

**R11 · `simp only [M𝓭, L𝓭, T𝓭]`** changes the **goal**: the base dimensions become their exponent vectors.
They are `def`s, so `simp` does not unfold them unless named.

| Before | After |
|---|---|
| `⊢ P (L𝓭 * T𝓭⁻¹)` | `⊢ P (ofLTMCTDimensionBase 1 0 0 0 0 * (ofLTMCTDimensionBase 0 1 0 0 0)⁻¹)` |

**R12 · `length_mul`, `inv_length`, `ofLTMCTDimensionBase_length`** change the **goal**: exponents add under
`*`, negate under `⁻¹`, and are read off `ofLTMCTDimensionBase`. The same lemmas exist for `time`, `mass`,
`charge`, `temperature`; all are `simp` lemmas. Placeholders: `(a b : ℚ)`.

| Before | After |
|---|---|
| `⊢ P (ofLTMCTDimensionBase 1 0 0 0 0 * (ofLTMCTDimensionBase 1 a b 0 0)⁻¹).length` | `⊢ P (1 + -1)` |

**R13 · `NNReal.smul_def`** changes the **goal**: `c • x = ↑c • x` for `c : NNReal`, so the factor becomes a
real number and `•` becomes ordinary `*` (`smul_eq_mul`, applied by `simp`). Placeholders:
`(c : NNReal) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (c • x)` | `⊢ P (↑c • x)` |

**R14 · `norm_num`** changes the **goal**: it evaluates numerals, including `NNReal` powers with numeral real
exponents and their casts to `ℝ`. Placeholders: `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑(2 ^ (1 + 1) * 3 ^ (-1 + -1) * 5) * c)` | `⊢ P (20 / 9 * c)` |

**R15 · `eq_iff_iff`, `iff_true`** change the **goal**: an equation of propositions is an `↔`, and
`A ↔ True` is `A`. In the exercise the original relation becomes `True` once its numbers are evaluated,
so the goal `¬ (A = True)` becomes `¬ A`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ P (A = True)` | `⊢ P A` |

### Closing

After the `norm_num` call the goal has the form `¬ (a * c = c * b)`: `c` times a numeral on each side, the
two numerals different (the right one may be printed as a product such as `c * b₁ * b₂`). It is false
only because `c ≠ 0`, so `norm_num` cannot finish it; `linarith` (R18) does not mind the product form.

**R16 · `intro h`** on `¬ A` changes the **goal and the context**: `¬ A` is `A → False`. Placeholders:
`(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R17 · `apply hab`** with `hab : a ≠ b` changes the **goal**: `a ≠ b` is `a = b → False`, so to prove
`False` it suffices to prove `a = b`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `hab : a ≠ b ⊢ False` | `⊢ a = b` |

**R18 · `linarith`** **closes** a goal that follows linearly from the hypotheses over an ordered field such
as `ℝ` (equalities, `≤`, `<`; products of a variable with numerals are fine). From `h : 3 * k = k * 2` it
proves `k = 0`.

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: "momentum = mass" is not dimensionally correct.** `MomWrong m p := (p.1 = m.1)` with
`m : WithDim M𝓭 ℝ`, `p : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹) ℝ`. After `simp only [isDimensionallyCorrect_fun_iff,
not_forall, funext_iff]` (two arguments: R4 is not needed), then `use SI, SIPrimed, ⟨1⟩, ⟨1⟩`, then
`unfold MomWrong`:

```lean-goal
⊢ ∃ x x_1 x_2 x_3, ¬scaleUnit x x_1 (MomWrong (scaleUnit x_1 x x_2)) x_3 = MomWrong x_2 x_3
⊢ ¬scaleUnit SI SIPrimed (MomWrong (scaleUnit SIPrimed SI { val := 1 })) { val := 1 } = MomWrong { val := 1 } { val := 1 }
⊢ ¬scaleUnit SI SIPrimed (fun p => p.val = (scaleUnit SIPrimed SI { val := 1 }).val) { val := 1 } = ({ val := 1 }.val = { val := 1 }.val)
```

`norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]` closes it: `p = m = 1` holds in `SI`, but
after converting, `p` and `m` get different factors. With no free constant nothing is left.

**W2: the closing pattern.** `¬ (3 * k = k * 2)` with `hk : k ≠ 0`: R16, R17, R18.

```lean-goal
⊢ ¬3 * k = k * 2
⊢ False
⊢ k = 0
```

---

## Traps

- Running R1, R2, R3, R4 as separate `simp only` calls in that order leaves a `¬ ∀` inside the `∃`: R3 creates
  a new `∀` after R2 has already run. Put all four in **one** `simp only [...]`.
- Pick values that make the relation **true** in the first system (`E = c · m · v` with your numbers). The goal
  compares the converted truth value with the original one; if the relation is false in both, you get
  `False = False` and no contradiction.
- `use` takes the unit systems first, then `m, v, E` in the order of `Wrong`'s arguments.
- `simp`/`norm_num` without `WithDim.scaleUnit_val` and `M𝓭, L𝓭, T𝓭` stops at `(scaleUnit … ).val` or at
  `↑M𝓭.length`: these are not `simp` lemmas, you must name them.
- For `c = 0` the relation is dimensionally correct (both sides are `0`), so `hc` must be used: the final goal
  needs R16 → R17 → R18, `norm_num` alone cannot close it.
- `≠` and `¬` are both `→ False`: `intro` and `apply` work on them directly.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold correctness, push `¬` inside | `simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff, scaleUnit_apply_fun]` | R1–R4 |
| give unit systems and values | `use SI, SIPrimed, ⟨a⟩, ⟨b⟩, …` | R5, R6 |
| expose a relation's body | `unfold Name` | R7 |
| `Prop`-valued function rescaled | `scaleUnit_apply_fun_left` (simp) | R8 |
| number of a rescaled quantity | `WithDim.scaleUnit_val` | R9 |
| factor `SIPrimed → SI` | `dimScale_SIPrimed_SI` (simp) | R10 |
| exponents of `M𝓭 L𝓭 T𝓭` | `simp only [M𝓭, L𝓭, T𝓭]` then `length_mul`, `inv_length`, … (simp) | R11, R12 |
| `NNReal` factor `•` real | `NNReal.smul_def` | R13 |
| evaluate the numbers | `norm_num [WithDim.scaleUnit_val, M𝓭, L𝓭, T𝓭, NNReal.smul_def]` | R14, R15 |
| `¬ A` | `intro h` | R16 |
| use `hc : c ≠ 0` on `False` | `apply hc` | R17 |
| linear arithmetic over `ℝ` | `linarith` | R18 |
| see the state | infoview | |
