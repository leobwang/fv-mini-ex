# E125 · Momentum is dimensionally correct: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's dimensions (`Dimension`,
`M𝓭 L𝓭 T𝓭`), quantities tagged with a dimension (`WithDim d ℝ`) and their products and `cast`, unit
systems (`LTMCTUnitChoices`), unit conversion (`scaleUnit`, the class `UnitDependent`), and
`IsDimensionallyCorrect`.

The physics: a unit system `u` fixes a unit of length, time, mass, charge and temperature. `scaleUnit u1 u2 x`
converts the quantity `x` from `u1` to `u2` (it multiplies the raw number by a positive scale factor that
depends on the dimension of `x`). A relation `R m v p : Prop` is *dimensionally correct* when converting
all its inputs to another unit system does not change whether it holds. For `p = m · v` the types already
force this: both sides have dimension `M L T⁻¹`, so they pick up the same factor. The proof only moves
`scaleUnit` from the arguments to the outside of each side, then cancels it with injectivity. No numbers
appear.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[UnitDependent M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Dimension LTMCTDimensionBase` | a physical dimension: one rational exponent for each base (Length, Time, Mass, Charge, Temperature). Dimensions form a commutative group under `*`, with inverse `⁻¹` |
| `M𝓭`, `L𝓭`, `T𝓭` | the base dimensions mass, length, time. `L𝓭 * T𝓭⁻¹` is velocity, `M𝓭 * L𝓭 * T𝓭⁻¹` is momentum |
| `WithDim d ℝ` | a real number tagged with dimension `d`: a structure with one field `val : ℝ` |
| `m * v` (on `WithDim`) | the product quantity: values multiply, dimensions multiply. `m * v : WithDim (M𝓭 * (L𝓭 * T𝓭⁻¹)) ℝ` |
| `x.cast h`, `cast x` | `x : WithDim d ℝ` retyped as `WithDim d2 ℝ` (same value), given a proof `h : d = d2`. Written `cast x` with no proof, Lean finds `h` itself |
| `MomentumEq._proof_1`, `⋯` | that proof `h`: in a `def` Lean names it `<def>._proof_1`, elsewhere it prints `⋯` |
| `LTMCTUnitChoices` | a unit system: a choice of length, time, mass, charge and temperature unit. `u1 u2` below are two of them |
| `UnitDependent M` | type class: `M` has a unit conversion `scaleUnit`. Met by `WithDim d ℝ`, by functions `M1 → M2` between such types, and by functions into `Prop` (where only the input is converted) |
| `scaleUnit u1 u2 x` | `x` converted from unit system `u1` to `u2` |
| `scaleUnit u1 u2 f` (`f` a function) | the converted function: `fun m => scaleUnit u1 u2 (f (scaleUnit u2 u1 m))` (R3), or `fun m => f (scaleUnit u2 u1 m)` when the output is a `Prop` (R4) |
| `IsDimensionallyCorrect f` | `∀ u1 u2, scaleUnit u1 u2 f = f`: converting `f` changes nothing |
| `(A = B) = (C = D)` | an equation between two propositions. `rw` with an `↔` lemma rewrites inside it (R8) |

---

## Part 1 · `momentum_isDimensionallyCorrect`

Statement: `IsDimensionallyCorrect MomentumEq`, where `MomentumEq m v p` is the proposition
`p = cast (m * v)` for a mass `m`, a velocity `v` and a momentum `p`. In words: for all unit systems
`u1 u2` and all `m v p`, the relation holds for `m v p` converted `u2 → u1` iff it holds for `m v p`.

### Dimensional correctness → one equation per input

**R1 · `rw [isDimensionallyCorrect_fun_iff]`** changes the **goal**. The lemma is
`IsDimensionallyCorrect f ↔ ∀ u1 u2 m, scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m`. Placeholders:
`{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (f : M1 → M2)`. `MomentumEq` is such an `f` with
`M1 = WithDim M𝓭 ℝ` (the mass) and `M2` the type of functions of `v` and `p`. It peels off the first
argument only; follow it with `intro u1 u2 m`.

| Before | After |
|---|---|
| `⊢ IsDimensionallyCorrect f` | `⊢ ∀ (u1 u2 : LTMCTUnitChoices) (m : M1), scaleUnit u1 u2 (f (scaleUnit u2 u1 m)) = f m` |

**R2 · `funext x y`** changes the **goal and the context**: an equation between functions of two arguments
becomes an equation between their values at two new variables. After R1 both sides are functions of `v`
and `p`. Placeholders: `{α β : Type} (f g : α → β → Prop)`. With one argument, write `funext x`.

| Before | After |
|---|---|
| `⊢ f = g` | `x : α, y : β ⊢ f x y = g x y` |

### Pushing `scaleUnit` onto the arguments

`simp only [scaleUnit_apply_fun, scaleUnit_apply_fun_left, D]` does R3, R4 and R5 in one step.

**R3 · `rw [scaleUnit_apply_fun]`** (full name `UnitDependent.scaleUnit_apply_fun`; the `open … UnitDependent …`
line lets you drop the prefix, likewise for R4 and R8) changes the **goal**:
`scaleUnit u1 u2 f m = scaleUnit u1 u2 (f (scaleUnit u2 u1 m))` for a function whose output also has units.
Placeholders: `{M1 M2 : Type} [UnitDependent M1] [UnitDependent M2] (u1 u2 : LTMCTUnitChoices) (f : M1 → M2) (m : M1)`.
In the exercise this is the step at `v`, where the output is still a function of `p`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 f m)` | `⊢ P (scaleUnit u1 u2 (f (scaleUnit u2 u1 m)))` |

**R4 · `rw [scaleUnit_apply_fun_left]`** changes the **goal**: the same for a function into a type with no
units, such as `Prop` (Lean picks the conversion that leaves the output alone): `scaleUnit u1 u2 f m = f (scaleUnit u2 u1 m)`. In the exercise this is the step at
the last argument `p`. Placeholders: `{M1 : Type} [UnitDependent M1] (u1 u2 : LTMCTUnitChoices) (f : M1 → Prop) (m : M1)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 f m)` | `⊢ P (f (scaleUnit u2 u1 m))` |

**R5 · `simp only [D]`** changes the **goal**: the defined name `D` applied to arguments becomes its body.
Placeholders: `D` defined by `def D {α : Type} (a b : α) : Prop := a = b`, and `(a b : α)`.

| Before | After |
|---|---|
| `⊢ P (D a b)` | `⊢ P (a = b)` |

After R1, `intro`, R2 and R3–R5 the goal of the exercise is an equation between two propositions:
the relation on converted inputs on the left, the relation itself on the right. The left side has
`scaleUnit u2 u1` on each of `m`, `v`, `p`.

### Moving `scaleUnit` outward through `*` and `cast`

**R6 · `rw [DMul.hMul_scaleUnit]`** changes the **goal**:
`scaleUnit u1 u2 x * scaleUnit u1 u2 y = scaleUnit u1 u2 (x * y)` (converting commutes with products).
`DMul` is physlib's class of dimensionful multiplication (`*` on `WithDim` is an instance); the lemma lives in
its namespace, so write the prefix.
Placeholders: `(d1 d2 : Dimension LTMCTDimensionBase) (u1 u2 : LTMCTUnitChoices) (x : WithDim d1 ℝ) (y : WithDim d2 ℝ)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 x * scaleUnit u1 u2 y)` | `⊢ P (scaleUnit u1 u2 (x * y))` |

**R7 · `rw [cast_scaleUnit]`** (full name `WithDim.cast_scaleUnit`) changes the **goal**:
`(scaleUnit u1 u2 x).cast h = scaleUnit u1 u2 (x.cast h)` (converting commutes with retyping).
Placeholders: `(d d2 : Dimension LTMCTDimensionBase) (hd : d = d2) (u1 u2 : LTMCTUnitChoices) (x : WithDim d ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((scaleUnit u1 u2 x).cast hd)` | `⊢ P (scaleUnit u1 u2 (x.cast hd))` |

**R8 · `rw [scaleUnit_injective]`** changes the **goal**. The lemma is
`scaleUnit u1 u2 a = scaleUnit u1 u2 b ↔ a = b`: converting is injective, so it cancels from both sides of
an equation. `rw` accepts an `↔` lemma and replaces the left proposition by the right one, even inside a
larger proposition. Placeholders: `{M : Type} [UnitDependent M] (u1 u2 : LTMCTUnitChoices) (a b : M)`.

| Before | After |
|---|---|
| `⊢ P (scaleUnit u1 u2 a = scaleUnit u1 u2 b)` | `⊢ P (a = b)` |

**R9 · `rw` closes by `rfl`** changes the **goal list**: after rewriting, `rw` tries `rfl`, so a goal whose
two sides became the same text is closed and nothing is left. In the exercise, R8 turns the left side into
the right side and the proof ends there. Placeholders: as in R8.

| Before | After |
|---|---|
| `⊢ (scaleUnit u1 u2 a = scaleUnit u1 u2 b) = (a = b)` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1.** `AreaEq a A := A = a * a` with `a : L`, `A : L²`. Two arguments, so one `funext A` and only R4.
The states after R1, `intro u1 u2 a`, `funext A`, and `simp only [scaleUnit_apply_fun_left, AreaEq]`;
then `rw [DMul.hMul_scaleUnit, scaleUnit_injective]` closes it (R6, R8, R9):

```lean-goal
⊢ IsDimensionallyCorrect AreaEq
⊢ ∀ (u1 u2 : LTMCTUnitChoices) (m : WithDim L𝓭 ℝ), scaleUnit u1 u2 (AreaEq (scaleUnit u2 u1 m)) = AreaEq m
⊢ scaleUnit u1 u2 (AreaEq (scaleUnit u2 u1 a)) = AreaEq a
⊢ scaleUnit u1 u2 (AreaEq (scaleUnit u2 u1 a)) A = AreaEq a A
⊢ (scaleUnit u2 u1 A = scaleUnit u2 u1 a * scaleUnit u2 u1 a) = (A = a * a)
```

**W2.** A `cast` around a product of a velocity and a time, `v * t : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭) ℝ` retyped
to `WithDim L𝓭 ℝ`. R6 first (the product is inside the `cast`), then R7:

```lean-goal
⊢ x = (scaleUnit u1 u2 v * scaleUnit u1 u2 t).cast ⋯
⊢ x = (scaleUnit u1 u2 (v * t)).cast ⋯
⊢ x = scaleUnit u1 u2 ((v * t).cast ⋯)
```

---

## Traps

- The inputs are converted `u2 → u1` (`scaleUnit u2 u1`), the opposite order to `IsDimensionallyCorrect`'s
  `u1 u2`. You never need to pick the order yourself here, but read the goals with it in mind.
- After R1 the goal is still an equation between *functions* of `v` and `p`; `simp only [scaleUnit_apply_fun]`
  fails with "`simp` made no progress" until `funext v p` (R2) applies both sides.
- The goal after R3–R5 is `(… = …) = (… = …)`, an equation between propositions, not an `↔`. `rw` with the
  `↔` lemma R8 still works on it.
- Order of R6 and R7: `cast` wraps the product, so `rw [cast_scaleUnit]` fails until R6 has turned
  `scaleUnit u2 u1 m * scaleUnit u2 u1 v` into one `scaleUnit u2 u1 (m * v)`.
- `rw [scaleUnit_injective]` needs `scaleUnit u2 u1` on *both* sides of the inner `=`; do R6 and R7 first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `IsDimensionallyCorrect f` → `∀ u1 u2 m, …` | `rw [isDimensionallyCorrect_fun_iff]` | R1 |
| name the unit systems and the first input | `intro u1 u2 m` | |
| apply both function sides to the other inputs | `funext v p` | R2 |
| push `scaleUnit` onto the arguments, unfold the relation `D` | `simp only [scaleUnit_apply_fun, scaleUnit_apply_fun_left, D]` | R3, R4, R5 |
| product of converted quantities → converted product | `rw [DMul.hMul_scaleUnit]` | R6 |
| `cast` of converted → converted `cast` | `rw [cast_scaleUnit]` | R7 |
| cancel `scaleUnit u1 u2` on both sides of `=` | `rw [scaleUnit_injective]` | R8 |
| goal became `X = X` | nothing: `rw` closes it | R9 |
| all of R1–R9 at once (`funext_iff : f = g ↔ ∀ x, f x = g x`) | `simp [funext_iff, D]` | |
| see the state | infoview | |
