# E122 · Minkowski interval of an event: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's spacetime vectors
(`Lorentz.Vector`, `SpaceTime`), the Minkowski product `⟪·, ·⟫ₘ`, `SpaceTime.properTime`, Mathlib's
finite sums `∑` and the real square root `√`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n` | the type of naturals `0, 1, …, n - 1`; numerals such as `0 : Fin 3` are its elements |
| `α ⊕ β` | the disjoint union (`Sum α β`): an element is `Sum.inl a` with `a : α` or `Sum.inr b` with `b : β` |
| `Lorentz.Vector d` | by definition `Fin 1 ⊕ Fin d → ℝ`: a 4-vector (for `d = 3`) is a function from indices to reals |
| `SpaceTime d` | a reducible synonym for `Lorentz.Vector d`; `d` defaults to `3` |
| `Sum.inl 0` | the time index (`0 : Fin 1`); `x (Sum.inl 0)` is the coordinate `ct` of `x` |
| `Sum.inr i` | the spatial index `i : Fin d`; `x (Sum.inr 0)` is the coordinate `x¹` (the problem's "x") |
| `fun \| Sum.inl 0 => 5 \| …` | a vector defined by pattern matching on the index, first matching line wins |
| `⟪x, y⟫ₘ` | the Minkowski product $x^0y^0 - \sum_{i} x^i y^i$, signature (+,−,−,−); needs `open Lorentz Vector` |
| `(minkowskiProduct x) y` | how the infoview prints `⟪x, y⟫ₘ`: `minkowskiProduct` is a bilinear map `Lorentz.Vector d →L[ℝ] Lorentz.Vector d →L[ℝ] ℝ` (`→L[ℝ]` = continuous ℝ-linear map), applied to `x`, then to `y` |
| `∑ i, f i` | Mathlib's finite sum of `f i` over every `i` of a finite type (here `Fin 3`) |
| `SpaceTime.properTime x y`, `x.properTime y` | proper time from event `x` to event `y`, defined as `√⟪y - x, y - x⟫ₘ` (units with `c = 1`) |
| `0 : SpaceTime 3` | the origin, the zero vector |
| `√x` | `Real.sqrt x`; for `x < 0` it is `0` (a junk value) |
| `match Sum.inr x with …` | a `fun \| …` definition applied to an index `simp` cannot decide (a bound variable `x`): stuck (W2) |

---

## Part 1 · `minkowski_p`

Statement: `⟪p, p⟫ₘ = 16`, where `p` has `ct = 5`, spatial coordinates `(3, 0, 0)`. In coordinates it is
$5\cdot 5 - (3\cdot 3 + 0\cdot 0 + 0\cdot 0) = 16$.

**R1 · `rw [minkowskiProduct_toCoord]`** changes the **goal**: the product becomes coordinates. The lemma
(`Lorentz.Vector.minkowskiProduct_toCoord`) is
`⟪x, y⟫ₘ = x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i)`.
Placeholders: `{d : ℕ} (x y : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((minkowskiProduct x) y)` | `⊢ P (x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i))` |

**R2 · `Fin.sum_univ_three`** changes the **goal**: a sum over `Fin 3` becomes three explicit terms, so every
index is a concrete numeral. The lemma is `∑ i, f i = f 0 + f 1 + f 2`. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Fin 3 → M)` (`M` has `+` and `0`, `+` commutative; `ℝ` qualifies). Use it
with `rw` or inside `simp [...]`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

**R3 · `simp only [q]`** changes the **goal**: it unfolds a vector `q` defined by `fun | … =>` and, when the
index is a concrete constructor, picks the matching line. Placeholders: `q` defined by
`def q : Lorentz.Vector 3 := fun | Sum.inl 0 => 2 | Sum.inr _ => 1` (the same type as `SpaceTime 3`). `simp [q]` (without `only`) does the same and
also simplifies the arithmetic around it.

| Before | After |
|---|---|
| `⊢ P (q (Sum.inl 0))` | `⊢ P 2` |
| `⊢ P (q (Sum.inr 2))` | `⊢ P 1` |

**R4 · `norm_num`** **closes** a goal of arithmetic on numerals in `ℝ`, such as `2 * 2 - 1 * 1 = 3`.

**W1: the chain on another event.** `r = (3, 0, 2, 0)`, goal `⟪r, r⟫ₘ = 5`. R1, R2, R3, then R4:

```lean-goal
⊢ (minkowskiProduct r) r = 5
⊢ r (Sum.inl 0) * r (Sum.inl 0) - ∑ i, r (Sum.inr i) * r (Sum.inr i) = 5
⊢ r (Sum.inl 0) * r (Sum.inl 0) - (r (Sum.inr 0) * r (Sum.inr 0) + r (Sum.inr 1) * r (Sum.inr 1) + r (Sum.inr 2) * r (Sum.inr 2)) = 5
⊢ 3 * 3 - (0 * 0 + 2 * 2 + 0 * 0) = 5
```

**W2: R3 before R2 gets stuck.** After R1, `simp [r]` reads off the time coordinate but not the sum: inside
`∑ x, …` the index `Sum.inr x` has a variable `x`, so the `match` cannot choose a line. The goal then shows
`match Sum.inr x with | Sum.inl 0 => 3 | Sum.inr 1 => 2 | …`. Rewriting with R2 afterwards makes the indices
concrete; then `simp` finishes reading them off:

```lean-goal
⊢ 3 * 3 - 2 * 2 = 5
```

---

## Part 2 · `properTime_p`

Statement: `SpaceTime.properTime 0 p = 4`, the proper time from the origin to `p`. Unfold it (R5), clean up
`p - 0` (R6), reuse Part 1 with `rw [minkowski_p]`, then evaluate `√16` (R7, R8).

**R5 · `rw [SpaceTime.properTime]`** changes the **goal**: the definition is unfolded,
`properTime x y = √⟪y - x, y - x⟫ₘ` (note the order: from `x` to `y`, so the difference is `y - x`).
Placeholders: `{d : ℕ} (x y : SpaceTime d)`. The infoview prints `SpaceTime.properTime x y` as `x.properTime y`
when `x` is a variable.

| Before | After |
|---|---|
| `⊢ P (x.properTime y)` | `⊢ P √((minkowskiProduct (y - x)) (y - x))` |

**R6 · `rw [sub_zero]`** changes the **goal**. The lemma is `sub_zero : a - 0 = a`; `rw` rewrites every
occurrence. Placeholders: `{d : ℕ} (y : SpaceTime d)` (vectors subtract entrywise; any additive group qualifies).

| Before | After |
|---|---|
| `⊢ P (y - 0)` | `⊢ P y` |

After R5 and R6 the goal contains `(minkowskiProduct p) p`, which is literally the left side of `minkowski_p`,
so `rw [minkowski_p]` turns it into `16` (TACTIC_STATES, `rw [h]`). Proving `minkowski_p` first is what lets
Part 2 skip the coordinates.

**R7 · `rw [show (a : ℝ) = e by norm_num]`** changes the **goal**: a numeral is replaced by another form of it.
`show T by tac` is a proof of `T` written inline. Placeholders: the numerals of the example, `9` and `3 ^ 2`.

| Before | After |
|---|---|
| `⊢ P 9` | `⊢ P (3 ^ 2)` |

**R8 · `Real.sqrt_sq`** changes the **goal**. The lemma is `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`.
Placeholders: `(x : ℝ) (hx : 0 ≤ x)`. When the goal is exactly `√(a ^ 2) = a`, close it with
`exact Real.sqrt_sq (by norm_num)`; the `(by norm_num)` proves `0 ≤ a`.

| Before | After |
|---|---|
| `⊢ P √(x ^ 2)` | `⊢ P x` |

**W3: `√9 = 3`.** R7, then R8 with `exact`:

```lean-goal
⊢ √9 = 3
⊢ √(3 ^ 2) = 3
```

---

## Traps

- `norm_num` and `simp` do not evaluate `√16` or `√9`: write the number as a square first (R7), then R8.
- `rw [show 9 = 3 ^ 2 by norm_num]` without `(9 : ℝ)` elaborates `9` in `ℕ` and fails with "did not find an
  occurrence of the pattern". Always ascribe the type.
- `norm_num [p]` or `simp [p]` straight after R1 leaves `match Sum.inr x with …` inside the sum (W2). Include
  `Fin.sum_univ_three` (R2) so the spatial indices become the concrete `0, 1, 2`.
- `properTime x y` is the proper time *from* `x` *to* `y`: the difference is `y - x`, so `properTime 0 p`
  unfolds to `√⟪p - 0, p - 0⟫ₘ`, and `sub_zero` (not `zero_sub`) cleans it.
- `⟪·, ·⟫ₘ` is notation that needs `open Lorentz Vector`; the infoview never shows it, only
  `(minkowskiProduct x) y`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `⟪x, y⟫ₘ` → coordinates | `rw [minkowskiProduct_toCoord]` | R1 |
| `∑ i : Fin 3, f i` → three terms | `Fin.sum_univ_three` (in `rw` or `simp`) | R2 |
| read off coordinates of a `fun \| …` vector | `simp [q, Fin.sum_univ_three]` | R3, R2 |
| numeric goal in `ℝ` | `norm_num` | R4 |
| unfold proper time | `rw [SpaceTime.properTime]` | R5 |
| `y - 0` → `y` | `rw [sub_zero]` | R6 |
| reuse a proved equation | `rw [minkowski_p]` | TACTIC_STATES |
| `16` → `4 ^ 2` | `rw [show (16 : ℝ) = 4 ^ 2 by norm_num]` | R7 |
| `√(a ^ 2) = a` | `exact Real.sqrt_sq (by norm_num)` | R8 |
| see the state | infoview | |
