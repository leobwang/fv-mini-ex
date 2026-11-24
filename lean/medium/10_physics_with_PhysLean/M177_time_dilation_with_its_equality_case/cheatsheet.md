# M177 · Time dilation, with its equality case: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's spacetime points `SpaceTime d`
(Lorentz vectors), the Minkowski product `⟪p, q⟫ₘ` and `SpaceTime.properTime`; Mathlib's real square
root `√`, finite sums `∑` with their sign lemmas, and the closer `linarith`.

The physics: in `d` space dimensions an event is a point `p` with a time coordinate `p⁰ = p (Sum.inl 0)`
and space coordinates `pⁱ = p (Sum.inr i)` (units with `c = 1`). For two events `q`, `p` let
`v = p − q`. The Minkowski product (signature `(+, −, …, −)`) is `⟪v, v⟫ₘ = (v⁰)² − ∑ᵢ (vⁱ)²`, and the
proper time is `τ = √⟪v, v⟫ₘ`: the time a clock moving uniformly from `q` to `p` shows. With
`Δt = v⁰ > 0`, time dilation says `τ ≤ Δt`, with equality exactly when the clock does not move
(`vⁱ = 0` for every `i`).

Math. Write `S = ∑ᵢ (vⁱ)² ≥ 0`. Then `⟪v, v⟫ₘ = Δt² − S ≤ Δt²`, so `√⟪v, v⟫ₘ ≤ Δt` (this needs `Δt ≥ 0`).
(→) If `√⟪v, v⟫ₘ = Δt > 0`, the radicand is not negative (Lean's `√` of a negative number is `0`), so
squaring gives `⟪v, v⟫ₘ = Δt²`, hence `S = 0`, hence every `(vⁱ)² = 0`, hence every `vⁱ = 0`.
(←) If every `vⁱ = 0` then `S = 0` and `τ = √(Δt²) = Δt`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal or hypothesis. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{n : ℕ}` is implicit (Lean infers it). A bracket such as
  `[AddCommMonoid N]` is a requirement on a type (a *type class*); all of them hold for `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `SpaceTime d` | an event in `d` space dimensions; by definition `Lorentz.Vector d` |
| `Lorentz.Vector d` | a 4-vector: a function `Fin 1 ⊕ Fin d → ℝ` (one time + `d` space components) |
| `Fin 1 ⊕ Fin d` | the index type (disjoint union `⊕`): `Sum.inl 0` is the time index, `Sum.inr i` (`i : Fin d`) the `i`-th space index |
| `v (Sum.inl 0)`, `v (Sum.inr i)` | the components `v⁰` and `vⁱ` (a vector is applied to an index like a function) |
| `p - q` | componentwise difference: `(p - q) μ = p μ - q μ` (R18) |
| `⟪p, q⟫ₘ` | Minkowski product `p⁰ q⁰ − ∑ᵢ pⁱ qⁱ`. Scoped notation: it needs `open Lorentz Vector` |
| `(minkowskiProduct p) q` | how the infoview prints `⟪p, q⟫ₘ`: a bilinear map applied first to `p`, then to `q` |
| `q.properTime p` | `SpaceTime.properTime q p`, defined as `√⟪p - q, p - q⟫ₘ` (R1) |
| `√x` | `Real.sqrt x`; it is `0` for every `x ≤ 0` (R13), so `√` never fails |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over all `i : Fin d` (`Finset.univ` = the finite set of all elements) |
| `∀ i ∈ Finset.univ, P i` | `∀ i, i ∈ Finset.univ → P i`; the membership is always true (R16) |
| `v : SpaceTime d := p - q` | a local definition made by `set` (R2): `v` *is* `p - q` |
| `a✝`, `x✝` | an anonymous hypothesis (introduced with `_`, e.g. `intro i _` or `fun i _ => …`); you cannot name it, and need not |
| `¬a ≤ b` | not `a ≤ b`; over `ℝ` the same as `b < a` (R12) |
| `case refine_2` | the name of the second goal after `refine` |

---

## Part 1 · `properTime_le`

Statement: for events `q p : SpaceTime d` with `h : 0 < (p - q) (Sum.inl 0)`,
`τ ≤ Δt ∧ (τ = Δt ↔ ∀ i, p (Sum.inr i) = q (Sum.inr i))`, where `τ = SpaceTime.properTime q p` and
`Δt = (p - q) (Sum.inl 0)`.

### Proper time → coordinates (skeleton steps 1–2)

**R1 · `unfold SpaceTime.properTime`** changes the **goal**: the name is replaced by its definition.
Placeholders: `{d : ℕ} (q p : SpaceTime d)`. Note the order: `properTime q p` is `√⟪p - q, p - q⟫ₘ`.

| Before | After |
|---|---|
| `⊢ P (q.properTime p)` | `⊢ P √((minkowskiProduct (p - q)) (p - q))` |

**R2 · `set v := p - q with hv`** changes the **goal and the context**: it adds the local definition
`v := p - q` and the equation `hv : v = p - q`, and replaces every `p - q` (in the goal and in every
hypothesis, so also in `h`) by `v`. Later, `simp [hv]` or `rw [hv]` turns `v` back into `p - q` (R20).
Placeholders: `{d : ℕ} (q p : SpaceTime d)`.

| Before | After |
|---|---|
| `⊢ P (p - q)` | `v : SpaceTime d := p - q, hv : v = p - q ⊢ P v` |

**R3 · `rw [minkowskiProduct_toCoord]`** changes the **goal**. The lemma is
`⟪x, y⟫ₘ = x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i)`.
Placeholders: `{d : ℕ} (x y : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((minkowskiProduct x) y)` | `⊢ P (x (Sum.inl 0) * y (Sum.inl 0) - ∑ i, x (Sum.inr i) * y (Sum.inr i))` |

**R4 · `sq`** changes the **goal**. The lemma is `sq a : a ^ 2 = a * a`. `simp only [sq]` rewrites every
square, also under the binder of `∑` (where `rw` cannot reach); `simp [sq]` does the same on both sides of an
equation and then closes it if they agree. Placeholders: `{n : ℕ} (a : ℝ) (f : Fin n → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ 2 - ∑ i, f i ^ 2)` | `⊢ P (a * a - ∑ x, f x * f x)` |

**R5 · `sq_nonneg a`** changes the **context** (with `have`): it adds `0 ≤ a ^ 2`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ a ^ 2 ⊢ G` |

**R6 · `Finset.sum_nonneg`** changes the **goal**. The lemma is `(∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i`:
a sum of nonnegative terms is nonnegative. Placeholders: `{n : ℕ} (f : Fin n → ℝ)`, `s = Finset.univ`. As a
term, `Finset.sum_nonneg (fun i _ => sq_nonneg _)` proves `0 ≤ ∑ i, g i ^ 2` in one go (the `_` ignores the
membership proof).

| Before | After `apply Finset.sum_nonneg` | After `intro i _` |
|---|---|---|
| `⊢ 0 ≤ ∑ i, f i` | `⊢ ∀ i ∈ Finset.univ, 0 ≤ f i` | `i : Fin n, a✝ : i ∈ Finset.univ ⊢ 0 ≤ f i` |

### Splitting the statement (skeleton step 3)

**R7 · `refine ⟨?_, ⟨fun hb => ?_, fun hc => ?_⟩⟩`** changes the **goal list**: one goal becomes three. An
`↔` is a structure with two fields (`→` and `←`), so it is built with `⟨_, _⟩` too; `fun hb => ?_` leaves the
body open with `hb` in the context. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ (B ↔ C)` | `⊢ A`, `hb : B ⊢ C`, `hc : C ⊢ B` |

### `τ ≤ Δt` (skeleton step 4)

**R8 · `h.le`** changes the **context** (with `have`), or is passed straight as an argument. For
`h : a < b`, `h.le : a ≤ b` (the lemma `le_of_lt`; `h.le` is dot notation for `LT.lt.le h`).
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a < b ⊢ G` | `h' : a ≤ b ⊢ G` |

**R9 · `rw [Real.sqrt_le_left hy]`** changes the **goal**. The lemma is
`Real.sqrt_le_left : 0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`; `rw` with an `↔` replaces one proposition by the other.
In the exercise the premise `0 ≤ y` is `h.le` (R8). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ √x ≤ y` | `⊢ x ≤ y ^ 2` |

**R10 · `linarith`** **closes** a goal `t ≤ u`, `t < u` or `t = u` that follows by adding up hypotheses
(linear arithmetic over ordered fields). Anything nonlinear (`a ^ 2`, `∑ …`, `⟪v, v⟫ₘ`, `√x`) is treated as an
opaque atom, which is exactly what is needed here: with `key : ⟪v, v⟫ₘ = v⁰ ^ 2 - S` and `hs : 0 ≤ S` in the
context it proves `⟪v, v⟫ₘ ≤ v⁰ ^ 2`. It also closes `False` from contradictory hypotheses.

| Before | After |
|---|---|
| `hx : x = a - s, hs : 0 ≤ s ⊢ x ≤ a` | closed |

### (→): `τ = Δt` gives equal space coordinates (skeleton step 5)

**R11 · `by_contra hneg`** changes the **goal and the context**: to prove `G`, assume `hneg : ¬G` and prove
`False`. Placeholders: `(x : ℝ)`, `G = 0 ≤ x`.

| Before | After |
|---|---|
| `⊢ 0 ≤ x` | `hneg : ¬0 ≤ x ⊢ False` |

**R12 · `not_le.mp`** changes the **context**. The lemma is `not_le : ¬a ≤ b ↔ b < a` (in a linear order such
as `ℝ`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : ¬a ≤ b ⊢ G` | `h' : b < a ⊢ G` |

**R13 · `rw [Real.sqrt_eq_zero'.mpr hx] at h`** changes the **context**. The lemma is
`Real.sqrt_eq_zero' : √x = 0 ↔ x ≤ 0`; `.mpr hx` (the `←` direction applied to `hx : x ≤ 0`) is the equation
`√x = 0`, which `rw … at h` uses inside `h`. Placeholders: `(x : ℝ) (hx : x ≤ 0)`.

| Before | After |
|---|---|
| `h : P √x ⊢ G` | `h : P 0 ⊢ G` |

**R14 · `rw [Real.sq_sqrt hx]`** changes the **goal**. The lemma is `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`.
Placeholders: `(x : ℝ) (hx : 0 ≤ x)`. Do not confuse it with R23 (`√(a ^ 2) = a`).

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

**R15 · `Finset.sum_eq_zero_iff_of_nonneg hf`** changes the **goal** (with `rw`) or the **context** (forwards,
`have h := (Finset.sum_eq_zero_iff_of_nonneg hf).mp hz` turns `hz : ∑ i, f i = 0` into
`h : ∀ i ∈ Finset.univ, f i = 0`). The lemma is `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)`:
a sum of nonnegative terms vanishes iff every term does. Placeholders: `{n : ℕ} (f : Fin n → ℝ)`,
`hf : ∀ i ∈ Finset.univ, 0 ≤ f i` (for squares: `fun i _ => sq_nonneg _`, R5).

| Before | After `rw [Finset.sum_eq_zero_iff_of_nonneg hf]` |
|---|---|
| `⊢ ∑ i, f i = 0` | `⊢ ∀ i ∈ Finset.univ, f i = 0` |

**R16 · `Finset.mem_univ i`** is the proof of `i ∈ Finset.univ`, the premise every `∀ j ∈ Finset.univ, …`
hypothesis asks for. Forwards: `h i (Finset.mem_univ i) : f i = 0`. With `apply h` the premise becomes the
**goal**, which `exact Finset.mem_univ i` closes. Placeholders: `{n : ℕ} (f : Fin n → ℝ) (i : Fin n)`,
`h : ∀ j ∈ Finset.univ, f j = 0`.

| Before | After `apply h` | After `exact Finset.mem_univ i` |
|---|---|---|
| `⊢ f i = 0` | `⊢ i ∈ Finset.univ` | closed |

**R17 · `(pow_eq_zero_iff two_ne_zero).mp h`** changes the **context**. The lemma is
`pow_eq_zero_iff : n ≠ 0 → (a ^ n = 0 ↔ a = 0)` (in a ring without nilpotents, such as `ℝ`); `two_ne_zero`
proves `2 ≠ 0`. The solution writes the same as `pow_eq_zero_iff two_ne_zero |>.mp h` (`x |>.f` is `(x).f`).
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : a ^ 2 = 0 ⊢ G` | `h' : a = 0 ⊢ G` |

**R18 · `Lorentz.Vector.apply_sub`** changes the **context** (or goal): `(x - y) μ = x μ - y μ`. `simp`
applies it by itself. Placeholders: `{d : ℕ} (x y : Lorentz.Vector d) (μ : Fin 1 ⊕ Fin d)`.

| Before | After |
|---|---|
| `h : P ((x - y) μ) ⊢ G` | `h : P (x μ - y μ) ⊢ G` |

**R19 · `sub_eq_zero`** changes the **context** (with `rw … at h`). The lemma is `a - b = 0 ↔ a = b`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a - b = 0 ⊢ G` | `h : a = b ⊢ G` |

**R20 · `simpa [hw, sub_eq_zero] using h`** **closes** the goal: it simplifies `h` and the goal with the same
lemmas (here `hw` turns `w` into `x - y`, then R18 and R19 apply) and closes the goal with the simplified `h`.
Placeholders: `{d : ℕ} (x y w : Lorentz.Vector d) (hw : w = x - y) (μ : Fin 1 ⊕ Fin d)`. In the exercise `hw` is
the `hv` from R2.

| Before | After |
|---|---|
| `hw : w = x - y, h : w μ = 0 ⊢ x μ = y μ` | closed |

### (←): equal space coordinates give `τ = Δt` (skeleton step 6)

**R21 · `Finset.sum_eq_zero`** changes the **goal**. The lemma is `(∀ i ∈ s, f i = 0) → ∑ i ∈ s, f i = 0`.
As a term: `Finset.sum_eq_zero (fun i _ => by simp [hv, hi i])`. Placeholders: `{n : ℕ} (f : Fin n → ℝ)`.

| Before | After `apply Finset.sum_eq_zero` | After `intro i _` |
|---|---|---|
| `⊢ ∑ i, f i = 0` | `⊢ ∀ x ∈ Finset.univ, f x = 0` | `i : Fin n, a✝ : i ∈ Finset.univ ⊢ f i = 0` |

**R22 · `rw [sub_zero]`** changes the **goal**. The lemma is `a - 0 = a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a - 0)` | `⊢ P a` |

**R23 · `rw [Real.sqrt_sq ha]`** changes the **goal**. The lemma is `Real.sqrt_sq : 0 ≤ a → √(a ^ 2) = a`.
Placeholders: `(a : ℝ) (ha : 0 ≤ a)`; in the exercise `ha` is `h.le` (R8).

| Before | After |
|---|---|
| `⊢ P √(a ^ 2)` | `⊢ P a` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a zero sum of squares has zero terms.** For `f : Fin n → ℝ` with `hz : ∑ i, f i ^ 2 = 0`: R15 with
`fun j _ => sq_nonneg (f j)` (R5), applied to `i` and `Finset.mem_univ i` (R16), then R17:

```lean-goal
⊢ f i = 0
```

and after the `have`, `h3 : f i ^ 2 = 0` is in the context; `(pow_eq_zero_iff two_ne_zero).mp h3` closes it.

**W2: squaring `he : √x = y`.** Goal `x = y ^ 2`. `rw [← he]` replaces `y` by `√x`, then R14 closes it (the
`rfl` that `rw` tries at the end finishes `x = x`):

```lean-goal
⊢ x = y ^ 2
⊢ x = √x ^ 2
```

**W3: `√x = y` with `y > 0` forces `0 ≤ x`.** R11, then R13 at `he` with the argument
`(not_le.mp hneg).le` (R12, R8): `he` becomes `0 = y`, which contradicts `hy : 0 < y` (R10).

| Before | After `by_contra hneg` | After `rw [… ] at he` |
|---|---|---|
| `he : √x = y ⊢ 0 ≤ x` | `hneg : ¬0 ≤ x ⊢ False` | `he : 0 = y ⊢ False` |

**W4: a square root that collapses.** `rw [hs]` (with `hs : s = 0`), R22, R23:

```lean-goal
⊢ √(a ^ 2 - s) = a
⊢ √(a ^ 2 - 0) = a
⊢ √(a ^ 2) = a
```

---

## Traps

- **`0 < Δt`, not `0 ≤ Δt`.** Lean's `√x` is `0` for every `x ≤ 0`. With `Δt = 0` and spacelike separation,
  `√⟪v, v⟫ₘ = 0 = Δt` although the space coordinates differ. The strict `h` is what rules out a negative
  radicand in (→) (W3).
- `properTime q p` is `√⟪p - q, p - q⟫ₘ`: the *second* argument comes first in the difference.
- Prove `key` and `hs` **before** `refine`: a `have` made inside one branch is not visible in the others.
- `set` also rewrites `h`: after R2 it reads `h : 0 < v (Sum.inl 0)`. The goal of (→) ends in `p`, `q`
  coordinates, so `v` must be turned back with `hv` (R20).
- `rw` cannot rewrite under the binder of `∑ i, …`; use `simp only [sq]` / `simp [sq]` (R4).
- R14 `√x ^ 2 = x` and R23 `√(x ^ 2) = x` are different lemmas (`Real.sq_sqrt` vs `Real.sqrt_sq`).
- `linarith` does not multiply: `a ^ 2` is an atom. It needs `key` and `hs` in the context.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `τ` | `unfold SpaceTime.properTime` | R1 |
| name `p - q` | `set v := p - q with hv` | R2 |
| `⟪v, v⟫ₘ` in coordinates | `rw [minkowskiProduct_toCoord]; simp [sq]` | R3, R4 |
| `0 ≤ ∑ i, g i ^ 2` | `Finset.sum_nonneg (fun i _ => sq_nonneg _)` | R5, R6 |
| split `A ∧ (B ↔ C)` | `refine ⟨?_, ⟨fun hb => ?_, fun hc => ?_⟩⟩` | R7 |
| `a < b` → `a ≤ b` | `h.le` | R8 |
| `√x ≤ y` → `x ≤ y ^ 2` | `rw [Real.sqrt_le_left hy]` | R9 |
| linear consequence | `linarith` | R10 |
| proof by contradiction | `by_contra hneg` | R11 |
| `¬a ≤ b` → `b < a` | `not_le.mp h` | R12 |
| `√x` → `0` when `x ≤ 0` | `rw [Real.sqrt_eq_zero'.mpr hx] at h` | R13 |
| `√x ^ 2` → `x` | `rw [Real.sq_sqrt hx]` | R14 |
| `∑ = 0` → each term `= 0` | `(Finset.sum_eq_zero_iff_of_nonneg hf).mp hz i (Finset.mem_univ _)` | R15, R16 |
| `a ^ 2 = 0` → `a = 0` | `(pow_eq_zero_iff two_ne_zero).mp h` | R17 |
| `v (…) = 0` → `p (…) = q (…)` | `simpa [hv, sub_eq_zero] using h` | R18–R20 |
| each term `= 0` → `∑ = 0` | `Finset.sum_eq_zero (fun i _ => …)` | R21 |
| `a - 0` → `a`, `√(a ^ 2)` → `a` | `rw [sub_zero, Real.sqrt_sq ha]` | R22, R23 |
| see the state | infoview | |
