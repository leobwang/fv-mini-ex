# E098 · A fair die: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's probability mass functions (`PMF`),
the measure they define, the extended non-negative reals `ENNReal`, the integral `∫ … ∂μ`, and sums over
`Fin n`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 6` | the type `{0, 1, …, 5}`; face `i` of the die shows `i + 1` pips |
| `ENNReal` (also written `ℝ≥0∞`) | the extended non-negative reals `[0, ∞]`, where masses and measures take values |
| `PMF α` | a probability mass function on `α`: a weight `p a : ENNReal` for each point, the weights summing to 1 |
| `p a` | the weight of the point `a` (a `PMF` is applied like a function) |
| `PMF.uniformOfFintype α` | the uniform PMF on a finite, non-empty type: every point weighs `(card α)⁻¹` |
| `(PMF.uniformOfFintype α) a` | how Lean prints `PMF.uniformOfFintype α a` |
| `p.toMeasure` | the measure (a function `Set α → ENNReal`) of `p`: `p.toMeasure s` is the total weight of `s` |
| `{a}` | the one-point set containing `a` |
| `MeasurableSet s` | `s` is in the σ-algebra (the family of sets a measure can measure); on `Fin n` every set is |
| `Fintype.card α` | the number of elements of a finite type `α` |
| `↑n` | a cast: here a natural number `n` read in `ENNReal` or `ℝ` (`Nat.cast`), or `i : Fin n` read in `ℕ` (`Fin.val`) |
| `↑↑a` | both casts: `a : Fin n` → its value in `ℕ` → that number in `ℝ` |
| `x⁻¹` | the inverse `1 / x`; in `ENNReal`, `0⁻¹ = ∞` and `∞⁻¹ = 0` |
| `a.toReal`, `ENNReal.toReal a` | `a : ENNReal` as a real number (`∞` goes to `0`) |
| `∫ (a : α), f a ∂μ` | the (Bochner) integral of `f : α → ℝ` against the measure `μ`: the expectation `E[f]` when `μ` is a probability measure |
| `∑ a, f a` | the sum over every `a` of a finite type |
| `c • x` | scalar multiplication; for `c x : ℝ` it is `c * x` (R9) |
| `j.succ` | the element `j + 1 : Fin (n + 1)` for `j : Fin n` (shifts the index up) |
| `inst✝ : …` | an unnamed type-class hypothesis, such as `Fintype α` |
| `case h` | the label of the side goal `MeasurableSet {a}` that R1 adds when you give it no third argument |

---

## Part 1 · `die_face`

Statement: every face `i : Fin 6` has probability `6⁻¹` under the fair die, as an `ENNReal`. Route:
`intro i` (Lean basics), the measure of `{i}` becomes the PMF's weight at `i` (R1, with R2 for the side goal),
the uniform weight becomes `(card (Fin 6))⁻¹` (R3), and `simp` evaluates the count and the cast (R4, R5).

**R1 · `PMF.toMeasure_apply_singleton`** changes the **goal list**. The lemma is
`PMF.toMeasure_apply_singleton (p : PMF α) (a : α) : MeasurableSet {a} → p.toMeasure {a} = p a`, so
`rw [PMF.toMeasure_apply_singleton p a]` rewrites the goal and adds the side goal `MeasurableSet {a}`. Give the
proof of that side goal as the third argument (`rw [PMF.toMeasure_apply_singleton _ _ hm]`, `_` letting Lean
infer `p` and `a`) and no side goal appears. Placeholders: `{α : Type} [MeasurableSpace α]` (`α` carries a
σ-algebra; `Fin n`, `Bool`, `ℕ`, `ℝ` do), `(p : PMF α) (a : α)`.

| Before | After |
|---|---|
| `⊢ P (p.toMeasure {a})` | `⊢ P (p a)`, `⊢ MeasurableSet {a}` |

**R2 · `measurableSet_singleton`** changes the **goal list**: it closes `MeasurableSet {a}`. The lemma is
`measurableSet_singleton (a : α) : MeasurableSet {a}`. Placeholders: `{α : Type} [MeasurableSpace α]
[MeasurableSingletonClass α]` (one-point sets are measurable; `Fin n`, `Bool`, `ℕ`, `ℝ` qualify),
`(a : α)`.

| Before | After |
|---|---|
| `⊢ MeasurableSet {a}` | no goals |

**R3 · `PMF.uniformOfFintype_apply`** changes the **goal**. The lemma is
`PMF.uniformOfFintype α a = (↑(Fintype.card α))⁻¹`, the cast going `ℕ → ENNReal`. Placeholders:
`{α : Type} [Fintype α] [Nonempty α]` (finitely many elements, at least one; `Fin 6` and `Bool` qualify),
`(a : α)`.

| Before | After |
|---|---|
| `⊢ P ((PMF.uniformOfFintype α) a)` | `⊢ P (↑(Fintype.card α))⁻¹` |

**R4 · `Fintype.card_fin`** changes the **goal**. The lemma is `Fintype.card (Fin n) = n`. Placeholders:
`(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**R5 · `Nat.cast_ofNat`** changes the **goal**. The lemma is `(↑(OfNat.ofNat n) : R) = OfNat.ofNat n` for a
numeral `n ≥ 2`: the natural numeral `5` cast into `ENNReal` is the `ENNReal` numeral `5`. The two print as
`↑5` and `5`. Placeholders: the numeral (here `5`), the target type (here `ENNReal`; any type with a cast from
`ℕ`).

| Before | After |
|---|---|
| `⊢ P ↑5` | `⊢ P 5` |

`simp` applies R4 and R5 by itself, which is all `die_face` needs after R1 and R3. **W1** in `guide.lean` runs
the chain R1 (+R2) → R3 → `simp` on a fair coin `Bool`.

---

## Part 2 · `die_mean`

Statement: the expected face value `E[i + 1]` under the fair die is `7 / 2`, as a real number. The integrand
`((i : ℕ) + 1 : ℝ)` prints as `↑↑i + 1`. Route: the integral over a finite type is a weighted sum (R6); then
`simp [Fin.sum_univ_succ]` evaluates the weights (R3, R4, R5, R7, R8, R9), unrolls the sum over `Fin 6` into
six terms (R10), and evaluates the face values (R11–R13); `norm_num` finishes the arithmetic.

**R6 · `PMF.integral_eq_sum`** changes the **goal**. The lemma is
`∫ a, f a ∂p.toMeasure = ∑ a, (p a).toReal • f a`: on a finite type the expectation is the sum of each value
times its weight, the weight turned into a real number. Placeholders: `{α : Type} [MeasurableSpace α]
[MeasurableSingletonClass α] [Fintype α]` (`Fin 6` qualifies), `(p : PMF α) (f : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (a : α), f a ∂p.toMeasure)` | `⊢ P (∑ a, (p a).toReal • f a)` |

**R7 · `ENNReal.toReal_inv`** changes the **goal**. The lemma is `a⁻¹.toReal = a.toReal⁻¹` (true also at `0`
and `∞`, because `ℝ` has `0⁻¹ = 0`). Placeholders: `(a : ENNReal)`.

| Before | After |
|---|---|
| `⊢ P a⁻¹.toReal` | `⊢ P a.toReal⁻¹` |

**R8 · `ENNReal.toReal_ofNat`** changes the **goal**. The lemma is `(OfNat.ofNat n : ENNReal).toReal =
OfNat.ofNat n` for a numeral `n ≥ 2`. Placeholders: the numeral (here `5`).

| Before | After |
|---|---|
| `⊢ P (ENNReal.toReal 5)` | `⊢ P 5` |

**R9 · `smul_eq_mul`** changes the **goal**. The lemma is `a • b = a * b` when `a` and `b` have the same type.
Placeholders: `(a b : ℝ)` (any type with `*`).

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**W2** in `guide.lean` chains R3 → R4 → R5 → R7 → R8 on one weight of a three-sided die:

```lean-goal
⊢ ((PMF.uniformOfFintype (Fin 3)) a).toReal = 3⁻¹
⊢ (↑(Fintype.card (Fin 3)))⁻¹.toReal = 3⁻¹
⊢ (↑3)⁻¹.toReal = 3⁻¹
⊢ 3⁻¹.toReal = 3⁻¹
⊢ 3.toReal⁻¹ = 3⁻¹
```

The last `rw` also closes the goal: after rewriting, both sides are `3⁻¹` and `rw` tries `rfl`.

**R10 · `Fin.sum_univ_succ`** changes the **goal**. The lemma is
`∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ`: it splits off the term for index `0` and re-indexes the
rest. `simp [Fin.sum_univ_succ]` repeats it until the sum is gone (six terms for `Fin 6`). Placeholders:
`{M : Type} [AddCommMonoid M]` (a commutative `+` with `0`; `ℝ`, `ℕ` qualify), `(n : ℕ) (f : Fin (n + 1) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + ∑ i, f i.succ)` |

**R11 · `Fin.val_succ`** changes the **goal**. The lemma is `↑j.succ = ↑j + 1` in `ℕ`. After R10 the indices
are `0`, `j.succ`, `j.succ.succ`, …; R11 and R12 turn their values into numbers. (`simp` reaches `↑0 = 0` through
`Fin.coe_ofNat_eq_mod` and `Nat.zero_mod` rather than R12; the result is the same.) Placeholders:
`(n : ℕ) (j : Fin n)`.

| Before | After |
|---|---|
| `⊢ P ↑j.succ` | `⊢ P (↑j + 1)` |

**R12 · `Fin.val_zero`** changes the **goal**. The lemma is `↑(0 : Fin (n + 1)) = 0`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑0` | `⊢ P 0` |

**R13 · `Nat.cast_add`, then `Nat.cast_one`** change the **goal**. The lemmas are `↑(m + n) = ↑m + ↑n` and
`↑1 = 1`: the cast `ℕ → ℝ` moves inside a sum. Placeholders: `(m : ℕ)`, target `ℝ` (any type with `+`, `0`,
`1` and a cast from `ℕ`).

| Before | After `rw [Nat.cast_add]` | After `rw [Nat.cast_one]` |
|---|---|---|
| `⊢ P ↑(m + 1)` | `⊢ P (↑m + ↑1)` | `⊢ P (↑m + 1)` |

After `simp [Fin.sum_univ_succ]` the goal is a sum of six products of `6⁻¹` with `1`, `1 + 1`, …; `simp` writes
face `k` as `1 + ⋯ + 1` and does not add the ones up. `norm_num` (TACTIC_STATES, "Closing") does. **W3** in
`guide.lean` shows the same pipeline on a three-sided die with faces `0, 1, 2`:

```lean-goal
⊢ ∫ (a : Fin 3), ↑↑a ∂(PMF.uniformOfFintype (Fin 3)).toMeasure = 1
⊢ ∑ a, ((PMF.uniformOfFintype (Fin 3)) a).toReal • ↑↑a = 1
⊢ 3⁻¹ + 3⁻¹ * (1 + 1) = 1
```

---

## Traps

- Plain `simp` closes `die_face` on its own (it knows R1–R5). Do the `rw` chain anyway: it is what you need
  when `simp` does not finish, and it shows what each lemma does.
- `die_face` lives in `ENNReal`, `die_mean` in `ℝ`. The weights move from one to the other through `toReal`
  (R6), and `toReal` must then be pushed inside `⁻¹` (R7) before the numeral can be read (R8).
- `rw [PMF.toMeasure_apply_singleton p a]` leaves a side goal `MeasurableSet {a}` **after** the main goal.
  Pass `(measurableSet_singleton a)` as the third argument to avoid it.
- `rw` does not see through casts: `↑5` (a natural cast) and `5` are different terms until R5 or `simp`.
- `Fin.sum_univ_succ` needs the type written as `Fin (n + 1)`; `Fin 6` unifies with it (`6 = 5 + 1`), so `simp`
  can apply it repeatedly.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| measure of a point → PMF weight | `rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]` | R1, R2 |
| uniform weight | `rw [PMF.uniformOfFintype_apply]` | R3 |
| `card (Fin n) → n` | `rw [Fintype.card_fin]` | R4 |
| `(↑5 : ENNReal) → 5` | `rw [Nat.cast_ofNat]` | R5 |
| integral over a finite type → sum | `rw [PMF.integral_eq_sum]` | R6 |
| `a⁻¹.toReal → a.toReal⁻¹` | `rw [ENNReal.toReal_inv]` | R7 |
| `(5 : ENNReal).toReal → 5` | `rw [ENNReal.toReal_ofNat]` | R8 |
| `a • b → a * b` | `rw [smul_eq_mul]` | R9 |
| unroll `∑ i : Fin (n+1)` | `simp [Fin.sum_univ_succ]` | R10 |
| index values `↑j.succ`, `↑0` | `rw [Fin.val_succ]`, `rw [Fin.val_zero]` | R11, R12 |
| cast through `+`, `1` | `rw [Nat.cast_add, Nat.cast_one]` (or `push_cast`) | R13 |
| all of R3–R13 at once | `simp [Fin.sum_univ_succ]` | |
| finish the arithmetic | `norm_num` | TACTIC_STATES |
