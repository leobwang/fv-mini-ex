# E126 · Hypercharge cancels the linear anomalies: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's anomaly-cancellation setup for
the Standard Model with right-handed neutrinos (SMν): charge spaces `(SMνCharges n).Charges`, the species
projections `Q U D L E N`, the three linear anomaly maps `accGrav`, `accSU2`, `accSU3` and their
`_decomp` lemmas; Mathlib's vector literal `![…]` and big sums `∑ i, f i`.

The physics. One SM family plus a right-handed neutrino is 6 *species* of left-handed Weyl fermions
(right-handed fields enter through their conjugates, which is why `U, D, E, N` carry the opposite sign of
the usual hypercharge):

| Species | Field | SU(3) dim | SU(2) dim | multiplicity (SU(3) dim × SU(2) dim) |
|---|---|---|---|---|
| `Q` | quark doublet | 3 | 2 | 6 |
| `U`, `D` | conjugate up / down quark | 3 | 1 | 3 each |
| `L` | lepton doublet | 1 | 2 | 2 |
| `E`, `N` | conjugate electron / neutrino | 1 | 1 | 1 each |

A U(1) charge assignment gives each species one rational number per family. A gauge anomaly is a
triangle-diagram coefficient; for the new U(1) these three are linear in the charges `q`:
gravitational `Σ (multiplicity) q`, SU(2)²×U(1) `Σ_{doublets} (colour dim) q = 3·Q + L`, and
SU(3)²×U(1) `Σ_{triplets} (isospin dim) q = 2·Q + U + D`. The theorem says hypercharge (scaled by 6 to be
integral) makes all three vanish. With one family each sum over families has one term, and the proof
is: rewrite each anomaly as sums (R2–R4), collapse the sums (R5, R6), plug in the numbers (R7, R8).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ACCSystemCharges` | physlib's structure holding one natural number, `numberCharges` (how many charges there are) |
| `(SMνCharges n).Charges` | a charge assignment for `n` families: a function `Fin (6 * n) → ℚ`, one rational per species per family |
| `(SMνSpecies n).Charges` | the charges of one species across the `n` families: `Fin n → ℚ` |
| `Fin (SMνSpecies 1).numberCharges` | the index type of the single family; it has one element, `⟨0, _⟩` |
| `Q S i`, `U S i`, … `N S i` | the charge of species `Q` (resp. `U D L E N`) in family `i` under `S`. `Q` is `toSpecies 0`, …, `N` is `toSpecies 5` |
| `toSpecies j S`, `(toSpecies j) S` | the projection of `S` onto species `j : Fin 6`, a map `Fin n → ℚ` (`toSpecies j` is a `ℚ`-linear map applied to `S`) |
| `toSpeciesEquiv ![…] j x` | the bijection `(SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ)` behind `toSpecies`. You only see it if you unfold `Y` too early (Traps) |
| `accGrav S`, `accSU2 S`, `accSU3 S` | the three linear anomalies of `S`. They are `ℚ`-linear maps (`→ₗ[ℚ] ℚ`), applied to `S` like functions |
| `∑ i, f i` | Mathlib's finite sum `Finset.sum Finset.univ f` over all `i` of a finite type |
| `![a, b, c]` | Mathlib's vector literal: the function `Fin 3 → α` with entries `a, b, c` (counted from 0) |
| `⟨0, sum_one._proof_1⟩` | the element `0` of the one-family index type, paired with the proof `0 < 1` that `sum_one` supplied |
| `Y 0`, `S 0` | entry 0 of a charge vector. Lean prints it, but you cannot type it: write `S (0 : Fin 6)` (R6) |
| `case refine_1` | the first of the goals made by `refine ⟨?_, ?_, ?_⟩` |

---

## Part 1 · `Y_linear`

Statement: `accGrav Y = 0 ∧ accSU2 Y = 0 ∧ accSU3 Y = 0` for the one-family hypercharge
`Y = ![1, -4, 2, -3, 6, 0]` in species order `(Q, U, D, L, E, N)`. Three equations in `ℚ`.

### Splitting the goal

**R1 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: one goal becomes three. `∧` nests to the right, so
`A ∧ B ∧ C` is `A ∧ (B ∧ C)`, and the pattern needs one `?_` per conjunct. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C` | `⊢ A`, `⊢ B`, `⊢ C` |

### Anomaly → sums

`accGrav` etc. are defined as a single sum over families of a weighted sum over species. The `_decomp`
lemmas split that into one sum per species. All three hold for any number of families `n`.
Placeholders for R2–R4: `{n : ℕ} (S : (SMνCharges n).Charges)`.

**R2 · `rw [accGrav_decomp]`** changes the **goal**. The lemma is
`accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i + ∑ i, N S i`
(the coefficients are the multiplicities in the table above).

| Before | After |
|---|---|
| `⊢ P (accGrav S)` | `⊢ P (6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i + ∑ i, N S i)` |

**R3 · `rw [accSU2_decomp]`** changes the **goal**. The lemma is `accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i`.

| Before | After |
|---|---|
| `⊢ P (accSU2 S)` | `⊢ P (3 * ∑ i, Q S i + ∑ i, L S i)` |

**R4 · `rw [accSU3_decomp]`** changes the **goal**. The lemma is
`accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i`.

| Before | After |
|---|---|
| `⊢ P (accSU3 S)` | `⊢ P (2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i)` |

### One family: collapse the sums

**R5 · `simp only [sum_one]`** changes the **goal**. The lemma is
`sum_one : ∑ i, f i = f ⟨0, _⟩` for `f : Fin (SMνSpecies 1).numberCharges → M`: a sum over a one-element
type is its one term. Placeholders: `{M : Type} [AddCommMonoid M]` (`M` has `+` and `0`; `ℚ` qualifies),
`(f : Fin (SMνSpecies 1).numberCharges → M)`. In the exercise `f` is `Q Y`, `U Y`, …. Use `simp only`, not
`rw`: `rw` rewrites only the first sum's pattern, `simp only` all six.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f ⟨0, sum_one._proof_1⟩)` |

**R6 · `simp only [toSpecies_one]`** changes the **goal**. The lemma is
`toSpecies_one : toSpecies j S ⟨0, _⟩ = S j` for `S : (SMνCharges 1).Charges` and `j : Fin 6`: with one
family, species `j` in family 0 is entry `j` of `S`. Because `Q`, …, `N` unfold to `toSpecies 0`, …,
`toSpecies 5`, it rewrites `Q S ⟨0, _⟩` to `S 0` and so on. Placeholders: `(S : (SMνCharges 1).Charges)`,
`(hi : 0 < (SMνSpecies 1).numberCharges)` (any proof of `0 < 1` works in the pair).

| Before | After |
|---|---|
| `⊢ P (Q S ⟨0, hi⟩ + U S ⟨0, hi⟩)` | `⊢ P (S 0 + S 1)` |

### Numbers

**R7 · `simp [V]`** changes the **goal**: it unfolds the definition `V := ![…]` and reads off each entry
(Mathlib's `Matrix.cons_val_…` lemmas). It also tidies `x * 1`, `x * 0`, `x + 0` and turns `a * -b` into
`-(a * b)`, but it does **not** multiply or add rational numerals. Placeholders: `V` defined by
`def V : (SMνCharges 1).Charges := ![2, -5, 0, 0, 0, 1]`.

| Before | After |
|---|---|
| `⊢ P (V 0 + 3 * V 1 + 4 * V 2)` | `⊢ P (2 + -(3 * 5))` |

Sometimes this already closes the goal (an equation such as `3 + -3 = 0` that `simp` recognises).

**R8 · `norm_num`** **closes** an equation between rational numerals, such as `(2 : ℚ) + -(3 * 4) + 5 * 2 = 0`.

### Worked combination (W1, on a charge vector that is not the exercise's)

**W1: B − L cancels the SU(3) anomaly.** `BL = ![1, -1, -1, -3, 3, 3]` (baryon minus lepton number, times 3).
R4, R5, R6, R7, R8 in order:

```lean-goal
⊢ accSU3 BL = 0
⊢ 2 * ∑ i, Q BL i + ∑ i, U BL i + ∑ i, D BL i = 0
⊢ 2 * Q BL ⟨0, sum_one._proof_1⟩ + U BL ⟨0, sum_one._proof_1⟩ + D BL ⟨0, sum_one._proof_1⟩ = 0
⊢ 2 * BL 0 + BL 1 + BL 2 = 0
⊢ 2 + -1 + -1 = 0
```

---

## Traps

- **Order matters: R5, R6 before `simp [Y]`.** If you unfold `Y` first (`simp [Y]` right after R2), `simp`
  rewrites `Q Y i` into `toSpeciesEquiv ![…] 0 i` and stops; `sum_one`/`toSpecies_one` no longer match and
  neither `norm_num` nor `rfl` gets past `toSpeciesEquiv`. Undo and collapse the sums first.
- **You cannot write `Y 0`.** The index type of `Y` is `Fin (SMνCharges 1).numberCharges`, which has no
  numerals. Lean prints `Y 0` after R6, but if you state a helper fact yourself, write `Y (0 : Fin 6)`.
- `simp [Y]` may already close a goal (the SU(2) one does); a `norm_num` after it then fails
  with "no goals". Check the infoview before adding R8.
- `rw [sum_one]` rewrites the instances of one sum only; use `simp only [sum_one]` (R5).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B ∧ C` | `refine ⟨?_, ?_, ?_⟩` | R1 |
| gravitational anomaly → species sums | `rw [accGrav_decomp]` | R2 |
| SU(2) anomaly → `3 ∑Q + ∑L` | `rw [accSU2_decomp]` | R3 |
| SU(3) anomaly → `2 ∑Q + ∑U + ∑D` | `rw [accSU3_decomp]` | R4 |
| one family: sum → its one term | `simp only [sum_one]` | R5 |
| `Q S ⟨0, _⟩` → `S 0` (all six species) | `simp only [toSpecies_one]` | R6 |
| plug in a `![…]` vector | `simp [V]` | R7 |
| rational arithmetic | `norm_num` | R8 |
| see the state | infoview | |
