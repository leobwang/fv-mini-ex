# M191 · Lepton-flavour charges are anomaly free: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `rw [h]`, `simp [h]`, `ring`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md); `unfold` and `exacts [h₁, …]` (close the open goals in
order) are from the easy tier.

**Assumed:** Lean basics (easy tier E001–E033). M190 (one family) uses the same `_decomp` lemmas but is
not required. **New here:** physlib's anomaly-cancellation framework for the Standard Model plus
right-handed neutrinos with `n` families (`SMνCharges n`, `PlusU1 n`, `Sols`, `IsSolution`,
`PlusU1.chargeToAF`, the ACCs and their `_decomp` lemmas, `toSpecies`, `toSpeciesEquiv`), Mathlib's
finite sums `∑ i, f i`, vector literals `![…]`, rationals `ℚ`, and the sign lemmas `Even.neg_pow`,
`Odd.neg_pow`.

**Physics in one paragraph.** Each of the `n` families of SM fermions plus a right-handed neutrino has six
species `Q, U, D, L, E, N` (quark doublet, up and down singlets, lepton doublet, electron singlet, neutrino
singlet; species index `0..5` in that order). A new `U(1)` gauge symmetry gives each (species, family)
pair a rational charge, so a charge assignment is a table `g : Fin 6 → Fin n → ℚ`. physlib writes every
field as a left-handed Weyl fermion, so `U, D, E, N` are the *conjugates* of the right-handed fields and
carry minus their charge. The assignment is consistent only if the six anomaly cancellation conditions
(ACCs) hold: `accGrav` (mixed gravitational), `accSU2`, `accSU3` (mixed with `SU(2)`, `SU(3)`), `accYY`
(mixed with hypercharge squared), `accQuad` (quadratic), `accCube` (cubic). The exercise: lepton flavour
(`x f` on `L`, `−x f` on `E` and `N`, quarks 0; e.g. `L_e − L_μ`) satisfies all six as soon as `∑ f, x f = 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{n : ℕ}` is any number of families. A bracket such as
  `[CommRing R]` is a requirement on `R` (a *type class*: `R` has `+`, `-`, `*`, `0`, `1` with the usual
  commutative-ring laws); `ℚ` qualifies. `[Fintype ι]` says `ι` is finite, so `∑ i, f i` over all of `ι`
  makes sense; `Fin n` qualifies.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℚ` | the rational numbers; all charges are rationals |
| `PlusU1 n`, `SMνCharges n` | physlib's anomaly system for the SM plus right-handed neutrinos with `n` families: an `ACCSystem` (a vector space of charges together with its anomaly equations); `PlusU1 n` has all six ACCs, `SMνCharges n` is its bare charge space |
| `A ≃ B` | a bijection between `A` and `B` with an explicit inverse (`.symm`) |
| `(PlusU1 n).Charges` | charge vectors for `n` families (`6n` rationals); the same type as `(SMνCharges n).Charges` |
| `(PlusU1 n).Sols` | charge vectors bundled with proofs of all six ACCs |
| `sol.val` | the charge vector inside `sol : (PlusU1 n).Sols` |
| `(PlusU1 n).IsSolution S` | `∃ sol, sol.val = S`: `S` satisfies all six ACCs (R2) |
| `toSpeciesEquiv` | the bijection `(SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ)`: vector ↔ (species, family) table |
| `toSpeciesEquiv.symm g` | the charge vector whose table is `g` (`.symm` is the inverse bijection) |
| `(toSpecies j) S` | species `j` of `S`, as a function of the family: an element of `(SMνSpecies n).Charges` |
| `Q S i`, `U S i`, …, `N S i` | charge of species `Q` (`U`, …) in family `i`. `Q` is `toSpecies 0`, …, `N` is `toSpecies 5` |
| `(SMνSpecies n).Charges` | the charges of one species across the families: `Fin (SMνSpecies n).numberCharges → ℚ` |
| `Fin (SMνSpecies n).numberCharges` | the family index of the decomp sums; equal to `Fin n` only after unfolding (R1, Traps) |
| `∑ i, f i` | the sum of `f i` over every `i` of a finite type (here: over the families) |
| `∑ i ∈ s, f i` | the sum over a finite set `s`; `∑ i, f i` is the case `s = univ` (all of the type) |
| `![a₀, a₁, a₂, a₃, a₄, a₅] k` | entry `k` (from 0) of the vector literal; `![0, 0, 0, 1, -1, -1] 3` is `1` (R12) |
| `accGrav S`, …, `accCube S` | the ACC evaluated at `S`: a linear map (`Grav, SU2, SU3, YY`), a quadratic form, a cubic form |
| `x_1`, `x` as a bound variable | the summation index, renamed by `simp` because the name is taken or was lost |
| `-a ^ k`, `-∑ x, f x` | `-(a ^ k)`, `-(∑ x, f x)`: unary minus binds looser than `^` and `∑` |
| `Even k`, `Odd k` | `k` is even (`∃ r, k = r + r`), odd (`∃ m, k = 2 * m + 1`); `even_two : Even 2` |
| `case refine_1` … `refine_6` | the six ACC goals made by R3, in the order Grav, SU2, SU3, YY, Quad, Cube |

---

## Part 1 · `leptonFlavour_isSolution`

Statement: for `n` families, `x : Fin n → ℚ` and `hx : ∑ f, x f = 0`, the charge vector
`leptonFlavour x` (table `g s f = ![0, 0, 0, 1, -1, -1] s * x f`) is a solution of `PlusU1 n`.

The plan: retype `hx` so it matches the decomp sums (R1); build the `Sols` with `PlusU1.chargeToAF`,
which leaves six ACC goals (R2, R3); in each goal expand the ACC into per-species sums (R4–R9), read off
the species charges of `leptonFlavour x` (R10 → R11), and let `simp` clean up (R12–R16), with `hx'` for
the linear ACCs and `Odd.neg_pow` (R17) plus `ring` for the cubic one.

### Before anything: a hypothesis over the right index type

**R1 · `have h' : T' := h`** changes the **context**: it adds `h'`, the same fact as `h : T` but at the type
`T'`, which Lean accepts because `T` and `T'` are equal after unfolding definitions. Here
`T' = (∑ i : Fin (SMνSpecies n).numberCharges, g i = c)`: `SMνSpecies n` is defined with
`numberCharges := n`, so the index types agree after unfolding. `rw` and `simp` match only up to
syntax, so they can use `h'` on a decomp sum but not `h`. Both print the same way, so the infoview does
not show the difference. Placeholders: `{n : ℕ} (g : Fin n → ℚ) (c : ℚ)`.

| Before | After |
|---|---|
| context `h : ∑ i, g i = c` | context `h : ∑ i, g i = c` and `h' : ∑ i, g i = c` (they print the same) |
| `⊢ P (∑ i, g i)` | `⊢ P (∑ i, g i)` (unchanged) |

After R1, `rw [h']` turns the goal into `⊢ P c`; `rw [h]` fails with "did not find an occurrence".

### From `IsSolution` to six anomaly equations

**R2 · `ACCSystem.IsSolution`** is a definition: `χ.IsSolution S` means `∃ sol : χ.Sols, sol.val = S`.
`unfold ACCSystem.IsSolution` changes the **goal** to the `∃`; you do not need it, since `refine ⟨_, _⟩`
sees through the definition. Placeholders: `{n : ℕ} (S : (PlusU1 n).Charges)`.

| Before | After |
|---|---|
| `⊢ (PlusU1 n).IsSolution S` | `⊢ ∃ sol, sol.val = S` |

**R3 · `refine ⟨PlusU1.chargeToAF S ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩`** changes the **goal list**: one goal becomes
six. `PlusU1.chargeToAF` has type
`(S : (PlusU1 n).Charges) → accGrav S = 0 → accSU2 S = 0 → accSU3 S = 0 → accYY S = 0 → accQuad S = 0 → accCube S = 0 → (PlusU1 n).Sols`,
and the result's `.val` is `S` by definition, so `rfl` fills the equation `sol.val = S`. Each `?_` becomes a
goal. Placeholders: `{n : ℕ} (S : (PlusU1 n).Charges)`. Work on each goal with `·` (TACTIC_STATES).

| Before | After |
|---|---|
| `⊢ (PlusU1 n).IsSolution S` | `⊢ accGrav S = 0`, `⊢ accSU2 S = 0`, `⊢ accSU3 S = 0`, `⊢ accYY S = 0`, `⊢ accQuad S = 0`, `⊢ accCube S = 0` |

### Each ACC as sums over families

R4–R9 change the **goal**: the ACC becomes a weighted sum over species of sums over families. Each lemma is
stated for `{n : ℕ} (S : (SMνCharges n).Charges)` and applies to `(PlusU1 n).Charges` (the same type).

**R4 · `rw [accGrav_decomp]`**: `accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i + ∑ i, N S i`.

| Before | After |
|---|---|
| `⊢ accGrav S = 0` | `⊢ 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i + ∑ i, N S i = 0` |

**R5 · `rw [accSU2_decomp]`**: `accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i` (only the `SU(2)` doublets).

| Before | After |
|---|---|
| `⊢ accSU2 S = 0` | `⊢ 3 * ∑ i, Q S i + ∑ i, L S i = 0` |

**R6 · `rw [accSU3_decomp]`**: `accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i` (only the quarks).

| Before | After |
|---|---|
| `⊢ accSU3 S = 0` | `⊢ 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i = 0` |

**R7 · `rw [accYY_decomp]`**: `accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i`
(no `N`: the neutrino has hypercharge 0).

| Before | After |
|---|---|
| `⊢ accYY S = 0` | `⊢ ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i = 0` |

**R8 · `rw [accQuad_decomp]`**: `accQuad S = ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2`.

| Before | After |
|---|---|
| `⊢ accQuad S = 0` | `⊢ ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2 = 0` |

**R9 · `rw [accCube_decomp]`**: `accCube S = 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3 + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3`.

| Before | After |
|---|---|
| `⊢ accCube S = 0` | `⊢ 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3 + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3 = 0` |

### Reading off the species charges

Run R10 and R11 together, as `simp only [yourDef, toSMSpecies_toSpecies_inv]`, **before** any plain `simp`
(Traps).

**R10 · `simp only [C]`** changes the **goal**: a defined name is replaced by its body (here a
`toSpeciesEquiv.symm` of a table). Placeholders: `{n : ℕ} (y : Fin n → ℚ) (i : Fin (SMνSpecies n).numberCharges)`,
and the guide's quark-flavour charge `C y = toSpeciesEquiv.symm fun s f => ![1, -1, -1, 0, 0, 0] s * y f`.

| Before | After |
|---|---|
| `⊢ P (Q (C y) i)` | `⊢ P (Q (toSpeciesEquiv.symm fun s f => ![1, -1, -1, 0, 0, 0] s * y f) i)` |

**R11 · `toSMSpecies_toSpecies_inv`** changes the **goal**: species `j` of the vector built from table `g` is
row `g j` of the table. The lemma: `(toSpecies j) (toSpeciesEquiv.symm g) = g j`. It also fires on `Q`, …,
`N`, which are `toSpecies 0`, …, `toSpecies 5`. Placeholders:
`{n : ℕ} (g : Fin 6 → Fin n → ℚ) (j : Fin 6) (i : Fin (SMνSpecies n).numberCharges)`. When `g` is a
`fun s f => …`, `simp only` also substitutes `s := j`, `f := i` (beta reduction).

| Before | After |
|---|---|
| `⊢ P ((toSpecies j) (toSpeciesEquiv.symm g))` | `⊢ P (g j)` |
| `⊢ P (Q (toSpeciesEquiv.symm g) i)` | `⊢ P (g 0 i)` |

### Cleaning up the numbers

Plain `simp` applies R12–R16 by itself; you never name them. They are here so you can read what `simp` did.

**R12 · `Matrix.cons_val_…`** changes the **goal**: entry `k` of a vector literal becomes that number.
Placeholders: `{α : Type} (a b c d e f : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b, c, d, e, f] 3)` | `⊢ P d` |

**R13 · `zero_mul`, `zero_pow`, `Finset.sum_const_zero`** change the **goal**: `0 * a = 0`, `0 ^ k = 0` for
`k ≠ 0`, `∑ i, 0 = 0`, so a species with charge 0 drops out of its sum. Placeholders:
`{ι R : Type} [Fintype ι] [CommRing R] (f : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, 0 * f i)` | `⊢ P 0` |
| `⊢ P (∑ i, (0 * f i) ^ 2)` | `⊢ P 0` |

**R14 · `neg_mul`, `one_mul`** change the **goal**: `-a * b = -(a * b)` and `1 * b = b`, so `-1 * b` becomes
`-b`, also under `∑` (where `rw` cannot reach the bound variable, `simp` can). Placeholders as R13.

| Before | After |
|---|---|
| `⊢ P (∑ i, -1 * f i)` | `⊢ P (∑ x, -f x)` |

**R15 · `Finset.sum_neg_distrib`** changes the **goal**: `∑ i ∈ s, -f i = -∑ i ∈ s, f i`, a minus sign comes
out of a sum. Placeholders as R13.

| Before | After |
|---|---|
| `⊢ P (∑ i, -f i)` | `⊢ P (-∑ x, f x)` |

**R16 · `Even.neg_pow`** changes the **goal**: `Even k → (-a) ^ k = a ^ k`. With `even_two : Even 2` it
turns `(-a) ^ 2` into `a ^ 2`; `simp` finds `even_two` by itself. Placeholders: `{R : Type} [CommRing R] (a : R)`.

| Before | After |
|---|---|
| `⊢ P ((-a) ^ 2)` | `⊢ P (a ^ 2)` |

**R17 · `Odd.neg_pow`** changes the **goal**: `Odd k → (-a) ^ k = -a ^ k` (read `-a ^ k` as `-(a ^ k)`).
`simp` does **not** prove `Odd 3` by itself, so pass the instance: `simp [Odd.neg_pow (by decide : Odd 3)]`;
`decide` checks `Odd 3` by computation. Without it `simp` leaves `(-y x) ^ 3` inside the sums and `ring`
fails. Placeholders: `{R : Type} [CommRing R] (a : R)`.

| Before | After |
|---|---|
| `⊢ P ((-a) ^ 3)` | `⊢ P (-a ^ 3)` |

### What is left, per ACC

After R10 → R11 and `simp`, each goal is a numeric combination of `s₁ = ∑ f, x f` (linear ACCs) or of
`∑ f, x f ^ k` (quadratic, cubic). For lepton flavour (`L: +1`, `E, N: −1`):

| ACC | Coefficients `L, E, N` | Left after `simp` | Finish |
|---|---|---|---|
| Grav | `2, 1, 1` | `2 s₁ − s₁ − s₁` | `simp [hx']` |
| SU2 | `1, 0, 0` | `s₁` | `simp [hx']` |
| SU3 | `0, 0, 0` | nothing (no leptons) | `simp` |
| YY | `3, 6, 0` | `3 s₁ − 6 s₁` | `simp [hx']` |
| Quad | `−1, 1, 0` | `−∑x² + ∑x²`, cancelled by `simp` | `simp` |
| Cube | `2, 1, 1` | `2∑x³ − ∑x³ − ∑x³` | `simp [R17, …]`, then `ring` |

### Worked combinations (W1–W3, on the quark-flavour charge `C y`, not the exercise's)

`C y` gives `y f` to `Q` and `−y f` to `U`, `D`.

**W1: a linear ACC that needs no sum hypothesis.** R6, then R10 → R11 in one `simp only`, then `simp`
(R12–R15), then `ring`:

```lean-goal
⊢ accSU3 (C y) = 0
⊢ 2 * ∑ i, Q (C y) i + ∑ i, U (C y) i + ∑ i, D (C y) i = 0
⊢ 2 * ∑ x, ![1, -1, -1, 0, 0, 0] 0 * y x + ∑ x, ![1, -1, -1, 0, 0, 0] 1 * y x + ∑ x, ![1, -1, -1, 0, 0, 0] 2 * y x = 0
⊢ 2 * ∑ x, y x + -∑ x, y x + -∑ x, y x = 0
```

**W2: a linear ACC that needs `∑ y = 0`.** R1 first (`hy'`), then R5, R10 → R11, and `simp [hy']` closes it:

```lean-goal
⊢ accSU2 (C y) = 0
⊢ 3 * ∑ i, Q (C y) i + ∑ i, L (C y) i = 0
⊢ 3 * ∑ x, ![1, -1, -1, 0, 0, 0] 0 * y x + ∑ x, ![1, -1, -1, 0, 0, 0] 3 * y x = 0
```

**W3: the cubic ACC.** R9, R10 → R11, `simp [Odd.neg_pow (by decide : Odd 3)]` (R17, with R12–R15
automatic), then `ring` closes the identity in the atom `∑ x, y x ^ 3`:

```lean-goal
⊢ 6 * ∑ i, Q (C y) i ^ 3 + 3 * ∑ i, U (C y) i ^ 3 + 3 * ∑ i, D (C y) i ^ 3 + 2 * ∑ i, L (C y) i ^ 3 + ∑ i, E (C y) i ^ 3 + ∑ i, N (C y) i ^ 3 = 0
⊢ 6 * ∑ x, y x ^ 3 + -(3 * ∑ x, y x ^ 3) + -(3 * ∑ x, y x ^ 3) = 0
```

---

## Traps

- `hx : ∑ f, x f = 0` sums over `Fin n`; the decomp sums run over `Fin (SMνSpecies n).numberCharges`. They
  print identically, but `rw [hx]` fails and `simp [hx]` reports `hx` as unused. Retype it first (R1):
  `have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx`.
- Plain `simp [leptonFlavour]` unfolds `toSpecies` before R11 can match, and gets stuck at
  `toSpeciesEquiv (toSpeciesEquiv.symm fun s f => …) 0 x_1`. Always run
  `simp only [leptonFlavour, toSMSpecies_toSpecies_inv]` first.
- `simp` proves `Even 2` but not `Odd 3`: the cubic needs `Odd.neg_pow (by decide : Odd 3)` (R17).
- `simp` leaves `2 * s + -s + -s = 0` for a sum `s` it cannot evaluate; `ring` (TACTIC_STATES) closes it,
  treating `s` as an unknown.
- Charges of `E`, `N` are `−x f`, not `+x f`: physlib stores right-handed fields as left-handed conjugates.
- After R3, work on the six goals one at a time with `·`; `t1 ; t2` runs `t2` on the first goal only.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `hx` usable on decomp sums | `have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx` | R1 |
| what `IsSolution` means | `∃ sol : (PlusU1 n).Sols, sol.val = S` | R2 |
| `IsSolution` → six ACC goals | `refine ⟨PlusU1.chargeToAF S ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩` | R3 |
| ACC → sums over families | `rw [accGrav_decomp]` (`accSU2_`, `accSU3_`, `accYY_`, `accQuad_`, `accCube_decomp`) | R4–R9 |
| species charges of your vector | `simp only [yourDef, toSMSpecies_toSpecies_inv]` | R10, R11 |
| evaluate `![…] k`, drop zeros, pull out `-` | `simp` | R12–R15 |
| linear ACC with `∑ x = 0` | `simp [hx']` | R1, TACTIC_STATES |
| `(-a) ^ 2` | `simp` (finds `even_two`) | R16 |
| `(-a) ^ 3` | `simp [Odd.neg_pow (by decide : Odd 3)]` | R17 |
| `2 * s + -s + -s = 0` | `ring` | TACTIC_STATES |
| see the state | infoview | |
