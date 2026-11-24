# H115 · Hypercharge can be added to any anomaly-free assignment: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's anomaly-cancellation library:
ACC systems (`ACCSystem`) and their solution structures (`LinSols`, `QuadSols`, `Sols`, `IsSolution`),
the Standard Model with right-handed neutrinos (`SMνCharges`, species maps `Q U D L E N`,
`familyUniversal`), symmetric bilinear and trilinear forms (`BiLinearSymm`, `TriLinearSymm`) and
homogeneous forms (`HomogeneousQuadratic`, `HomogeneousCubic`); Mathlib's finite sums `∑`; the tactics
`change` and `repeat`.

**The math.** A charge assignment gives each of the 6 species $f \in \{Q, U, D, L, E, N\}$ (quark doublet,
up and down antiquarks, lepton doublet, charged antilepton, antineutrino) in each family $i < n$ a
rational U(1) charge $S_f(i)$. The species have multiplicities $d = (6, 3, 3, 2, 1, 1)$ (colour × isospin).
Write $B$ = `quadBiLin` (symmetric bilinear), $\tau$ = `cubeTriLin` (symmetric trilinear), so that
`accQuad S` $= B(S,S)$ and `accCube S` $= \tau(S,S,S) = \sum_{f,i} d_f S_f(i)^3$. Hypercharge on one family
is $Y_1 = (1, -4, 2, -3, 6, 0)$; $Y$ = `PlusU1.Y n` is $Y_1$ copied to every family. Then, for every $S$:

1. $B(Y, S) = $ `accYY S` (milestone `quadBiLin_Y`).
2. $\tau(Y, Y, S) = 6\,$`accYY S` (milestone `cubeTriLin_Y_Y`).
3. $\tau(Y, S, S) = 6\,$`accQuad S` (milestone `cubeTriLin_Y_S_S`).
4. $B(aS+bY, aS+bY) = a^2 B(S,S) + b^2 B(Y,Y) + 2ab\,B(Y,S)$ (milestone `accQuad_shift`).
5. $c(aS+bY) = a^3\tau(S,S,S) + b^3\tau(Y,Y,Y) + 3a^2b\,\tau(S,S,Y) + 3ab^2\,\tau(Y,Y,S)$, where $c(X) = \tau(X,X,X)$ (milestone `accCube_shift`).

If $S$ solves all ACCs, `accYY S = accQuad S = 0`, so every cross term vanishes; $Y$ itself is a solution;
the linear ACCs are linear, so $aS + bY$ satisfies them for free. Hence $aS + bY$ is a solution.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℚ → Prop`, or `P : ℚ → ℚ → Prop` for two spots). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders. `{V : Type} [AddCommMonoid V] [Module ℚ V]` means: `V` is any
  ℚ-vector space (a *type class* requirement). `(SMνCharges n).Charges` qualifies.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `(SMνCharges n).Charges` | charge assignments for `n` families: functions `Fin (6 * n) → ℚ` |
| `(PlusU1 n)` | the ACC system: those charges with 4 linear ACCs (`accGrav`, `accSU2`, `accSU3`, `accYY`), 1 quadratic (`accQuad`), 1 cubic (`accCube`) |
| `accGrav S`, `accSU2 S`, `accSU3 S`, `accYY S` | the linear ACCs: mixed gravity–U(1), SU(2)²–U(1), SU(3)²–U(1), hypercharge²–U(1) anomalies; each is a weighted sum of charges (R2 for `accYY`) |
| `accQuad S`, `accCube S` | the quadratic ACC $B(S,S)$ (hypercharge–U(1)², R11) and the cubic ACC $\tau(S,S,S)$ (U(1)³) |
| `(PlusU1 n).Charges` | the same type as `(SMνCharges n).Charges` under another name (Traps) |
| `(PlusU1 n).LinSols` / `.QuadSols` / `.Sols` | structures: a charge `.val` plus proofs that it solves the linear / linear+quadratic / all ACCs |
| `S.1`, `S.1.1`, `S.toLinSols` | for `S : Sols`: the underlying `QuadSols`, then `LinSols` (R23). `S.1.1.val` prints as `S.val` |
| `(PlusU1 n).IsSolution T` | `∃ sol : (PlusU1 n).Sols, sol.val = T` |
| `a • S` | scalar `a : ℚ` times the charge vector `S` |
| `Q S i`, `U S i`, …, `N S i` | charge of species Q, U, D, L, E, N in family `i : Fin n` |
| `(toSpecies j) S i` | the same thing, species `j : Fin 6` (`Q = toSpecies 0`, …, `N = toSpecies 5`); `rw` prints this form |
| `toSpeciesEquiv S j x` | the same number again: what `simp` unfolds `toSpecies j S x` to |
| `∑ i, f i` | the sum of `f i` over all `i : Fin n` |
| `(quadBiLin S) T` | $B(S, T)$; the brackets appear because a bilinear form is a function returning a function |
| `((cubeTriLin S) T) R` | $\tau(S, T, R)$ |
| `quadBiLin.toHomogeneousQuad S`, `cubeTriLin.toCubic S` | $B(S,S)$, $\tau(S,S,S)$: the unfolded `accQuad S`, `accCube S` |
| `BiLinearSymm V`, `TriLinearSymm V` | symmetric ℚ-bilinear / trilinear forms on `V` |
| `HomogeneousQuadratic V`, `HomogeneousCubic V` | maps `f : V → ℚ` with `f (a • S) = a ^ 2 * f S` / `a ^ 3 * f S` |
| `(familyUniversal n) S₁` | the one-family charge `S₁ : (SMνCharges 1).Charges` copied to all `n` families |
| `![a₀, a₁, …, a₅]` | (guide.lean, W1) the function `Fin 6 → ℚ` sending `j` to `aⱼ`; a one-family charge |
| `PlusU1.Y₁`, `PlusU1.Y n` | hypercharge on one family (a `Sols` of `PlusU1 1`), and on `n` families |
| `⟨0, toSpecies_familyUniversal._proof_1⟩`, `⟨0, Nat.zero_lt_one⟩` | family `0 : Fin 1`: an element of `Fin 1` is a pair ⟨value, proof that value < 1⟩; the proof's name does not matter |
| `case refine_1` | the first goal `refine` left open |

---

## Part 1 · `quadBiLin_Y` (milestone)

Statement: `quadBiLin (PlusU1.Y n).val S = accYY S` for every `S : (SMνCharges n).Charges`. Pairing with
hypercharge in $B$ is the hypercharge²–charge anomaly.

**R1 · `rw [quadBiLin_decomp]`** changes the **goal**: $B(S,T)$ becomes its species sums. Statement:
`quadBiLin S T = ∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i + ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i`.
Placeholders: `{n : ℕ} (S T : (SMνCharges n).Charges)`. N does not appear (weight 0).

| Before | After |
|---|---|
| `⊢ P ((quadBiLin S) T)` | `⊢ P (∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i + ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i)` |

**R2 · `rw [accYY_decomp]`** changes the **goal**. Statement:
`accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i`.
Placeholders: `{n : ℕ} (S : (SMνCharges n).Charges)`.

| Before | After |
|---|---|
| `⊢ P (accYY S)` | `⊢ P (∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i)` |

**R3 · `rw [PlusU1.Y_val]`** changes the **goal**: `PlusU1.Y_val n : (PlusU1.Y n).val = familyUniversal n PlusU1.Y₁.val`.
Placeholders: `{n : ℕ}`.

| Before | After |
|---|---|
| `⊢ P (PlusU1.Y n).val` | `⊢ P ((familyUniversal n) PlusU1.Y₁.val)` |

**R4 · `rw [sum_familyUniversal_two]`** changes the **goal**: a universal charge is constant over families,
so it leaves the sum. Statement, for species `j : Fin 6`:
`∑ i, toSpecies j (familyUniversal n S₁) i * toSpecies j T i = toSpecies j S₁ ⟨0, _⟩ * ∑ i, toSpecies j T i`.
Placeholders: `{n : ℕ} (S₁ : (SMνCharges 1).Charges) (T : (SMνCharges n).Charges)`. It matches `Q`, `U`, …
directly (they are abbreviations of `toSpecies j`).

| Before | After |
|---|---|
| `⊢ P (∑ i, Q ((familyUniversal n) S₁) i * Q T i)` | `⊢ P ((toSpecies 0) S₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 0) T i)` |

**R5 · `repeat rw [l]`** changes the **goal**: it runs `rw [l]` until it fails. One `rw [l]` fixes `l`'s free
arguments (here the species `j`) at the first match and rewrites only that instance, so five species need five
rewrites. `repeat` never fails, so check the state afterwards. Placeholders as in R4.

| Before | After |
|---|---|
| `⊢ P (∑ i, Q ((familyUniversal n) S₁) i * Q T i) (∑ i, U ((familyUniversal n) S₁) i * U T i)` | `⊢ P ((toSpecies 0) S₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 0) T i) ((toSpecies 1) S₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 1) T i)` |

**R6 · `simp only [toSpecies_one]`** changes the **goal**: with one family, species `j` of family 0 is entry `j`.
Statement: `toSpecies_one S₁ j : toSpecies j S₁ ⟨0, _⟩ = S₁ j`. Placeholders: `(S₁ : (SMνCharges 1).Charges)`.

| Before | After |
|---|---|
| `⊢ P ((toSpecies 3) S₁ ⟨0, Nat.zero_lt_one⟩)` | `⊢ P (S₁ 3)` |

**R7 · `simp [PlusU1.Y₁]`** changes the **goal**: `PlusU1.Y₁.val j` becomes the number
$(1, -4, 2, -3, 6, 0)_j$. `simp only [PlusU1.Y₁_val]` does just this; plain `simp` also normalises the rest of
the goal (unfolds `toSpecies` to `toSpeciesEquiv`, cancels equal summands), so its output is not
predictable term by term: follow it with R8. Placeholders: none.

| Before | After |
|---|---|
| `⊢ P (PlusU1.Y₁.val 1) (PlusU1.Y₁.val 4)` | `⊢ P (-4) 6` |

**R8 · `ring`** **closes** an identity of commutative rings. Each sum `∑ x, f x` is an unknown to it, so it
proves `2 * (4 * s) = 8 * s` for a sum `s` but never moves anything inside a `∑`. Placeholders:
`(f g : Fin n → ℚ)`.

| Before | After |
|---|---|
| `⊢ 2 * (4 * ∑ x, f x) + -∑ x, g x = 8 * ∑ x, f x - ∑ x, g x` | no goals |

**W1: the whole chain on another universal charge.** `BL₁ = ![1, -1, -1, -3, 3, 3]` (a B−L pattern). R1, then
R5 with R4, R6, R7 (`simp [BL₁]`), R8:

```lean-goal
⊢ (quadBiLin ((familyUniversal n) BL₁)) S = ∑ i, Q S i + 2 * ∑ i, U S i - ∑ i, D S i + 3 * ∑ i, L S i + 3 * ∑ i, E S i
⊢ ∑ i, Q ((familyUniversal n) BL₁) i * Q S i - 2 * ∑ i, U ((familyUniversal n) BL₁) i * U S i + ∑ i, D ((familyUniversal n) BL₁) i * D S i - ∑ i, L ((familyUniversal n) BL₁) i * L S i + ∑ i, E ((familyUniversal n) BL₁) i * E S i = ∑ i, Q S i + 2 * ∑ i, U S i - ∑ i, D S i + 3 * ∑ i, L S i + 3 * ∑ i, E S i
⊢ (toSpecies 0) BL₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 0) S i - 2 * ((toSpecies 1) BL₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 1) S i) + (toSpecies 2) BL₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 2) S i - (toSpecies 3) BL₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 3) S i + (toSpecies 4) BL₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 4) S i = ∑ i, Q S i + 2 * ∑ i, U S i - ∑ i, D S i + 3 * ∑ i, L S i + 3 * ∑ i, E S i
⊢ BL₁ 0 * ∑ i, (toSpecies 0) S i - 2 * (BL₁ 1 * ∑ i, (toSpecies 1) S i) + BL₁ 2 * ∑ i, (toSpecies 2) S i - BL₁ 3 * ∑ i, (toSpecies 3) S i + BL₁ 4 * ∑ i, (toSpecies 4) S i = ∑ i, Q S i + 2 * ∑ i, U S i - ∑ i, D S i + 3 * ∑ i, L S i + 3 * ∑ i, E S i
⊢ ∑ x, toSpeciesEquiv S 0 x + 2 * ∑ x, toSpeciesEquiv S 1 x + -∑ x, toSpeciesEquiv S 2 x = ∑ x, toSpeciesEquiv S 0 x + 2 * ∑ x, toSpeciesEquiv S 1 x - ∑ x, toSpeciesEquiv S 2 x
```

The last line is after `simp [BL₁]`: it already cancelled the L and E summands; `ring` closes the rest.

---

## Part 2 · `cubeTriLin_Y_Y` (milestone)

Statement: `cubeTriLin (PlusU1.Y n).val (PlusU1.Y n).val S = 6 * accYY S`. Same chain as Part 1 with the
trilinear form: R9, R2, R3; R5 with R10, then R5 with R4 (R10 leaves two-factor sums); R6, R7, R8.

**R9 · `rw [cubeTriLin_decomp]`** changes the **goal**: $\tau(S,T,R) = \sum_f d_f \sum_i S_f(i)T_f(i)R_f(i)$ with
weights $d = (6,3,3,2,1,1)$. Placeholders: `{n : ℕ} (S T R : (SMνCharges n).Charges)`.

| Before | After |
|---|---|
| `⊢ P (((cubeTriLin S) T) R)` | `⊢ P (6 * ∑ i, Q S i * Q T i * Q R i + 3 * ∑ i, U S i * U T i * U R i + 3 * ∑ i, D S i * D T i * D R i + 2 * ∑ i, L S i * L T i * L R i + ∑ i, E S i * E T i * E R i + ∑ i, N S i * N T i * N R i)` |

**R10 · `rw [sum_familyUniversal_three]`** changes the **goal**: the three-factor version of R4. Statement:
`∑ i, toSpecies j (familyUniversal n S₁) i * toSpecies j T i * toSpecies j R i = toSpecies j S₁ ⟨0, _⟩ * ∑ i, toSpecies j T i * toSpecies j R i`.
The universal charge must be the **first** factor. Placeholders:
`{n : ℕ} (S₁ : (SMνCharges 1).Charges) (T R : (SMνCharges n).Charges)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, Q ((familyUniversal n) S₁) i * Q T i * Q R i)` | `⊢ P ((toSpecies 0) S₁ ⟨0, toSpecies_familyUniversal._proof_1⟩ * ∑ i, (toSpecies 0) T i * (toSpecies 0) R i)` |

---

## Part 3 · `cubeTriLin_Y_S_S` (milestone)

Statement: `cubeTriLin (PlusU1.Y n).val S S = 6 * accQuad S`. Chain: R9, R11, R3; R5 with R10 (one universal
factor per sum, so R4 is not needed); R6; R7 together with R12 in one `simp`; R8.

**R11 · `rw [accQuad_decomp]`** changes the **goal**. Statement:
`accQuad S = ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2`.
Placeholders: `{n : ℕ} (S : (SMνCharges n).Charges)`.

| Before | After |
|---|---|
| `⊢ P (accQuad S)` | `⊢ P (∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2)` |

**R12 · `sq`** changes the **goal**: `sq x : x ^ 2 = x * x`. The left side of the milestone has
`∑ i, S i * S i`, the right side `∑ i, S i ^ 2`; `ring` cannot look inside a `∑` (R8), so pass `sq` to the
`simp` of R7: `simp [PlusU1.Y₁, sq]`. Placeholders: `(x : ℚ)` (any monoid).

| Before | After |
|---|---|
| `⊢ P (x ^ 2)` | `⊢ P (x * x)` |

---

## Part 4 · `accQuad_shift` (milestone)

Statement: from `quadBiLin Y S = 0`, `accQuad S = 0`, `accQuad Y = 0`, conclude
`accQuad (a • S + b • Y) = 0`. Pure algebra of the form $q(S) = B(S,S)$; `S Y` are arbitrary charges here.

**R13 · `change G'`** changes the **goal** to `G'`, which must be the same statement after unfolding
definitions (Lean checks this). `accQuad` is defined as `quadBiLin.toHomogeneousQuad` and `accCube` as
`cubeTriLin.toCubic`; `rw` only matches literally, so use `change` to switch to the form a lemma (R14, R19)
is stated in, and back to the form your hypotheses are stated in. Placeholders: `{n : ℕ} (S : (SMνCharges n).Charges)`.

| Before | After |
|---|---|
| `⊢ P (accQuad S) (accCube S)` | `⊢ P (quadBiLin.toHomogeneousQuad S) (cubeTriLin.toCubic S)` |

**R14 · `rw [BiLinearSymm.toHomogeneousQuad_add]`** changes the **goal**: $q(S+T) = q(S) + q(T) + 2B(S,T)$.
Placeholders: `{V : Type} [AddCommMonoid V] [Module ℚ V] (B : BiLinearSymm V) (S T : V)`.

| Before | After |
|---|---|
| `⊢ P (B.toHomogeneousQuad (S + T))` | `⊢ P (B.toHomogeneousQuad S + B.toHomogeneousQuad T + 2 * (B S) T)` |

**R15 · `rw [HomogeneousQuadratic.map_smul]`** changes the **goal**: `f (a • S) = a ^ 2 * f S`. `accQuad` is a
`HomogeneousQuadratic`. Placeholders: `{V : Type} [AddCommMonoid V] [Module ℚ V] (f : HomogeneousQuadratic V) (a : ℚ) (S : V)`.

| Before | After |
|---|---|
| `⊢ P (f (a • S))` | `⊢ P (a ^ 2 * f S)` |

**R16 · `rw [BiLinearSymm.map_smul₁]`** changes the **goal**: `B (a • S) T = a * B S T` (first slot).
Placeholders: `(B : BiLinearSymm V) (a : ℚ) (S T : V)`, `V` as in R14.

| Before | After |
|---|---|
| `⊢ P ((B (a • S)) T)` | `⊢ P (a * (B S) T)` |

**R17 · `rw [BiLinearSymm.map_smul₂]`** changes the **goal**: `B S (a • T) = a * B S T` (second slot).
Placeholders as in R16.

| Before | After |
|---|---|
| `⊢ P ((B S) (a • T))` | `⊢ P (a * (B S) T)` |

**R18 · `rw [BiLinearSymm.swap]`** changes the **goal**: `B S T = B T S`. Without arguments it swaps the first
`B _ _` it finds (and every identical copy); `rw [BiLinearSymm.swap quadBiLin S Y]` picks one. Needed because
R14 produces `B S Y` while the hypothesis is about `B Y S`. Placeholders as in R16.

| Before | After |
|---|---|
| `⊢ P ((B S) T)` | `⊢ P ((B T) S)` |

**W2: the quadratic ACC of a plain sum.** From `hS : accQuad S = 0`, `hT : accQuad T = 0`,
`hTS : quadBiLin T S = 0`: R13, R14, R13 back, then `rw [BiLinearSymm.swap, hS, hT, hTS]`, `norm_num`.

```lean-goal
⊢ accQuad (S + T) = 0
⊢ quadBiLin.toHomogeneousQuad (S + T) = 0
⊢ quadBiLin.toHomogeneousQuad S + quadBiLin.toHomogeneousQuad T + 2 * (quadBiLin S) T = 0
⊢ accQuad S + accQuad T + 2 * (quadBiLin S) T = 0
⊢ 0 + 0 + 2 * 0 = 0
```

---

## Part 5 · `accCube_shift` (milestone)

Statement: from `τ Y Y S = 0`, `τ Y S S = 0`, `accCube S = 0`, `accCube Y = 0`, conclude
`accCube (a • S + b • Y) = 0`. Chain: R13, R19, R13 back; R20 twice; R21; R22; the hypotheses; R8.

**R19 · `rw [TriLinearSymm.toCubic_add]`** changes the **goal**:
$c(S+T) = c(S) + c(T) + 3\tau(S,S,T) + 3\tau(T,T,S)$ with $c(S) = \tau(S,S,S)$.
Placeholders: `{V : Type} [AddCommMonoid V] [Module ℚ V] (τ : TriLinearSymm V) (S T : V)`.

| Before | After |
|---|---|
| `⊢ P (τ.toCubic (S + T))` | `⊢ P (τ.toCubic S + τ.toCubic T + 3 * ((τ S) S) T + 3 * ((τ T) T) S)` |

**R20 · `rw [HomogeneousCubic.map_smul]`** changes the **goal**: `f (a • S) = a ^ 3 * f S`.
Placeholders: `(f : HomogeneousCubic V) (a : ℚ) (S : V)`.

| Before | After |
|---|---|
| `⊢ P (f (a • S))` | `⊢ P (a ^ 3 * f S)` |

**R21 · `simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]`** changes the
**goal**: each lemma pulls a scalar out of one slot (`τ (a • S) T R = a * τ S T R`, and likewise for slots 2
and 3); `simp only` repeats them until no `•` is left inside `τ`. Placeholders:
`(τ : TriLinearSymm V) (a b c : ℚ) (S T R : V)`.

| Before | After |
|---|---|
| `⊢ P (((τ (a • S)) (b • T)) (c • R))` | `⊢ P (c * (b * (a * ((τ S) T) R)))` |

**R22 · `rw [TriLinearSymm.swap₃ τ S S]`** changes the **goal**: `swap₃ τ S T R : τ S T R = τ R T S`. Fixing the
first two arguments makes it move only terms `τ S S _`. R19 produces `τ S S Y`; the hypothesis is `τ Y S S`.
Placeholders: `(τ : TriLinearSymm V) (S T : V)`.

| Before | After |
|---|---|
| `⊢ P (((τ S) S) T)` | `⊢ P (((τ T) S) S)` |

**W3: scalars out, then swap so a hypothesis fits** (`h : cubeTriLin T S S = 0`): R21,
`rw [TriLinearSymm.swap₃ cubeTriLin S S, h]`, then `simp only [mul_zero]` (R30).

```lean-goal
⊢ ((cubeTriLin (a • S)) (a • S)) (b • T) = 0
⊢ b * (a * (a * ((cubeTriLin S) S) T)) = 0
⊢ b * (a * (a * 0)) = 0
```

---

## Part 6 · `add_hypercharge_isSolution`

Statement: for `S : (PlusU1 n).Sols` and `a b : ℚ`, `(PlusU1 n).IsSolution (a • S.val + b • (PlusU1.Y n).val)`.
Build the solution from the `LinSols` combination (linear ACCs come free), and discharge the quadratic and
cubic ACCs with milestones 4 and 5, whose hypotheses come from milestones 1–3.

**R23 · `S.1`, `S.1.1`** changes the **context** (here: `have hL : S.1.1.val = S.val := rfl`; the goal is
unchanged). For `S : Sols`, `S.1 : QuadSols` drops the cubic proof and `S.1.1 : LinSols` drops the quadratic
one. All have the same `.val`, by definition, so `rfl` proves the equation and Lean prints both sides as
`S.val`. Use `S.1.1` where a lemma wants a `LinSols` (R24) and `S.1` where it wants a `QuadSols` (R28).
Placeholders: `{n : ℕ} (S : (PlusU1 n).Sols)`.

| Before | After |
|---|---|
| `⊢ P S.val` | `hL : S.val = S.val ⊢ P S.val` |

(The goal was `P S.1.1.val`; Lean prints it as `P S.val`.)

**R24 · `have hYY : accYY S.val = 0 := PlusU1.YYsol S`** changes the **context**. `PlusU1.YYsol` reads the 4th
linear ACC off `S : (PlusU1 n).LinSols`; for a full solution pass `S.1.1`. Placeholders: `(S : (PlusU1 n).LinSols)`.

| Before | After |
|---|---|
| `⊢ G` | `hYY : accYY S.val = 0 ⊢ G` |

**R25 · `refine ⟨sol, ?_⟩`** changes the **goal**: `IsSolution` is an `∃`, so give the witness and prove its
`.val` is the target. Placeholders: `(S : (PlusU1 n).Sols) (T : (PlusU1 n).Charges)`.

| Before | After |
|---|---|
| `⊢ (PlusU1 n).IsSolution T` | `⊢ S.val = T` |

**R26 · `refine ⟨PlusU1.linearToAF T ?_ ?_, rfl⟩`** changes the **goal list**.
`PlusU1.linearToAF : (T : LinSols) → accQuad T.val = 0 → accCube T.val = 0 → Sols` keeps `T.val`, so `rfl`
proves the `.val` equation and the two `?_` become goals. Placeholders: `(T : (PlusU1 n).LinSols)`.

| Before | After |
|---|---|
| `⊢ (PlusU1 n).IsSolution T.val` | `⊢ accQuad T.val = 0`, `⊢ accCube T.val = 0` |

**R27 · `.val` of a `LinSols` combination** changes the **goal** (`change`): `LinSols` is a ℚ-module and
`(a • S + b • T).val` is `a • S.val + b • T.val` by definition. So `rfl` in R26 accepts the witness
`a • S.1.1 + b • (PlusU1.Y n).1.1` for the target `a • S.val + b • (PlusU1.Y n).val`, and `exact` accepts a
milestone about `a • S.val + b • Y.val` for a goal about `(…).val`. Placeholders:
`(S T : (PlusU1 n).LinSols) (a b : ℚ)`.

| Before | After |
|---|---|
| `⊢ P (a • S + b • T).val` | `⊢ P (a • S.val + b • T.val)` |

**R28 · `PlusU1.quadSol`** changes the **context**: `PlusU1.quadSol S : accQuad S.val = 0` for
`S : (PlusU1 n).QuadSols` (use `S.1` for a `Sols`, `(PlusU1.Y n).1` for hypercharge).

| Before | After |
|---|---|
| `⊢ G` | `hQ : accQuad S.val = 0 ⊢ G` |

**R29 · `PlusU1.cubeSol`** changes the **context**: `PlusU1.cubeSol S : accCube S.val = 0` for `S : (PlusU1 n).Sols`.

| Before | After |
|---|---|
| `⊢ G` | `hC : accCube S.val = 0 ⊢ G` |

**R30 · `rw [mul_zero]`** changes the **goal**: `mul_zero a : a * 0 = 0`. Use it after rewriting an ACC to `0`
inside `6 * accYY S`. Placeholders: `(a : ℚ)`.

| Before | After |
|---|---|
| `⊢ P (a * 0)` | `⊢ P 0` |

**W4: a rescaled solution `c • S.val` is a solution.** Helpers `hq`, `hc` stated over
`(SMνCharges n).Charges` (proved with R15/R20, R30), then R26 with the witness `c • S.1.1` (R27 makes `rfl`
work), then `exact hq S.val (PlusU1.quadSol S.1)` and `exact hc S.val (PlusU1.cubeSol S)`. After the `refine`:

```lean-goal
⊢ accQuad (c • S.toLinSols).val = 0
⊢ accCube (c • S.toLinSols).val = 0
```

---

## Traps

- `(PlusU1 n).Charges` is `(SMνCharges n).Charges` under another name, and `rw` does not see through it: on
  `accQuad (c • S.val)` with `S.val : (PlusU1 n).Charges`, `rw [HomogeneousQuadratic.map_smul]` fails with
  "Did not find an occurrence of the pattern" (the `•` there is the one of `(PlusU1 n).Charges`). State helpers and milestones over
  `(SMνCharges n).Charges` and apply them with `exact` (W4); `exact` compares up to unfolding.
- After R26 the goals show `(a • S.toLinSols + b • (PlusU1.Y n).toLinSols).val`, not `a • S.val + …`. Do not
  `rw` there; `exact` a milestone (R27).
- `rw [l]` rewrites one instantiation of `l`. Five species need `repeat rw [l]` (R5).
- In Part 2, apply `sum_familyUniversal_three` before `sum_familyUniversal_two`: R10 is what produces the
  two-factor sums R4 needs.
- `rw [hQ]` needs `accQuad S` literally. After R14 the goal says `quadBiLin.toHomogeneousQuad (a • S)`; `change`
  back first (R13).
- Cross terms come out with the arguments in the wrong order for the hypotheses (`B S Y`, `τ S S Y`): R18, R22.
- `simp [PlusU1.Y₁]` rewrites more than the entries of `Y₁` (R7); do not try to predict its output, end with `ring`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a form as species sums | `rw [quadBiLin_decomp]`, `rw [cubeTriLin_decomp]`, `rw [accYY_decomp]`, `rw [accQuad_decomp]` | R1, R9, R2, R11 |
| hypercharge as a universal charge | `rw [PlusU1.Y_val]` | R3 |
| constant factor out of every species sum | `repeat rw [sum_familyUniversal_three]`, `repeat rw [sum_familyUniversal_two]` | R10, R4, R5 |
| one-family entries, then the numbers of `Y₁` | `simp only [toSpecies_one]`, `simp [PlusU1.Y₁, sq]` | R6, R7, R12 |
| finish (sums are atoms) | `ring` | R8 |
| `accQuad`/`accCube` ↔ `toHomogeneousQuad`/`toCubic` | `change …` | R13 |
| expand `q (S + T)`, `c (S + T)` | `rw [BiLinearSymm.toHomogeneousQuad_add]`, `rw [TriLinearSymm.toCubic_add]` | R14, R19 |
| scalars out of `q`, `c` | `rw [HomogeneousQuadratic.map_smul]`, `rw [HomogeneousCubic.map_smul]` | R15, R20 |
| scalars out of `B`, `τ` | `rw [BiLinearSymm.map_smul₁, BiLinearSymm.map_smul₂]`, `simp only [TriLinearSymm.map_smul₁, TriLinearSymm.map_smul₂, TriLinearSymm.map_smul₃]` | R16, R17, R21 |
| reorder arguments | `rw [BiLinearSymm.swap]`, `rw [TriLinearSymm.swap₃ τ S S]` | R18, R22 |
| ACCs of a solution | `PlusU1.YYsol S.1.1`, `PlusU1.quadSol S.1`, `PlusU1.cubeSol S` | R23, R24, R28, R29 |
| prove `IsSolution` | `refine ⟨PlusU1.linearToAF (…) ?_ ?_, rfl⟩` | R25, R26, R27 |
| `a * 0 → 0` | `rw [mul_zero]` | R30 |
| see the state | infoview | |
