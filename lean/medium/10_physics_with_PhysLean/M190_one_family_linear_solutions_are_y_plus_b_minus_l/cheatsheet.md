# M190 · One family: linear solutions are Y plus B−L: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `refine ⟨?_, ?_, ?_⟩`, `rw [h]`, `ring`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's anomaly-cancellation framework
for the Standard Model plus right-handed neutrinos (`SMνCharges`, `PlusU1`, `LinSols`, the ACCs and
their `_decomp` lemmas), Mathlib's finite sums `∑ i, f i`, rationals `ℚ`, the scalar action `•` on
vectors, and the tactics `linarith`, `funext`, `match`, `change`.

**Physics in one paragraph.** One family of SM fermions plus a right-handed neutrino has six species
`Q, U, D, L, E, N` (quark doublet, up and down singlets, lepton doublet, electron singlet, neutrino
singlet). A new `U(1)` gauge symmetry assigns each species a rational charge, so a charge assignment is
a vector `S ∈ ℚ⁶` (index `0..5` in that order). It is consistent only if the anomaly cancellation
conditions (ACCs) hold: four linear ones (`accGrav`: mixed gravitational; `accSU2`, `accSU3`: mixed with
`SU(2)`, `SU(3)`; `accYY`: mixed with hypercharge squared), one quadratic (`accQuad`) and one cubic
(`accCube`). The exercise: the linear ones force `S = a·Y + b·(B−L)`, and then the other two hold too.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- A cell with no `⊢` shows only a hypothesis (the goal is unchanged): used when `rw … at h` rewrites
  a long hypothesis.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{n : ℕ}` is any number of families; the exercise has `n = 1`.
  A bracket such as `[AddCommMonoid M]` is a requirement on `M` (a *type class*: `M` has `+` and `0`, with
  `+` commutative); `ℚ` qualifies.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℚ` | the rational numbers; all charges are rationals |
| `PlusU1 n` | physlib's ACC system for `n` SM families plus right-handed neutrinos: its charge vectors and its linear, quadratic and cubic ACCs |
| `(PlusU1 1).LinSols` | charge vectors for 1 family that satisfy the 4 linear ACCs: a vector `S.val` plus proofs |
| `S.val` | the charge vector itself, of type `(PlusU1 1).Charges` |
| `(SMνCharges n).Charges` | all charge vectors for `n` families: functions `Fin (SMνCharges n).numberCharges → ℚ`, i.e. `6n` rationals |
| `Fin (PlusU1 1).numberCharges` | the index type of `S.val`; it is `Fin 6`, but Lean does not see numerals in it (Traps) |
| `S.val 0`, `S 2` | entry 0 (charge of `Q`), entry 2 (charge of `D`). Printed this way; to **type** it write `S.val (0 : Fin 6)` |
| `Fin (SMνSpecies 1).numberCharges` | the family index: `(SMνSpecies n).numberCharges` is `n` (one charge per family for a single species), so here it is `Fin 1` |
| `Q S i`, `U S i`, …, `N S i` | charge of species `Q` (`U`, …) in family `i`. `Q` is `toSpecies 0`, …, `N` is `toSpecies 5` |
| `(toSpecies j) S` | species `j` of `S`, as a function of the family index |
| `∑ i, f i` | the sum of `f i` over all `i` of a finite type (here: over the families) |
| `⟨0, ⋯⟩`, `⟨0, sum_one._proof_1⟩` | the element `0` of `Fin 1` (value `0`, plus a proof that `0 < 1`): family 0 |
| `accGrav S`, `accQuad S`, `accCube S` | the ACC evaluated at `S` (a linear map, a quadratic form, a cubic form applied to `S`) |
| `PlusU1.Y₁.val`, `PlusU1.BL₁.val` | hypercharge `Y = (1, −4, 2, −3, 6, 0)` and `B−L = (1, −1, −1, −3, 3, 3)`, defined by a `match` on the index |
| `a • v` | scalar `a` times every entry of the vector `v`; `(a • v) k = a * v k` by definition |
| `⟨1, isLt✝⟩` | the index `1` inside a `match` branch; `isLt✝ : 1 < …` is its bound proof (the `✝` means you cannot name it) |
| `case refine_1` | the first goal made by `refine ⟨?_, ?_, ?_⟩` |

---

## Part 1 · `linSol_classification`

Statement: for every `S : (PlusU1 1).LinSols`, `accQuad S.val = 0`, `accCube S.val = 0`, and
`S.val = (Q − N/3) • Y + (N/3) • (B−L)`, where `Q = S.val (0 : Fin 6)` and `N = S.val (5 : Fin 6)`.

The plan: get the four linear ACCs as hypotheses (R1), expand them into the six entries (R2–R8), solve
for `U, D, L, E` in terms of `Q, N` with `linarith` (R9), then prove the three conjuncts: substitute
and `ring` for the quadratic and cubic ACCs (R10, R11), entry by entry for the vector equation (R12–R14).

### From a linear solution to four equations

**R1 · `have h := PlusU1.gravSol S`** changes the **context**. `have h := e` adds `h` with whatever type
`e` has. The four lemmas, for `{n : ℕ} (S : (PlusU1 n).LinSols)`:
`PlusU1.gravSol S : accGrav S.val = 0`, `PlusU1.SU2Sol S : accSU2 S.val = 0`,
`PlusU1.SU3Sol S : accSU3 S.val = 0`, `PlusU1.YYsol S : accYY S.val = 0`.

| Before | After the four `have`s |
|---|---|
| `⊢ G` | `hG : accGrav S.val = 0, h2 : accSU2 S.val = 0, h3 : accSU3 S.val = 0, hY : accYY S.val = 0 ⊢ G` |

**R2 · `rw [accGrav_decomp] at h`** changes the **context**: `h` is rewritten, the goal stays. The lemma,
for `{n : ℕ} (S : (SMνCharges n).Charges)`:
`accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i + ∑ i, N S i`.
It applies to `S.val` because `(PlusU1 n).Charges` is `(SMνCharges n).Charges`.

| Before | After |
|---|---|
| `h : accGrav S.val = 0` | `h : 6 * ∑ i, Q S.val i + 3 * ∑ i, U S.val i + 3 * ∑ i, D S.val i + 2 * ∑ i, L S.val i + ∑ i, E S.val i + ∑ i, N S.val i = 0` |

**R3 · `rw [accSU2_decomp] at h`** changes the **context**. The lemma: `accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i`.

| Before | After |
|---|---|
| `h : accSU2 S.val = 0` | `h : 3 * ∑ i, Q S.val i + ∑ i, L S.val i = 0` |

**R4 · `rw [accSU3_decomp] at h`** changes the **context**. The lemma:
`accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i`.

| Before | After |
|---|---|
| `h : accSU3 S.val = 0` | `h : 2 * ∑ i, Q S.val i + ∑ i, U S.val i + ∑ i, D S.val i = 0` |

**R5 · `rw [accYY_decomp] at h`** changes the **context**. The lemma:
`accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i` (no `N`: the
neutrino has hypercharge 0).

| Before | After |
|---|---|
| `h : accYY S.val = 0` | `h : ∑ i, Q S.val i + 8 * ∑ i, U S.val i + 2 * ∑ i, D S.val i + 3 * ∑ i, L S.val i + 6 * ∑ i, E S.val i = 0` |

### One family: the sums and species disappear

**R6 · `sum_one`** changes the **goal**: with one family, a sum over families is its single term. The
lemma (`SMνCharges.sum_one`): `∑ i, f i = f ⟨0, _⟩` for
`{M : Type} [AddCommMonoid M] (f : Fin (SMνSpecies 1).numberCharges → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f ⟨0, sum_one._proof_1⟩)` |

**R7 · `toSpecies_one`** changes the **goal**: species `j` in family 0 is entry `j` of the 6-vector. The
lemma (`SMνCharges.toSpecies_one`): `toSpecies j S ⟨0, _⟩ = S j` for
`(S : (SMνCharges 1).Charges) (j : Fin 6)`. Since `D` is `toSpecies 2`, it also turns `D S ⟨0, ⋯⟩` into
`S 2` (`rw` and `simp only` both see through the name `D`).

| Before | After |
|---|---|
| `⊢ P ((toSpecies j) S ⟨0, ⋯⟩)` | `⊢ P (S j)` |
| `⊢ P (D S ⟨0, ⋯⟩)` | `⊢ P (S 2)` |

**R8 · `simp only [sum_one, toSpecies_one] at h₁ h₂`** changes the **context**: R6 then R7, in every
listed hypothesis at once. `sum_one` must run first: `toSpecies_one` only matches family `⟨0, _⟩`.
Without `at …` it rewrites the goal (Part 1's quadratic and cubic conjuncts).

| Before | After |
|---|---|
| `h₁ : 3 * ∑ i, Q S i + ∑ i, L S i = 0` and `h₂ : ∑ i, N S i = 0` | `h₁ : 3 * S 0 + S 3 = 0, h₂ : S 5 = 0 ⊢ 3 * S 0 + S 3 = 0 ∧ S 5 = 0` |

### Solving the linear system

**R9 · `linarith`** **closes** a goal `a = b`, `a ≤ b` or `a < b` that follows from the hypotheses by
adding them up with rational coefficients. It treats every non-arithmetic term, such as `S.val 3`, as an
unknown, and two terms count as the same unknown only if they are written the same way. Use it inside a
`have`: `have hL : S.val (3 : Fin 6) = … := by linarith`.

| Before | After |
|---|---|
| `h₁ : x + y + z = 0, h₂ : 2 * x + y = 0, h₃ : x - z = 3 ⊢ y = -2` | closed |

The four linear ACCs leave `Q = S 0` and `N = S 5` free and give
`U = N − 4Q`, `D = 2Q − N`, `L = −3Q`, `E = 6Q − N`.

### The quadratic and cubic ACCs

**R10 · `rw [accQuad_decomp]`** changes the **goal**. The lemma, for `(S : (SMνCharges n).Charges)`:
`accQuad S = ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2`.

| Before | After |
|---|---|
| `⊢ accQuad S = 0` | `⊢ ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2 = 0` |

**R11 · `rw [accCube_decomp]`** changes the **goal**. The lemma:
`accCube S = 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3 + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3`.

| Before | After |
|---|---|
| `⊢ accCube S = 0` | `⊢ 6 * ∑ i, Q S i ^ 3 + 3 * ∑ i, U S i ^ 3 + 3 * ∑ i, D S i ^ 3 + 2 * ∑ i, L S i ^ 3 + ∑ i, E S i ^ 3 + ∑ i, N S i ^ 3 = 0` |

After R10 or R11: `simp only [sum_one, toSpecies_one]` (R8 on the goal), `rw` your four facts
(`rw [h]`, TACTIC_STATES), then `ring` (TACTIC_STATES) closes the polynomial identity in `Q, N`.

### The vector equation, entry by entry

**R12 · `funext j`** changes the **goal and the context**: a charge vector is a function, so two are
equal when every entry is. Placeholders: `(S T : (SMνCharges 1).Charges)`.

| Before | After |
|---|---|
| `⊢ S = T` | `j : Fin (SMνCharges 1).numberCharges ⊢ S j = T j` |

**R13 · `match j with | ⟨0, _⟩ => tac₀ | … `** changes the **goal list**: one goal per value of `j`. A
`Fin m` element is a pair `⟨k, proof of k < m⟩`, and the patterns `⟨0, _⟩ … ⟨m-1, _⟩` cover all of
them. Each branch runs its own tactics. Placeholders: `(P : Fin 3 → Prop) (j : Fin 3)`; the exercise
has six branches `⟨0, _⟩ … ⟨5, _⟩`. Indent every `| … =>` line the same; the branch's tactics go
after `=>` or on the next lines, indented further.

| Before | After (one goal per branch) |
|---|---|
| `j : Fin 3 ⊢ P j` | `isLt✝ : 0 < 3 ⊢ P ⟨0, isLt✝⟩`, `isLt✝ : 1 < 3 ⊢ P ⟨1, isLt✝⟩`, `isLt✝ : 2 < 3 ⊢ P ⟨2, isLt✝⟩` |

**R14 · `change G'`** changes the **goal** to `G'`, provided `G'` and the goal are equal by unfolding
definitions (Lean checks this). Here it does three jobs at once: `(a • v + b • w) k` unfolds to
`a * v k + b * w k`; an entry of a `match`-defined vector such as `PlusU1.Y₁.val` unfolds to its
number; and `⟨1, isLt✝⟩` is replaced by `(1 : Fin 6)`, so the atoms match your `have` facts for
`linarith`. Placeholders: `(a b : ℚ) (w : Fin 3 → ℚ) (hk : 1 < 3)`, and `V = (2, −5, 7)` defined by a
`match` like `Y₁`.

| Before | After `change P (a * -5 + b * w 1)` |
|---|---|
| `⊢ P ((a • V + b • w) ⟨1, hk⟩)` | `⊢ P (a * -5 + b * w 1)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: one linear ACC on a bare charge vector** (`S : (SMνCharges 1).Charges`, `h : accSU3 S = 0`).
R4 turns `h` into `2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i = 0`, R8 into `2 * S 0 + S 1 + S 2 = 0`,
and R9 closes the goal, which stays

```lean-goal
⊢ S 2 = -2 * S 0 - S 1
```

**W2: the quadratic ACC after a substitution** (`hU : S 1 = 2 * S 0`). R10, R8 on the goal, `rw [hU]`,
then `ring`:

```lean-goal
⊢ accQuad S = -7 * S 0 ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2
⊢ ∑ i, Q S i ^ 2 - 2 * ∑ i, U S i ^ 2 + ∑ i, D S i ^ 2 - ∑ i, L S i ^ 2 + ∑ i, E S i ^ 2 = -7 * S 0 ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2
⊢ S 0 ^ 2 - 2 * S 1 ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2 = -7 * S 0 ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2
⊢ S 0 ^ 2 - 2 * (2 * S 0) ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2 = -7 * S 0 ^ 2 + S 2 ^ 2 - S 3 ^ 2 + S 4 ^ 2
```

**W3: a 3-vector as a combination** `x = x 0 • Ones + (x 1 - x 0) • W` with `W = (0, 1, 1)`, given
`h : x 2 = x 1`. R12 gives one entry goal; R13 splits it; in each branch R14 spells out the entry, e.g.
`change x 2 = x 0 * 1 + (x 1 - x 0) * 1`, and `ring` or R9 finishes.

```lean-goal
⊢ x = x 0 • Ones + (x 1 - x 0) • W
⊢ x j = (x 0 • Ones + (x 1 - x 0) • W) j
```

---

## Traps

- The index type of `S.val` is `Fin (PlusU1 1).numberCharges`, which has no numerals: `S.val 0` is an
  error ("failed to synthesize instance of type class `OfNat (Fin (PlusU1 1).numberCharges) 0`"). Write `S.val (0 : Fin 6)`.
  The infoview still prints it as `S.val 0`.
- `linarith` matches unknowns by how they are written. Inside a `match` branch the entry is
  `S.val ⟨1, isLt✝⟩`, not `S.val (1 : Fin 6)`, so first `change` it (R14). `linarith` also cannot unfold
  `(a • v + b • w) k` or the `match` inside `Y₁`, `B−L`: that is the other job of `change`.
- In a `change` for a branch, the coefficients come from the entries of `Y` and `B−L` at that index
  (listed in the problem's GOAL). Get one wrong and `change` fails: the goals are no longer equal.
- `simp only [toSpecies_one] at h` before `sum_one` fails with `simp made no progress`: it needs the
  family index `⟨0, _⟩`, and a sum `∑ i, Q S i` has only the bound variable `i`.
- Plain `simp at h` instead of R8 leaves sums of `toSpeciesEquiv S.val 0 x` (physlib's internal form of
  `Q S.val x`) that no later entry matches. Use `simp only [sum_one, toSpecies_one]`.
- Prove the four linear facts **before** `refine ⟨?_, ?_, ?_⟩`, so all three goals have them.
- `t1 ; t2` runs `t2` on the first goal only. After `refine`, use `·` to focus each goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| the 4 linear ACCs as hypotheses | `have hG := PlusU1.gravSol S` (and `SU2Sol`, `SU3Sol`, `YYsol`) | R1 |
| ACC → sums over families | `rw [accGrav_decomp] at hG` (`accSU2_`, `accSU3_`, `accYY_decomp`) | R2–R5 |
| sums over 1 family → entries `S k` | `simp only [sum_one, toSpecies_one] at hG h2 h3 hY` | R6–R8 |
| solve for one entry | `have hU : S.val (1 : Fin 6) = … := by linarith` | R9 |
| split `A ∧ B ∧ C` | `refine ⟨?_, ?_, ?_⟩` | TACTIC_STATES |
| quadratic / cubic ACC → sums | `rw [accQuad_decomp]` / `rw [accCube_decomp]` | R10, R11 |
| substitute, finish | `rw [hU, hD, hL, hE]; ring` | TACTIC_STATES |
| vector equation → entries | `funext j` | R12 |
| one goal per index | `match j with \| ⟨0, _⟩ => … \| ⟨5, _⟩ => …` | R13 |
| spell out an entry | `change S.val (1 : Fin 6) = c * (-4) + d * (-1)` | R14 |
| type an index | `S.val (0 : Fin 6)` | Traps |
| see the state | infoview | |
