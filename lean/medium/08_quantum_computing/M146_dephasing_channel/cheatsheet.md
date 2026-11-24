# M146 · The dephasing channel: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices (`diagonal`, `ᴴ`,
`Pi.single`), and physlib's mixed states `MState` and channels `CPTPMap` built from Kraus operators.

Physics in one paragraph. A qubit state is a density matrix `ρ` (2×2, positive semidefinite, trace 1).
A channel is a map `Λ` on density matrices that is completely positive and trace preserving (CPTP). A
family of matrices `M k` (the *Kraus operators*) gives the channel `Λ(ρ) = ∑ k, M k * ρ * (M k)ᴴ`; it is
trace preserving exactly when `∑ k, (M k)ᴴ * M k = 1`. `|k⟩` is the `k`-th basis column vector and
`|k⟩⟨k|` the projector onto it (the matrix with a single `1` at `(k, k)`). Dephasing uses the two projectors
`P 0 = |0⟩⟨0| = diag(1, 0)` and `P 1 = |1⟩⟨1| = diag(0, 1)`; in Lean, `P k = diagonal (Pi.single k 1)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `P : α → α → Prop` takes two such parts. In the guide `P` is only this placeholder,
  not the exercise's Kraus operators `P k`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddMonoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it. `[Fintype d]` says `d`
  is finite (needed to sum over it); `[DecidableEq d]` says equality on `d` can be decided (needed for
  `if i = j`); `Fin n` meets both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 complex matrices; rows and columns indexed by `Fin 2 = {0, 1}` |
| `M i j` | entry in row `i`, column `j` |
| `diagonal v` | the matrix with `v i` at `(i, i)` and `0` elsewhere (`v : d → α`) |
| `Pi.single i x` | the vector (function `d → β`) with `x` at index `i` and `0` elsewhere |
| `Aᴴ` | conjugate transpose: `Aᴴ i j = star (A j i)` |
| `star z`, `star v` | complex conjugate of `z`; on a vector, conjugate of every entry |
| `1 i j` | entry of the identity matrix |
| `∑ k, f k` | the sum over all `k` of a finite type (here `Fin 2`); `f k` may be a matrix |
| `MState d` | physlib's mixed state on the index type `d`: a density matrix bundled with its proofs |
| `ρ.m` | the density matrix of `ρ`, a `Matrix d d ℂ` (`MState.m`) |
| `CPTPMap dIn dOut ℂ` | physlib's quantum channel from `dIn`-states to `dOut`-states |
| `Λ ρ` | the channel `Λ` applied to the state `ρ` (a `CPTPMap` coerces to a function), an `MState dOut` |
| `CPTPMap.of_kraus_CPTPMap M h` | the channel with Kraus operators `M`, given `h : ∑ k, (M k)ᴴ * M k = 1` |
| `(((Λ.toPTPMap ℂ).toPMap ℂ).toHPMap ℂ).map` | how the infoview prints `Λ.map`, the linear map on matrices underlying `Λ` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case «0».«1»` | the goal for entry (0, 1), after `fin_cases i <;> fin_cases j` |
| `case pos`, `case neg` | the two goals after `by_cases h : i = j` (R16) |
| `h : ¬i = j` | `h` says `i ≠ j` (`¬` is "not") |

---

## Part 1 · `dephase_tp`

Statement: `∑ k, (P k)ᴴ * P k = 1`, the trace-preservation condition. It is an equation between 2×2
matrices: `|0⟩⟨0| + |1⟩⟨1| = 1`.

**R1 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when
every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R2 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context and there is one
goal per value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`. Use `fin_cases i <;> fin_cases j` for all four
entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

`simp [P, Fin.sum_univ_two, Pi.single_apply]` then evaluates each entry. It unfolds `P k` to
`diagonal (Pi.single k 1)` and applies R3–R10 in about this order. You do not write them, but they are
the moves to know when `simp` stops.

**R3 · `Matrix.diagonal_conjTranspose`** changes the **goal**. The lemma is `(diagonal v)ᴴ = diagonal (star v)`.
Placeholders: `{α : Type} [AddMonoid α] [StarAddMonoid α] {d : Type} [DecidableEq d] (v : d → α)`
(α has `+`, `0` and a conjugation `star` compatible with `+`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (diagonal v)ᴴ` | `⊢ P (diagonal (star v))` |

**R4 · `Pi.star_single`, then `star_one`** change the **goal**. The lemmas are
`star (Pi.single i x) = Pi.single i (star x)` and `star 1 = 1`. Placeholders: `{d : Type} [DecidableEq d] (i : d)`,
entries in `ℂ`. Together with R3: `(P k)ᴴ = P k`.

| Before | After `rw [Pi.star_single]` | After `rw [star_one]` |
|---|---|---|
| `⊢ P (star (Pi.single i 1))` | `⊢ P (Pi.single i (star 1))` | `⊢ P (Pi.single i 1)` |

**R5 · `Matrix.diagonal_mul_diagonal`** changes the **goal**: a product of diagonal matrices is the diagonal of
the entrywise products, `diagonal v * diagonal w = diagonal (fun i => v i * w i)`. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] (v w : d → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (diagonal v * diagonal w)` | `⊢ P (diagonal fun i => v i * w i)` |

**R6 · `Pi.single_apply`** changes the **goal**. The lemma is `Pi.single i x k = if k = i then x else 0`.
Placeholders: `{d : Type} [DecidableEq d] {β : Type} [Zero β] (i k : d) (x : β)`. With concrete indices
`simp` decides `k = i` and drops the `if` (`↓reduceIte`); with `x * (if …)` it first pushes the product
inside (`mul_ite`).

| Before | After |
|---|---|
| `⊢ P (Pi.single i x k)` | `⊢ P (if k = i then x else 0)` |

**R7 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. It works for sums of
matrices too. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → Matrix (Fin 2) (Fin 2) β)`.

| Before | After |
|---|---|
| `⊢ P (∑ k, f k)` | `⊢ P (f 0 + f 1)` |

**R8 · `Matrix.add_apply`** changes the **goal**: `(A + B) i j = A i j + B i j`. Placeholders:
`{d α : Type} [Add α] (A B : Matrix d d α) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P ((A + B) i j)` | `⊢ P (A i j + B i j)` |

**R9 · `Matrix.diagonal_apply_eq`, `Matrix.diagonal_apply_ne`** change the **goal**:
`diagonal v i i = v i`, and `i ≠ j → diagonal v i j = 0`. Placeholders:
`{d : Type} [DecidableEq d] {α : Type} [Zero α] (v : d → α) (i j : d) (hij : i ≠ j)`.

| Before | After `rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ hij]` |
|---|---|
| `⊢ P (diagonal v i i) (diagonal v i j)` | `⊢ P (v i) 0` |

**R10 · `Matrix.one_apply_eq`, `Matrix.one_apply_ne`** change the **goal**: the identity has `1` on the
diagonal and `0` elsewhere (`i ≠ j`). Placeholders: `{d : Type} [DecidableEq d] (i j : d) (hij : i ≠ j)`.

| Before | After |
|---|---|
| `⊢ P (1 i i) (1 i j)` | `⊢ P 1 0` |

---

## Part 2 · the bridge lemma (your helper) and `dephase_apply`

`dephase_apply`: `(dephase ρ).m = diagonal (fun i => ρ.m i i)`. The output keeps the populations
`ρ 0 0`, `ρ 1 1` and erases the coherences `ρ 0 1`, `ρ 1 0`.

`dephase ρ` is a bundled `MState`; nothing about matrices applies to it until you turn `(dephase ρ).m` into
the Kraus sum. Prove that first, as your own lemma between the spec blocks (the problem leaves room):
`(dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ`. Then `rw` with it in `dephase_apply`.

**R11 · `rw [CPTPMap.mat_coe_eq_apply_mat]`** changes the **goal**. The lemma is `(Λ ρ).m = Λ.map ρ.m`: the
matrix of the output state is the channel's linear map applied to the input matrix. Placeholders:
`{dIn dOut : Type} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] (Λ : CPTPMap dIn dOut ℂ) (ρ : MState dIn)`.

| Before | After |
|---|---|
| `⊢ P (Λ ρ).m` | `⊢ P ((((Λ.toPTPMap ℂ).toPMap ℂ).toHPMap ℂ).map ρ.m)` |

**R12 · `rfl`** **closes** the goal "the map of `of_kraus_CPTPMap M hM` is the Kraus sum". `of_kraus_CPTPMap`
stores `MatrixMap.of_kraus M M`, which is defined as `X ↦ ∑ k, M k * X * (M k)ᴴ`, so both sides are equal
by unfolding. Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (M : Fin 3 → Matrix d d ℂ) (hM : ∑ k, (M k)ᴴ * M k = 1) (X : Matrix d d ℂ)`.
The index must be a concrete `Fin n`; with an abstract `κ` the sum does not unfold and `rfl` fails.

```lean-goal
⊢ ((((CPTPMap.of_kraus_CPTPMap M hM).toPTPMap ℂ).toPMap ℂ).toHPMap ℂ).map X = ∑ k, M k * X * (M k)ᴴ
```

After the bridge, `dephase_apply` is R1, R2 and `simp [P, Fin.sum_univ_two, Matrix.mul_apply]`, which uses
R3, R4, R7, R8, R13, R9, R14.

**R13 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(AB)_{ik} = \sum_j A_{ij} B_{jk}$. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] {α : Type} [Mul α] [AddCommMonoid α] (A B : Matrix d d α) (i k : d)`
(α has `*` and a commutative `+` with `0`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P ((A * B) i k)` | `⊢ P (∑ j, A i j * B j k)` |

**R14 · `Pi.single_eq_same`, `Pi.single_eq_of_ne`** change the **goal**: `Pi.single i x i = x`, and
`j ≠ i → Pi.single i x j = 0`. Placeholders: `{d : Type} [DecidableEq d] {β : Type} [Zero β] (i j : d) (hji : j ≠ i) (x : β)`.
`simp` uses these instead of R6 when the indices are visibly equal or different.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x i) (Pi.single i x j)` | `⊢ P x 0` |

### Worked combination W1 (the identity channel on a qutrit, not the exercise's channel)

`K _ = 1 : Matrix (Fin 3) (Fin 3) ℂ`, one Kraus operator; `idCh = CPTPMap.of_kraus_CPTPMap K K_tp`. The
bridge `idCh_kraus` is R11 then R12:

```lean-goal
⊢ (idCh ρ).m = ∑ k, K k * ρ.m * (K k)ᴴ
⊢ (((idCh.toPTPMap ℂ).toPMap ℂ).toHPMap ℂ).map ρ.m = ∑ k, K k * ρ.m * (K k)ᴴ
```

Then `idCh_m : (idCh ρ).m = ρ.m` is `rw [idCh_kraus]` and `simp [K]`:

```lean-goal
⊢ (idCh ρ).m = ρ.m
⊢ ∑ k, K k * ρ.m * (K k)ᴴ = ρ.m
```

---

## Part 3 · `dephase_idem`

Statement: `dephase (dephase ρ) = dephase ρ`, an equation between **states**. Reduce it to matrices (R15),
rewrite both sides with `dephase_apply`, then compare entries.

**R15 · `apply MState.ext_m`** changes the **goal**. The lemma is `ρ₁.m = ρ₂.m → ρ₁ = ρ₂`: states with the same
matrix are equal. Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d)`.

| Before | After |
|---|---|
| `⊢ ρ = σ` | `⊢ ρ.m = σ.m` |

**R16 · `by_cases h : i = j`** changes the **goal list and the context**: two goals, one with `h : i = j`
(`case pos`), one with `h : ¬i = j` (`case neg`). Placeholders: `{d : Type} (i j : d) (G : Prop)`. Follow
with `simp [h]`: in `pos` it replaces `i` by `j` and uses R9 `diagonal_apply_eq`; in `neg` it uses R9
`diagonal_apply_ne`.

| Before | After |
|---|---|
| `⊢ G` | `h : i = j ⊢ G`, `h : ¬i = j ⊢ G` |

### Worked combinations W2–W3 (not the exercise's objects)

**W2: a lemma about `(idCh ?ρ).m` used twice.** `rw [idCh_m]` rewrites the **outermost** `(idCh _).m` first
(`?ρ := idCh ρ`); the second `rw [idCh_m]` then rewrites the inner one and `rw` closes `ρ.m = ρ.m` by `rfl`:

```lean-goal
⊢ (idCh (idCh ρ)).m = ρ.m
⊢ (idCh ρ).m = ρ.m
```

**W3: an entry identity of diagonal matrices** (`v w : Fin 3 → ℂ`): `ext i j`, `by_cases h : i = j`,
`all_goals simp [h]`:

```lean-goal
⊢ diagonal v * diagonal w = diagonal fun k => v k * w k
⊢ (diagonal v * diagonal w) i j = diagonal (fun k => v k * w k) i j
```

---

## Traps

- `dephase ρ` is a bundled state, not a matrix: no matrix lemma applies to it, and `rw [dephase_apply]` on
  `dephase (dephase ρ) = dephase ρ` finds no `(dephase _).m`. Go through `.m`: R11/R12 for the bridge, R15
  for states.
- `ext i j` directly on `dephase (dephase ρ) = dephase ρ` does run, but it leaves
  `↑↑(dephase (dephase ρ)) i j = ↑↑(dephase ρ) i j`: the entries through a double coercion (state → Hermitian
  matrix → matrix), not through `.m`, and `rw [dephase_apply]` fails there. Use R15 first, then `rw`, then `ext`.
- The bridge needs `rw [CPTPMap.mat_coe_eq_apply_mat]` **and then** `rfl`; `simp` does not unfold the Kraus
  map for you. `rfl` works because the Kraus index is `Fin 2` (R12).
- In `dephase_idem`, `rw [dephase_apply]` rewrites the outermost `(dephase _).m` first (W2). You need it twice,
  once for each `dephase`.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases` or `by_cases`, use `<;>` or `all_goals`.
- `simp [P]` needs the name `P` to unfold the Kraus operators. Without it `simp` sees `P 0` as an opaque
  matrix and stops.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R1, R2 |
| evaluate entries of sums of diagonals | `simp [P, Fin.sum_univ_two, Pi.single_apply]` | R3–R10 |
| `(diagonal v)ᴴ` | `Matrix.diagonal_conjTranspose`, `Pi.star_single`, `star_one` | R3, R4 |
| `diagonal v * diagonal w` | `Matrix.diagonal_mul_diagonal` | R5 |
| `Pi.single i x k` | `Pi.single_apply` / `Pi.single_eq_same`, `Pi.single_eq_of_ne` | R6, R14 |
| sum over `Fin 2` | `Fin.sum_univ_two` | R7 |
| entries of `A + B`, `diagonal v`, `1` | `Matrix.add_apply`, `diagonal_apply_eq/ne`, `one_apply_eq/ne` | R8, R9, R10 |
| `(Λ ρ).m` → linear map on `ρ.m` | `rw [CPTPMap.mat_coe_eq_apply_mat]` | R11 |
| Kraus map = Kraus sum | `rfl` | R12 |
| entries of products | `simp [names, Matrix.mul_apply, Fin.sum_univ_two]` | R13 |
| states equal ← matrices equal | `apply MState.ext_m` | R15 |
| split on `i = j` | `by_cases h : i = j` then `simp [h]` | R16 |
| see the state | infoview | |
