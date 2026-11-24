/- Guide for M146 (The dephasing channel).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. (It is a
placeholder here, not the exercise's Kraus operators `P k`.) A hypothesis `h` in an entry is only there
to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the identity channel on a qutrit,
other diagonal matrices).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.Channels.CPTP

open Matrix

namespace M146Guide

/-! # Part R · Reference entries -/

/-! ## Matrix equations → entries -/

/-! ### R1. `ext i j` (lemma `Matrix.ext`) · goal `M = N` → context gains `i j`, goal is one entry -/
example {α : Type} (M N : Matrix (Fin 2) (Fin 2) α) (h : ∀ i j, M i j = N i j) : M = N := by
  ext i j
  exact h i j

/-! ### R2. `fin_cases i` · context loses `i : Fin 2`; goal → one goal per value of `i`
`(fun i => i) ⟨0, ⋯⟩` is how Lean prints the index `0`. -/
example (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) (i : Fin 2) : P i := by
  fin_cases i
  exacts [h0, h1]

/-! ## Diagonal matrices and `Pi.single` (`simp` applies R3–R10 by itself) -/

/-! ### R3. `Matrix.diagonal_conjTranspose` · `(diagonal v)ᴴ = diagonal (star v)` · goal
`diagonal v` is the square matrix with `v i` at `(i, i)` and `0` elsewhere; `Aᴴ` is the conjugate
transpose; `star v` conjugates every entry of the vector `v`. -/
example {α : Type} [AddMonoid α] [StarAddMonoid α] {d : Type} [DecidableEq d] (v : d → α)
    (P : Matrix d d α → Prop) (h : P (diagonal (star v))) : P (diagonal v)ᴴ := by
  rw [Matrix.diagonal_conjTranspose]
  exact h

/-! ### R4. `Pi.star_single`, `star_one` · goal: `star (Pi.single i 1)` → `Pi.single i 1`
`Pi.single i x : d → β` is the vector with `x` at index `i` and `0` elsewhere (a basis vector when
`x = 1`). Conjugating it conjugates `x`, and `star 1 = 1`. -/
example {d : Type} [DecidableEq d] (i : d) (P : (d → ℂ) → Prop) (h : P (Pi.single i 1)) :
    P (star (Pi.single i (1 : ℂ))) := by
  rw [Pi.star_single]
  rw [star_one]
  exact h

/-! ### R5. `Matrix.diagonal_mul_diagonal` · goal: product of diagonals → diagonal of the products -/
example {d : Type} [Fintype d] [DecidableEq d] (v w : d → ℂ) (P : Matrix d d ℂ → Prop)
    (h : P (diagonal fun i => v i * w i)) : P (diagonal v * diagonal w) := by
  rw [Matrix.diagonal_mul_diagonal]
  exact h

/-! ### R6. `Pi.single_apply` · `Pi.single i x k = if k = i then x else 0` · goal
On concrete indices `simp` then decides the condition (`0 = 0` true, `0 = 1` false) and drops the `if`. -/
example {d : Type} [DecidableEq d] {β : Type} [Zero β] (i k : d) (x : β) (P : β → Prop)
    (h : P (if k = i then x else 0)) : P ((Pi.single i x : d → β) k) := by
  rw [Pi.single_apply]
  exact h

/-! ### R7. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms (here a sum of matrices) -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → Matrix (Fin 2) (Fin 2) β)
    (P : Matrix (Fin 2) (Fin 2) β → Prop) (h : P (f 0 + f 1)) : P (∑ k, f k) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R8. `Matrix.add_apply` · goal: entry of `A + B` → sum of the entries -/
example {d : Type} {α : Type} [Add α] (A B : Matrix d d α) (i j : d) (P : α → Prop)
    (h : P (A i j + B i j)) : P ((A + B) i j) := by
  rw [Matrix.add_apply]
  exact h

/-! ### R9. `Matrix.diagonal_apply_eq`, `Matrix.diagonal_apply_ne` · goal: entries of `diagonal v`
On the diagonal `diagonal v i i = v i`; off it `diagonal v i j = 0`, given `i ≠ j`.
`P : α → α → Prop` takes both entries at once. -/
example {d : Type} [DecidableEq d] {α : Type} [Zero α] (v : d → α) (i j : d) (hij : i ≠ j)
    (P : α → α → Prop) (h : P (v i) 0) : P (diagonal v i i) (diagonal v i j) := by
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ hij]
  exact h

/-! ### R10. `Matrix.one_apply_eq`, `Matrix.one_apply_ne` · goal: entries of the identity `1` -/
example {d : Type} [DecidableEq d] (i j : d) (hij : i ≠ j) (P : ℂ → ℂ → Prop) (h : P 1 0) :
    P ((1 : Matrix d d ℂ) i i) ((1 : Matrix d d ℂ) i j) := by
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne hij]
  exact h

/-! ## Channels: from `Λ ρ` to the Kraus sum -/

/-! ### R11. `CPTPMap.mat_coe_eq_apply_mat` · goal: `(Λ ρ).m` → the channel's linear map applied to `ρ.m`
`Λ : CPTPMap dIn dOut ℂ` is a channel; `Λ ρ : MState dOut` applies it to a state; `.m` is a state's
density matrix. `Λ.map` is the underlying linear map on matrices; the infoview prints it as
`(((Λ.toPTPMap ℂ).toPMap ℂ).toHPMap ℂ).map`. -/
example {dIn dOut : Type} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
    (Λ : CPTPMap dIn dOut ℂ) (ρ : MState dIn) (P : Matrix dOut dOut ℂ → Prop) (h : P (Λ.map ρ.m)) :
    P (Λ ρ).m := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  exact h

/-! ### R12. `rfl` · closes "the map of `of_kraus_CPTPMap M _` is `∑ k, M k * X * (M k)ᴴ`"
True by definition (`MatrixMap.of_kraus`), so `rfl` closes it, but only when the Kraus index is a
concrete `Fin n`: for an abstract index type `κ` the sum does not unfold and `rfl` fails. -/
example {d : Type} [Fintype d] [DecidableEq d] (M : Fin 3 → Matrix d d ℂ)
    (hM : ∑ k, (M k)ᴴ * M k = 1) (X : Matrix d d ℂ) :
    (CPTPMap.of_kraus_CPTPMap M hM).map X = ∑ k, M k * X * (M k)ᴴ := by
  rfl

/-! ### R13. `Matrix.mul_apply` · goal: entry of a product → a sum over the middle index -/
example {d : Type} [Fintype d] [DecidableEq d] {α : Type} [Mul α] [AddCommMonoid α]
    (A B : Matrix d d α) (i k : d) (P : α → Prop) (h : P (∑ j, A i j * B j k)) :
    P ((A * B) i k) := by
  rw [Matrix.mul_apply]
  exact h

/-! ### R14. `Pi.single_eq_same`, `Pi.single_eq_of_ne` · goal: `Pi.single i x i` → `x`, `Pi.single i x j` → `0` -/
example {d : Type} [DecidableEq d] {β : Type} [Zero β] (i j : d) (hji : j ≠ i) (x : β)
    (P : β → β → Prop) (h : P x 0) : P ((Pi.single i x : d → β) i) ((Pi.single i x : d → β) j) := by
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hji]
  exact h

/-! ## States and case splits -/

/-! ### R15. `apply MState.ext_m` · goal: equality of states → equality of their matrices -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ σ : MState d) (h : ρ.m = σ.m) : ρ = σ := by
  apply MState.ext_m
  exact h

/-! ### R16. `by_cases h : i = j` · goal list: one goal → two (`case pos` with `h : i = j`,
`case neg` with `h : ¬i = j`); context gains `h` in each -/
example {d : Type} (i j : d) (G : Prop) (hy : i = j → G) (hn : ¬i = j → G) : G := by
  by_cases h : i = j
  exact hy h
  exact hn h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A channel from one Kraus operator: the identity channel on a qutrit (`Fin 3`) -/
def K (_ : Fin 1) : Matrix (Fin 3) (Fin 3) ℂ := 1

theorem K_tp : ∑ k, (K k)ᴴ * K k = 1 := by simp [K]

noncomputable def idCh : CPTPMap (Fin 3) (Fin 3) ℂ := CPTPMap.of_kraus_CPTPMap K K_tp

/-- the bridge for `idCh`: R11, then R12 -/
theorem idCh_kraus (ρ : MState (Fin 3)) : (idCh ρ).m = ∑ k, K k * ρ.m * (K k)ᴴ := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  rfl

/-- after the bridge it is matrix arithmetic -/
theorem idCh_m (ρ : MState (Fin 3)) : (idCh ρ).m = ρ.m := by
  rw [idCh_kraus]
  simp [K]

/-! ### W2. `rw` with a lemma about `(idCh ?ρ).m` rewrites the outermost occurrence first -/
example (ρ : MState (Fin 3)) : (idCh (idCh ρ)).m = ρ.m := by
  rw [idCh_m]
  rw [idCh_m]

/-! ### W3. An entry identity of diagonals: `ext`, then R16, then `simp [h]` (R9 inside) -/
example (v w : Fin 3 → ℂ) : diagonal v * diagonal w = diagonal (fun k => v k * w k) := by
  ext i j
  by_cases h : i = j
  all_goals simp [h]

end M146Guide
