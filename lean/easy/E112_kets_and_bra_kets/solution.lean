/- E112 | Kets and bra-kets | 2-3 min | Ket, Bra, Braket.dot, Ket.basis, structure literal, physlib
GOAL
  Meet physlib's `Ket d`: a vector `d → ℂ` of norm 1. Show the basis kets |i⟩ are orthonormal,
  ⟨i|j⟩ = (1 if i = j, else 0); build the qubit state |+⟩ = (|0⟩ + |1⟩)/√2 as a `Ket (Fin 2)` (you must
  prove it is normalized); and compute its overlaps ⟨i|+⟩ = 1/√2.

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Pure.Braket

namespace E112

/- SKELETON · basis_orthonormal
  1. Bra-ket → a sum over `x : d`:                                         R1
  2. The bra and the kets → their vectors, then their entries:
       the bra of a ket, the basis-ket literal                              R2, R5
       entries of the literals                                              R3
       entry of the conjugated vector, then the inner entry                 R4, R3
  3. Each term is now `conj (if i = x then 1 else 0) * (if j = x then 1 else 0)`:
       conj fixes 0 and 1; factor into the `if`; drop `* 1`, `* 0`         R6 → R7 → R9
  4. The sum has one nonzero term, at `x = j`:                              R10 → R11
  5. Left: `(if i = j then 1 else 0) = if i = j then 1 else 0`, with two
     different decidability instances, so not `rfl`:                       R12
  Steps 1–5 are ONE `simp` call that names the definitions of R1, R2, R3 (both), R5;
  `simp` applies R4 and R6–R12 by itself.
-/
-- BEGIN SPEC
open Braket

theorem basis_orthonormal {d : Type} [Fintype d] [DecidableEq d] (i j : d) :
    〈Ket.basis i‖Ket.basis j〉 = if i = j then 1 else 0 :=
-- END SPEC
  by simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]

/- SKELETON · plus
  1. Anonymous constructor: the vector (constantly `((Real.sqrt 2)⁻¹ : ℂ)`) and a
     `by` proof of the normalization goal `∑ x, ‖(↑√2)⁻¹‖ ^ 2 = 1`:        R13
  2. That proof is `simp`, which goes:
       ‖(↑√2)⁻¹‖ ^ 2 → (√2 ^ 2)⁻¹ → 2⁻¹                                     R14 → R15 → R16 → R17 → R18 → R19
       ∑ over `Fin 2` of a constant → 2 • 2⁻¹ → 2 * 2⁻¹ → 1                 R20 → R21 → R22
-/
-- BEGIN SPEC
noncomputable def plus : Ket (Fin 2) :=
-- END SPEC
  ⟨fun _ => ((Real.sqrt 2)⁻¹ : ℂ), by simp⟩

/- SKELETON · plus_apply
  1. Holds by unfolding `plus`, the entry coercion and your constant vector:  R23
-/
-- BEGIN SPEC
theorem plus_apply (i : Fin 2) : plus i = ((Real.sqrt 2)⁻¹ : ℂ) :=
-- END SPEC
  rfl

/- SKELETON · plus_overlap
  1. As in `basis_orthonormal`: ONE `simp` call naming the definitions of R1, R2, R3, R5,
     and also `plus` (unfold your own definition, like R5).
  2. `simp` then applies R4, R6, and, because the basis ket is now the LEFT factor,
     R8 → R9 (`one_mul`, `zero_mul`) instead of R7; then R10 → R11.
     The entry `(↑√2)⁻¹` passes through unchanged: no √2 arithmetic.
-/
-- BEGIN SPEC
theorem plus_overlap (i : Fin 2) : 〈Ket.basis i‖plus〉 = ((Real.sqrt 2)⁻¹ : ℂ) :=
-- END SPEC
  by simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply, plus]

end E112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A bra-ket is a finite sum of entry products (R1). Once the bra, the kets and `plus` are unfolded
    into their vectors (R2, R3, R5), each sum has a single nonzero term, which `simp` finds (R10, R11).
    `plus` is a structure literal: a vector plus a proof that it is normalized (R13).
H2. `basis_orthonormal` and `plus_overlap`: one `simp` that names the physlib definitions (and `plus`).
    `plus`: the constant vector `fun _ => ((Real.sqrt 2)⁻¹ : ℂ)`; its proof `2 · (1/√2)² = 1` is a job
    for `simp` (R14–R22). `plus_apply` then holds by definition (R23).
H3. `simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]` (add `plus` for `plus_overlap`);
    `⟨fun _ => ((Real.sqrt 2)⁻¹ : ℂ), by simp⟩`; `rfl`.
-/
