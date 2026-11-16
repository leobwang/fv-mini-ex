/- E112 | Kets and bra-kets | 2-3 min | Ket, Bra, Braket.dot, Ket.basis, structure literal, physlib
GOAL
  Meet physlib's `Ket d`: a vector `d → ℂ` of norm 1. Show the basis kets |i⟩ are orthonormal,
  ⟨i|j⟩ = (1 if i = j, else 0); build the qubit state |+⟩ = (|0⟩ + |1⟩)/√2 as a `Ket (Fin 2)` (you must
  prove it is normalized); and compute its overlaps ⟨i|+⟩ = 1/√2.

REFERENCE
  #check Ket.normalized'  -- (ψ : Ket d) : ∑ x, ‖ψ.vec x‖ ^ 2 = 1   (`Ket` has fields `vec`, `normalized'`)
  #check Ket.basis        -- (i : d) : Ket d   with vec = fun j => if i = j then 1 else 0
  #check Braket.dot       -- (ξ : Bra d) (ψ : Ket d) : ℂ   and `dot ξ ψ = ∑ x, ξ x * ψ x` by definition
  #check Ket.to_bra       -- (ψ : Ket d) : Bra d   conjugates every entry; it is the coercion Ket → Bra
  #check Ket.apply        -- ψ i = ψ.vec i   (likewise `Bra.apply`)
  `〈ξ‖ψ〉` (needs `open Braket`; copy the brackets from the spec) is `dot ↑ξ ψ`, i.e. ∑ x, conj (ξ x) * ψ x.
  `⟨v, h⟩ : Ket d` builds a ket from a vector `v` and a proof `h : ∑ x, ‖v x‖ ^ 2 = 1`.
  `simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]` unfolds a bra-ket into a sum and computes it.
-/
import QuantumInfo.States.Pure.Braket

namespace E112

-- BEGIN SPEC
open Braket

theorem basis_orthonormal {d : Type} [Fintype d] [DecidableEq d] (i j : d) :
    〈Ket.basis i‖Ket.basis j〉 = if i = j then 1 else 0 :=
-- END SPEC
  by simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]

-- BEGIN SPEC
noncomputable def plus : Ket (Fin 2) :=
-- END SPEC
  ⟨fun _ => ((Real.sqrt 2)⁻¹ : ℂ), by simp⟩

-- BEGIN SPEC
theorem plus_apply (i : Fin 2) : plus i = ((Real.sqrt 2)⁻¹ : ℂ) :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem plus_overlap (i : Fin 2) : 〈Ket.basis i‖plus〉 = ((Real.sqrt 2)⁻¹ : ℂ) :=
-- END SPEC
  by simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply, plus]

end E112

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A bra-ket is a finite sum; once everything is unfolded, `simp` can evaluate sums of `if`s.
H2. `plus`: an anonymous constructor whose vector is constantly `1/√2`; the norm proof
    (`2 * (1/√2)² = 1`) is a job for `simp`. `plus_apply` then holds by definition. For the overlaps,
    unfold `plus` together with the bra-ket definitions.
H3. `⟨fun _ => ((Real.sqrt 2)⁻¹ : ℂ), by simp⟩`; `rfl`;
    `simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]` (add `plus` for `plus_overlap`).
-/
