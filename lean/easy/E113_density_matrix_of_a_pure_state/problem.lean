/- E113 | Density matrix of a pure state | 2-3 min | MState, MState.pure, MState.m, Born rule, conj, exact_mod_cast, physlib
GOAL
  physlib's `MState d` is a mixed state (density matrix); `MState.pure ψ` is |ψ⟩⟨ψ|. Show its entries
  satisfy ρ_ji = conj ρ_ij (Hermitian), its diagonal holds the Born probabilities ρ_ii = |ψ i|², and
  those sum to 1 (trace 1).

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.States.Mixed.MState

namespace E113

/- SKELETON · pure_conj
  1. Turn both matrix entries into ket entries (the left entry first, then the right):   R1, R1
       ⊢ ψ j * conj (ψ i) = conj (ψ i * conj (ψ j))
  2. Push `conj` through the product, then cancel the double conjugate:                R2, R3
  3. Both sides are now the same product in opposite order; the `rw` closes it:          R4
-/
-- BEGIN SPEC
open ComplexConjugate

theorem pure_conj {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i j : d) :
    (MState.pure ψ).m j i = conj ((MState.pure ψ).m i j) :=
-- END SPEC
  sorry

/- SKELETON · pure_diag
  1. Turn the diagonal entry into `ψ i * conj (ψ i)`:                                   R1
  2. An entry times its conjugate is its `normSq`, cast into ℂ; the `rw` closes it:      R5
-/
-- BEGIN SPEC
theorem pure_diag {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i : d) :
    (MState.pure ψ).m i i = Complex.normSq (ψ i) :=
-- END SPEC
  sorry

/- SKELETON · pure_trace
  1. Rewrite every summand (it sits under `∑`, so not with `rw`), using R1 and R5:      R6
       ⊢ ∑ x, ↑(Complex.normSq (ψ x)) = 1
  2. That is the ket's normalization (a sum in ℝ), cast into ℂ:                        R7 → R8
-/
-- BEGIN SPEC
theorem pure_trace {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    ∑ i, (MState.pure ψ).m i i = 1 :=
-- END SPEC
  sorry

end E113

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three statements are about entries of `(MState.pure ψ).m`, and `MState.pure_apply` (R1) turns
    each entry into ket entries `ψ i * conj (ψ j)`.
H2. `pure_conj`: R1 on both sides, push `conj` inside and cancel it (R2, R3), then commute (R4).
    `pure_diag`: R1, then `Complex.mul_conj` (R5). `pure_trace`: the same two rewrites, but under the
    sum, so with `simp only` (R6); what is left is `Ket.normalized` (R7) cast into ℂ (R8).
H3. `rw [MState.pure_apply, MState.pure_apply, map_mul, Complex.conj_conj, mul_comm]`;
    `rw [MState.pure_apply, Complex.mul_conj]`;
    `simp only [MState.pure_apply, Complex.mul_conj]` then `exact_mod_cast ψ.normalized`.
-/
