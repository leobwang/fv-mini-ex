/- E113 | Density matrix of a pure state | 2-3 min | MState, MState.pure, MState.m, Born rule, conj, exact_mod_cast, physlib
GOAL
  physlib's `MState d` is a mixed state (density matrix); `MState.pure ψ` is |ψ⟩⟨ψ|. Show its entries
  satisfy ρ_ji = conj ρ_ij (Hermitian), its diagonal holds the Born probabilities ρ_ii = |ψ i|², and
  those sum to 1 (trace 1).

REFERENCE
  #check MState.m          -- (ρ : MState d) : Matrix d d ℂ   the raw matrix of a state; `ρ.m i j` is an entry
  #check MState.pure_apply -- (pure ψ).m i j = ψ i * conj (ψ j)   (`conj` prints as `(starRingEnd ℂ)`)
  #check Complex.mul_conj  -- z * conj z = ↑(normSq z)   (`normSq z` = |z|², a real number)
  #check Complex.conj_conj -- conj (conj x) = x
  #check map_mul           -- f (x * y) = f x * f y   (for `conj` and any other ring hom)
  #check Ket.normalized    -- (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1
  `exact_mod_cast h` closes a goal that is `h` up to casts, e.g. `∑ x, ↑(f x) = 1` in ℂ from a sum in ℝ.
-/
import QuantumInfo.States.Mixed.MState

namespace E113

-- BEGIN SPEC
open ComplexConjugate

theorem pure_conj {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i j : d) :
    (MState.pure ψ).m j i = conj ((MState.pure ψ).m i j) :=
-- END SPEC
  by rw [MState.pure_apply, MState.pure_apply, map_mul, Complex.conj_conj, mul_comm]

-- BEGIN SPEC
theorem pure_diag {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i : d) :
    (MState.pure ψ).m i i = Complex.normSq (ψ i) :=
-- END SPEC
  by rw [MState.pure_apply, Complex.mul_conj]

-- BEGIN SPEC
theorem pure_trace {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    ∑ i, (MState.pure ψ).m i i = 1 :=
-- END SPEC
  by
    simp only [MState.pure_apply, Complex.mul_conj]
    exact_mod_cast ψ.normalized

end E113

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every statement is about entries of `(MState.pure ψ).m`, and `MState.pure_apply` gives them all.
H2. `pure_conj`: rewrite both entries, push `conj` through the product, and commute. `pure_diag`: one
    more rewrite turns `ψ i * conj (ψ i)` into `normSq`. `pure_trace`: rewrite under the sum with
    `simp only`, then the statement is `Ket.normalized` cast into ℂ.
H3. `rw [MState.pure_apply, MState.pure_apply, map_mul, Complex.conj_conj, mul_comm]`;
    `rw [MState.pure_apply, Complex.mul_conj]`;
    `simp only [MState.pure_apply, Complex.mul_conj]; exact_mod_cast ψ.normalized`.
-/
