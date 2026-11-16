/- H080 | The swap test | 45-75 min | controlled-SWAP, circuit, Finset sums over d × d, normSq, physlib
GOAL
  The swap test: start in |0⟩|ψ⟩|φ⟩, apply H to the ancilla qubit, swap the two registers if the
  ancilla is 1 (controlled-SWAP), apply H again, measure the ancilla. It reads 0 with probability
  `(1 + |⟨ψ|φ⟩|²) / 2`, so it estimates the overlap of two unknown states.

REFERENCE
  -- `ψ : Ket d` is a unit vector; `ψ i : ℂ` its i-th amplitude (= `ψ.vec i`, ∑ |ψ i|² = 1);  `starRingEnd ℂ` = conj
  -- ancilla ⊗ reg₁ ⊗ reg₂ state: `Fin 2 × d × d → ℂ`, `p.1` ancilla, `p.2 = (i, j)`;  `〈ψ‖φ〉` = ∑ i, conj (ψ i) * φ i
  #check Complex.normSq_add      -- normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re
  #check Complex.normSq_mul      -- normSq (z * w) = normSq z * normSq w
  #check Complex.normSq_eq_conj_mul_self  -- (normSq z : ℂ) = conj z * z
  #check Complex.sq_norm         -- ‖z‖ ^ 2 = normSq z   (`Complex.normSq z = |z|²`, a real number)
  #check Complex.re_sum          -- (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re
  #check Ket.normalized          -- (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1
  example {d : Type} [Fintype d] (f : d × d → ℝ) : ∑ q : d × d, f q.swap = ∑ q, f q :=
    Fintype.sum_equiv (Equiv.prodComm d d) _ _ fun _ => rfl     -- reindex a sum by a bijection
  example : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
-/
import QuantumInfo.States.Pure.Braket

namespace H080

open Braket

-- BEGIN SPEC
/-- Hadamard on the ancilla: `(H v)(a, r) = (v (0, r) + (-1)^a v (1, r)) / √2` -/
noncomputable def hA {d : Type} (v : Fin 2 × d × d → ℂ) : Fin 2 × d × d → ℂ :=
  fun p => (Real.sqrt 2 : ℂ)⁻¹ * (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2))

/-- controlled-SWAP: exchange the two registers when the ancilla is 1 -/
def cswap {d : Type} (v : Fin 2 × d × d → ℂ) : Fin 2 × d × d → ℂ :=
  fun p => if p.1 = 0 then v p else v (p.1, p.2.2, p.2.1)

/-- the input |0⟩ ⊗ |ψ⟩ ⊗ |φ⟩ -/
def input {d : Type} [Fintype d] (ψ φ : Ket d) : Fin 2 × d × d → ℂ :=
  fun p => if p.1 = 0 then ψ p.2.1 * φ p.2.2 else 0
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- the final amplitude with the ancilla at 0 is the symmetrised product -/
theorem swap_amp {d : Type} [Fintype d] (ψ φ : Ket d) (i j : d) :
    hA (cswap (hA (input ψ φ))) (0, (i, j)) = (1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i) := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [hA, cswap, input]
  simp
  linear_combination (ψ i * φ j + ψ j * φ i) * h2

-- MILESTONE (optional: change or delete)
theorem sum_normSq_prod {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, Complex.normSq (ψ q.1 * φ q.2) = 1 := by
  simp only [Complex.normSq_mul, Fintype.sum_prod_type, ← Finset.sum_mul_sum, Ket.normalized,
    mul_one]

-- MILESTONE (optional: change or delete)
/-- the interference term is |⟨ψ|φ⟩|² -/
theorem cross_term {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, (ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)).re = ‖〈ψ‖φ〉‖ ^ 2 := by
  have h : ∑ q : d × d, ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)
      = starRingEnd ℂ 〈ψ‖φ〉 * 〈ψ‖φ〉 := by
    simp only [Braket.dot, map_sum, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Ket.to_bra, Bra.apply, Ket.apply]
    ring
  rw [← Complex.re_sum, h, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]

-- BEGIN SPEC
theorem swap_test {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, Complex.normSq (hA (cswap (hA (input ψ φ))) (0, q)) = (1 + ‖〈ψ‖φ〉‖ ^ 2) / 2 :=
-- END SPEC
  by
    have e : ∀ q : d × d, Complex.normSq (hA (cswap (hA (input ψ φ))) (0, q)) =
        (Complex.normSq (ψ q.1 * φ q.2) + Complex.normSq (ψ q.2 * φ q.1)
          + 2 * (ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)).re) / 4 := by
      intro q
      rw [swap_amp, Complex.normSq_mul, Complex.normSq_add]
      norm_num
      ring
    -- WHY: the swapped norm sum is the same sum, reindexed by (i, j) ↦ (j, i)
    have h1 : ∑ q : d × d, Complex.normSq (ψ q.2 * φ q.1) = 1 := by
      rw [← sum_normSq_prod ψ φ]
      exact Fintype.sum_equiv (Equiv.prodComm d d) _ _ fun _ => rfl
    simp only [e, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, cross_term,
      sum_normSq_prod, h1]
    ring

end H080

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work out the final amplitude at `(0, (i, j))` by hand first: it is `(ψᵢφⱼ + ψⱼφᵢ) / 2`. Then
    `|x + y|² = |x|² + |y|² + 2 Re(x ȳ)` splits the probability into two "norm" sums and one cross sum.
H2. `swap_amp`: `simp only [hA, cswap, input]`, then `simp` to evaluate the `if`s on `Fin 2`, and close
    with the `1/√2 · 1/√2 = 1/2` fact (`linear_combination (...) * h2`). Norm sums: `normSq_mul` and
    `Fintype.sum_prod_type` factor them into `(∑ |ψᵢ|²)(∑ |φⱼ|²)`; the swapped one reindexes by
    `Equiv.prodComm`. Cross sum: the complex double sum equals `conj ⟨ψ|φ⟩ * ⟨ψ|φ⟩`.
H3. In `cross_term`: `have h : ∑ q : d × d, ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1) =
    starRingEnd ℂ 〈ψ‖φ〉 * 〈ψ‖φ〉` (unfold `Braket.dot`, `map_sum`, `Fintype.sum_prod_type`,
    `Finset.sum_mul_sum`, match terms), then `rw [← Complex.re_sum, h, ← Complex.normSq_eq_conj_mul_self]`.
    Main: rewrite each summand to `(normSq (ψ q.1 * φ q.2) + normSq (ψ q.2 * φ q.1) + 2 * (cross).re) / 4`
    (`swap_amp`, `normSq_mul`, `normSq_add`), then `Finset.sum_div`, `Finset.sum_add_distrib`, `Finset.mul_sum`.
-/
