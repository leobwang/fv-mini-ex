/- H080 | The swap test | 45-75 min | controlled-SWAP, circuit, Finset sums over d × d, normSq, physlib
GOAL
  The swap test: start in |0⟩|ψ⟩|φ⟩, apply H to the ancilla qubit, swap the two registers if the
  ancilla is 1 (controlled-SWAP), apply H again, measure the ancilla. It reads 0 with probability
  `(1 + |⟨ψ|φ⟩|²) / 2`, so it estimates the overlap of two unknown states.

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · swap_amp   (MILESTONE 1, used in step 1 of `swap_test`)
  1. Prove the √2 fact first (a `have`):
       h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2      proof: R3 → R4 → R5 → R6
  2. Unfold the three circuit stages at once: simp only [hA, cswap, input]   R1
  3. Clear the `if`s (`if True`, `if 1 = 0` in `Fin 2`):                     R2
  4. Close with the √2 fact, coefficient = the symmetrised product:          R7
-/
-- MILESTONE (optional: change or delete)
/-- the final amplitude with the ancilla at 0 is the symmetrised product -/
theorem swap_amp {d : Type} [Fintype d] (ψ φ : Ket d) (i j : d) :
    hA (cswap (hA (input ψ φ))) (0, (i, j)) = (1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i) := by
  sorry

/- SKELETON · sum_normSq_prod   (MILESTONE 2, used in step 2 and step 5 of `swap_test`)
  1. Split |ψᵢ φⱼ|² into |ψᵢ|² |φⱼ|²:                         R8
  2. Sum over pairs → double sum:                             R9
  3. Factor the double sum into (∑ |ψᵢ|²) * (∑ |φⱼ|²):        R10
  4. Each factor is 1, then 1 * 1:                            R11, R12
  (steps 1–4 fit in one `simp only [...]`)
-/
-- MILESTONE (optional: change or delete)
theorem sum_normSq_prod {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, Complex.normSq (ψ q.1 * φ q.2) = 1 := by
  sorry

/- SKELETON · cross_term   (MILESTONE 3, used in step 5 of `swap_test`)
  1. Prove the complex identity first (a `have`):
       h : ∑ q : d × d, ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1) = starRingEnd ℂ 〈ψ‖φ〉 * 〈ψ‖φ〉
     a. unfold 〈ψ‖φ〉, conj of the sum, pair sum → double sum,
        product of sums → double sum (one `simp only`):            R13, R14, R9, R15
     b. compare the two double sums term by term (nested twice):   R16
     c. evaluate bra/ket amplitudes and conj of products (one `simp`), then `ring`:   R17, R18, R19
  2. Pull `.re` out of the sum, then rw [h]:                       R20
  3. conj z * z → ↑(normSq z), take `.re`, then ‖z‖ ^ 2 → normSq z:  R21 → R22 → R23
-/
-- MILESTONE (optional: change or delete)
/-- the interference term is |⟨ψ|φ⟩|² -/
theorem cross_term {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, (ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)).re = ‖〈ψ‖φ〉‖ ^ 2 := by
  sorry

/- SKELETON · swap_test
  Prove the three MILESTONES above first; this proof only assembles them.
  1. Per-term formula (a `have e : ∀ q : d × d, … := by intro q; …`):
       e : ∀ q, normSq (final amplitude at (0, q)) =
             (normSq (ψ q.1 * φ q.2) + normSq (ψ q.2 * φ q.1)
               + 2 * (ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)).re) / 4
       proof: rw [swap_amp] (MILESTONE 1), then R8, R24, then R25, then `ring`
  2. The swapped norm sum is 1 too:
       h1 : ∑ q : d × d, Complex.normSq (ψ q.2 * φ q.1) = 1
       proof: rw [← sum_normSq_prod ψ φ] (MILESTONE 2), then R26
  3. Rewrite every summand with e (under the ∑):                  R27
  4. Pull out / 4, split the sum of three terms, pull out 2 *:   R28, R29, R30
  5. Substitute cross_term, sum_normSq_prod, h1 (MILESTONES 3, 2):  R27 (simp only [...])
  6. (1 + 1 + 2 * x) / 4 = (1 + x) / 2:                           ring
-/
-- BEGIN SPEC
theorem swap_test {d : Type} [Fintype d] (ψ φ : Ket d) :
    ∑ q : d × d, Complex.normSq (hA (cswap (hA (input ψ φ))) (0, q)) = (1 + ‖〈ψ‖φ〉‖ ^ 2) / 2 :=
-- END SPEC
  sorry

end H080

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work out the final amplitude at `(0, (i, j))` by hand first: it is `(ψᵢφⱼ + ψⱼφᵢ) / 2` (MILESTONE
    `swap_amp`). Then `|x + y|² = |x|² + |y|² + 2 Re(x ȳ)` (R24) splits the probability into two "norm"
    sums, each equal to 1 (`sum_normSq_prod`), and one cross sum, equal to `|⟨ψ|φ⟩|²` (`cross_term`).
H2. `swap_amp`: prove the √2 fact `h2` (R3–R6), unfold with `simp only [hA, cswap, input]` (R1), let `simp`
    clear the `if`s on `Fin 2` (R2), close with `linear_combination (...) * h2` (R7).
    `sum_normSq_prod`: `normSq_mul`, `Fintype.sum_prod_type`, `← Finset.sum_mul_sum`, `Ket.normalized`
    (R8–R12). `cross_term`: the complex double sum equals `conj ⟨ψ|φ⟩ * ⟨ψ|φ⟩`; take `.re` (R20–R23).
    Main: rewrite each summand under the `∑` (R27), split the sums (R28–R30); the swapped norm sum is
    `sum_normSq_prod` reindexed by `Equiv.prodComm` (R26).
H3. In `cross_term`: `have h : ∑ q : d × d, ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1) =
    starRingEnd ℂ 〈ψ‖φ〉 * 〈ψ‖φ〉` (unfold `Braket.dot`, `map_sum`, `Fintype.sum_prod_type`,
    `Finset.sum_mul_sum`, then match terms with `Finset.sum_congr` twice), then
    `rw [← Complex.re_sum, h, ← Complex.normSq_eq_conj_mul_self]` and finish with R22, R23.
    Main: rewrite each summand to `(normSq (ψ q.1 * φ q.2) + normSq (ψ q.2 * φ q.1) + 2 * (cross).re) / 4`
    (`swap_amp`, `normSq_mul`, `normSq_add`, then `norm_num; ring`), then `simp only [e, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.mul_sum, …]` with the three milestones.
-/
