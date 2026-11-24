/- M172 | Superexchange from the Hubbard dimer spectrum | 15-20 min | Matrix.mulVec, eigenvalue equations, linear_combination, nlinarith, mathlib
GOAL
  Two-site Hubbard model, two electrons, `S_z = 0`: (a) the triplet `|↑,↓⟩ - |↓,↑⟩` has energy 0;
  (b) for `U > 0`, every negative eigenvalue `E` solves `E² - U E - 4t² = 0`; (c) such an `E` gives a
  singlet-triplet gap `J = 0 - E` with `4t²/U - 16t⁴/U³ ≤ J ≤ 4t²/U` (superexchange, `J ≈ 4t²/U`).

REFERENCE
  example : !![(1 : ℝ), 2; 3, 4] *ᵥ ![1, 0] = ![1, 3] := by ext i; fin_cases i <;> simp  -- matrix * vector
  #check Matrix.mulVec      -- (M *ᵥ v) i = ∑ j, M i j * v j   (as `dotProduct (fun j => M i j) v`)
  #check Fin.sum_univ_four  -- ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3
  example (v w : Fin 4 → ℝ) (h : v = w) : v 2 = w 2 := congrFun h 2  -- read off one component
  example (a b c : ℝ) (h1 : a = b) (h2 : b = c) : 2 * a = b + c := by linear_combination 2 * h1 + h2
  #check mul_eq_zero        -- a * b = 0 ↔ a = 0 ∨ b = 0
  #check le_div_iff₀        -- 0 < c → (a ≤ b / c ↔ a * c ≤ b)   (and `div_le_iff₀`)
  `nlinarith` proves polynomial inequalities from hypotheses (pass products/squares as hints).
NOTE: basis `|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩`; `t` = hopping, `U` = on-site repulsion; `![a, b, c, d]` is a vector.
  Fermionic sign convention: `|↓,↑⟩ := c†₂↑ c†₁↓ |0⟩`, so in this basis the spin triplet is
  `|↑,↓⟩ - |↓,↑⟩` and the singlet `|↑,↓⟩ + |↓,↑⟩` couples to the doubly occupied states.
-/
import Mathlib

open Matrix

namespace M172

-- BEGIN SPEC
/-- Two-site Hubbard Hamiltonian at half filling, `S_z = 0` sector, basis
`|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩` (hopping `t`, on-site repulsion `U`). -/
noncomputable def H (t U : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![U, 0, -t, -t; 0, U, -t, -t; -t, -t, 0, 0; -t, -t, 0, 0]
-- END SPEC

-- BEGIN SPEC
theorem triplet_energy (t U : ℝ) : H t U *ᵥ ![0, 0, 1, -1] = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem char_eq (t U E : ℝ) (hU : 0 < U) (hE : E < 0)
    (hv : ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ H t U *ᵥ v = E • v) :
    E ^ 2 - U * E - 4 * t ^ 2 = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem superexchange (t U E : ℝ) (hU : 0 < U) (hE : E < 0)
    (hq : E ^ 2 - U * E - 4 * t ^ 2 = 0) :
    4 * t ^ 2 / U - 16 * t ^ 4 / U ^ 3 ≤ 0 - E ∧ 0 - E ≤ 4 * t ^ 2 / U :=
-- END SPEC
  sorry

end M172

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `char_eq`: write out the four component equations of `H *ᵥ v = E • v` (`congrFun hv i`, then
    `simp [H, mulVec, dotProduct, Fin.sum_univ_four] at h`). `superexchange`: put `J = -E > 0`;
    then `hq` says `J (U + J) = 4t²`. No square roots are needed anywhere.
H2. `char_eq`: argue by contradiction (`by_contra hne; apply hv0`). With `s = v 0 + v 1`, a combination
    of the four equations gives `(E² - U E - 4t²) · s = 0`, so `s = 0`; then `v 2 = v 3` (from `E < 0`),
    then `v 2 = 0`, then `v 0 = v 1 = 0` (from `U - E > 0`). `superexchange`: upper bound from
    `J U ≤ J (U + J) = 4t²`; lower bound: `J U = 4t² - J² ≥ 4t² - (4t²/U)²`, using `J ≤ 4t²/U`.
H3. `linear_combination (-E) * h0 + (-E) * h1 + (2 * t) * h2 + (2 * t) * h3` proves the `s` identity.
    Upper bound: `rw [le_div_iff₀ hU]; nlinarith`. Lower bound: rewrite the left side as
    `(4 * t ^ 2 - (4 * t ^ 2 / U) ^ 2) / U` (`field_simp; ring`), then `div_le_iff₀` and `nlinarith`
    with `pow_le_pow_left₀ _ up 2 : (-E) ^ 2 ≤ (4 * t ^ 2 / U) ^ 2`.
-/
