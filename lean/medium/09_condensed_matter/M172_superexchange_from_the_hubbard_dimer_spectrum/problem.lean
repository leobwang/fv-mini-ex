/- M172 | Superexchange from the Hubbard dimer spectrum | 15-20 min | Matrix.mulVec, eigenvalue equations, linear_combination, nlinarith, mathlib
GOAL
  Two-site Hubbard model, two electrons, `S_z = 0`: (a) the triplet `|↑,↓⟩ - |↓,↑⟩` has energy 0;
  (b) for `U > 0`, every negative eigenvalue `E` solves `E² - U E - 4t² = 0`; (c) such an `E` gives a
  singlet-triplet gap `J = 0 - E` with `4t²/U - 16t⁴/U³ ≤ J ≤ 4t²/U` (superexchange, `J ≈ 4t²/U`).

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · triplet_energy
  1. Vector equation → four component goals:                               R1, R2
  2. On all four goals at once (`<;>`): `simp` with `H` and the product
     lemmas, which unfolds `*ᵥ`, `⬝ᵥ`, the sum and the literal entries:    R3 → R4 → R5, R6, R7, R8
-/
-- BEGIN SPEC
theorem triplet_energy (t U : ℝ) : H t U *ᵥ ![0, 0, 1, -1] = 0 :=
-- END SPEC
  sorry

/- SKELETON · char_eq
  1. Unpack the eigenvector `v`, `hv0 : v ≠ 0`, `hv : H t U *ᵥ v = E • v`:   R9
  2. Four component equations as hypotheses `h0 h1 h2 h3`, then simplify
     them all in one `simp [H, mulVec, dotProduct, Fin.sum_univ_four] at …`:  R10 (×4), R12 with R3–R5, R7, R11
  3. Contradiction: assume `hne : ¬ (E² - U E - 4t² = 0)`, aim for `v = 0`:  R13, R14
  4. Milestones, in this order, each a `have` (each uses the previous ones):
       hs  : v 0 + v 1 = 0   from `(E²-UE-4t²) * (v 0 + v 1) = 0`           R15, then R16 → R17 with hne
       h23 : v 2 = v 3       from `E * (v 2 - v 3) = 0`                       R15, R16 → R17 with R18, R20
       hv2 : v 2 = 0         from `E * v 2 = 0` (uses hs)                     R15, R16 → R17 with R18
       hv0': v 0 = 0         from `(U - E) * v 0 = 0` (uses hv2, h23)         R15 (R19 for v 3 = 0), R16 → R17, R20
  5. Close `v = 0` component by component (v 1 from hs and hv0'):           R1, R2, R8 via `simp`, R20
-/
-- BEGIN SPEC
theorem char_eq (t U E : ℝ) (hU : 0 < U) (hE : E < 0)
    (hv : ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ H t U *ᵥ v = E • v) :
    E ^ 2 - U * E - 4 * t ^ 2 = 0 :=
-- END SPEC
  sorry

/- SKELETON · superexchange
  1. With J = -E, the quadratic as `hJU : (-E) * (U + -E) = 4 * t ^ 2`:       R15
  2. Upper bound first, as `up : -E ≤ 4 * t ^ 2 / U` (also used in step 5):   R21, R22
  3. Split the conjunction; the second half follows from `up`:              refine ⟨?_, by linarith⟩, R20
  4. Rewrite the lower bound's left side as one fraction:
       h4 : 4 * t ^ 2 / U - 16 * t ^ 4 / U ^ 3 = (4 * t ^ 2 - (4 * t ^ 2 / U) ^ 2) / U
                                                                            R23, then `ring`
  5. rw [h4], clear the denominator, square `up`, finish:                   R24, R25 (with R20), R22
-/
-- BEGIN SPEC
theorem superexchange (t U E : ℝ) (hU : 0 < U) (hE : E < 0)
    (hq : E ^ 2 - U * E - 4 * t ^ 2 = 0) :
    4 * t ^ 2 / U - 16 * t ^ 4 / U ^ 3 ≤ 0 - E ∧ 0 - E ≤ 4 * t ^ 2 / U :=
-- END SPEC
  sorry

end M172

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything is polynomial arithmetic on four component equations; no square roots are needed.
    `triplet_energy`: compare components (`ext i`, `fin_cases i`) and let `simp` compute. `char_eq`:
    get the components of `hv` as hypotheses (`congrFun hv i`, then `simp […] at`). `superexchange`:
    put `J = -E > 0`; then `hq` says `J (U + J) = 4t²`.
H2. `char_eq`: by contradiction (`by_contra hne; apply hv0`), then show each component of `v` is 0.
    With `s = v 0 + v 1`, a combination of the four equations is `(E² - U E - 4t²) · s = 0`, so `s = 0`;
    then `v 2 = v 3` (`E ≠ 0`), then `v 2 = 0`, then `v 0 = 0` (`U - E ≠ 0`), each by
    `linear_combination` + `mul_eq_zero` + `Or.resolve_left`. `superexchange`: upper bound from
    `J U ≤ J (U + J) = 4t²`; lower bound from `J U = 4t² - J² ≥ 4t² - (4t²/U)²`, using `J ≤ 4t²/U`.
H3. The `s` identity: `linear_combination (-E) * h0 + (-E) * h1 + (2 * t) * h2 + (2 * t) * h3`.
    Upper bound: `rw [le_div_iff₀ hU]; nlinarith`. Lower bound: after `rw [h4, div_le_iff₀ hU]`, give
    `nlinarith` the fact `pow_le_pow_left₀ (by linarith) up 2 : (-E) ^ 2 ≤ (4 * t ^ 2 / U) ^ 2`.
-/
