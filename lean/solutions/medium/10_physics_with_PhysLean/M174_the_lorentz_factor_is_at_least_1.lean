/- M174 | The Lorentz factor is at least 1 | 10 min | boost matrix entries, Real.sqrt, one_le_div, nlinarith, physlib
GOAL
  `boost i β hβ` is the Lorentz boost with speed `β = v / c` (speed in units of `c`, `|β| < 1`) along
  spatial axis `i`. Show its time-time entry `Λ⁰₀ = (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0)` is `≥ 1`
  (that entry is the Lorentz factor `γ β = 1 / √(1 - β ^ 2)`: moving clocks never run fast).

REFERENCE
  -- `(boost i β hβ).1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ`; `Sum.inl 0` is time, `Sum.inr i` is space
  #check LorentzGroup.boost_inl_0_inl_0  -- (boost i β hβ).1 (inl 0) (inl 0) = γ β
  #check LorentzGroup.γ     -- γ β = 1 / √(1 - β ^ 2); `unfold γ` exposes it.  `√x` is `Real.sqrt x`
  #check abs_lt             -- |a| < b ↔ -b < a ∧ a < b
  #check Real.sqrt_le_one   -- √x ≤ 1 ↔ x ≤ 1
  #check Real.sqrt_pos      -- 0 < √x ↔ 0 < x
  #check one_le_div         -- 0 < b → (1 ≤ a / b ↔ b ≤ a)
  example (x : ℝ) (h : -1 < x ∧ x < 1) : x ^ 2 < 1 := by nlinarith [h.1, h.2]
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup

namespace M174

-- BEGIN SPEC
theorem one_le_gamma {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) :
    1 ≤ (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0) :=
-- END SPEC
  by
    rw [boost_inl_0_inl_0]
    unfold γ
    have h1 : 0 < 1 - β ^ 2 := by nlinarith [abs_lt.mp hβ]
    rw [one_le_div (Real.sqrt_pos.mpr h1)]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg β])

end M174

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First turn the matrix entry into `γ β` (find the physlib lemma named after the entry). Then
    `1 ≤ 1 / s` holds exactly when `0 < s ≤ 1`; here `s = √(1 - β ^ 2)`.
H2. Get `h1 : 0 < 1 - β ^ 2` from `abs_lt.mp hβ` with `nlinarith`; the square root of a number in
    `(0, 1]` lies in `(0, 1]`.
H3. `rw [boost_inl_0_inl_0]; unfold γ`, then the key step is `rw [one_le_div (Real.sqrt_pos.mpr h1)]`.
-/
