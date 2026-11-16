/- M168 | Bloch states are delocalised | 10-15 min | inner products, orthonormal basis, Complex.norm_exp, physlib
GOAL
  In the tight-binding chain (`N` sites `|n⟩`, spacing `a`), the energy eigenstate
  `ψ_k = ∑ n, exp (i k n a) • |n⟩` has amplitude of modulus 1 on every site, `‖⟨n|ψ_k⟩‖ = 1`,
  and squared norm `⟨ψ_k|ψ_k⟩ = N`. So the electron sits on each site with probability `1/N`.

REFERENCE
  #check TightBindingChain.energyEigenstate  -- T.energyEigenstate k = ∑ n, exp (I * k * n * T.a) • |n⟩
  #check TightBindingChain.localizedState_orthonormal_eq_ite  -- ⟪|m⟩, |n⟩⟫_ℂ = if m = n then 1 else 0
  #check inner_sum         -- ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫   (`sum_inner`: sum on the left)
  #check inner_smul_right  -- ⟪x, r • y⟫ = r * ⟪x, y⟫
  #check inner_smul_left   -- ⟪r • x, y⟫ = conj r * ⟪x, y⟫   (`conj` is `starRingEnd ℂ`)
  #check Finset.sum_ite_eq -- ∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0
  #check Complex.norm_exp  -- ‖exp z‖ = Real.exp z.re
  #check Complex.exp_conj  -- exp (conj z) = conj (exp z)
NOTE: `⟪x, y⟫_ℂ` is the inner product (conjugate-linear in `x`); `|n⟩` is `localizedState n`;
  `k : T.QuantaWaveNumber` is a subtype element, `(k : ℝ)` its value; `I` is `Complex.I`.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M168

-- BEGIN SPEC
theorem bloch_delocalized (T : TightBindingChain) (k : T.QuantaWaveNumber) (n : Fin T.N) :
    ‖⟪localizedState n, T.energyEigenstate k⟫_ℂ‖ = 1 :=
-- END SPEC
  by
    simp only [TightBindingChain.energyEigenstate, inner_sum, inner_smul_right,
      localizedState_orthonormal_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    -- WHY: `I * k * n * a` is purely imaginary, so its real part is 0 and `‖exp _‖ = exp 0 = 1`.
    simp [Complex.norm_exp]

-- BEGIN SPEC
theorem bloch_norm_sq (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    ⟪T.energyEigenstate k, T.energyEigenstate k⟫_ℂ = T.N :=
-- END SPEC
  by
    simp only [TightBindingChain.energyEigenstate, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, localizedState_orthonormal_eq_ite]
    simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]

end M168

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `energyEigenstate`, push the inner product through the sum and the scalars, and let
    orthonormality turn every `⟪|n⟩, |m⟩⟫` into an `if`.
H2. `bloch_delocalized`: only the `m = n` term survives, leaving `‖exp (I * k * n * a)‖`; the exponent
    is purely imaginary. `bloch_norm_sq`: the double sum collapses to `∑ n, conj (exp z) * exp z`,
    and `conj (exp z) * exp z = exp (conj z + z) = exp 0` because `conj z = -z` for imaginary `z`.
H3. First step: `simp only [TightBindingChain.energyEigenstate, inner_sum, inner_smul_right,
    localizedState_orthonormal_eq_ite]` (add `sum_inner, inner_smul_left` for the norm). To finish
    `bloch_delocalized`, use that the real part of `I * k * n * a` is 0; for `bloch_norm_sq`, rewrite
    `conj (exp z) * exp z` as `exp (conj z + z)` and simplify the exponent.
-/
