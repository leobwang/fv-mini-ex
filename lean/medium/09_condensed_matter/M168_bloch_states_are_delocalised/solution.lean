/- M168 | Bloch states are delocalised | 10-15 min | inner products, orthonormal basis, Complex.norm_exp, physlib
GOAL
  In the tight-binding chain (`N` sites `|n⟩`, spacing `a`), the energy eigenstate
  `ψ_k = ∑ n, exp (i k n a) • |n⟩` has amplitude of modulus 1 on every site, `‖⟨n|ψ_k⟩‖ = 1`,
  and squared norm `⟨ψ_k|ψ_k⟩ = N`. So the electron sits on each site with probability `1/N`.

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace M168

/- SKELETON · bloch_delocalized
  1. Unfold ψ_k, push `⟪|n⟩, ·⟫` through the sum and the scalars, apply orthonormality.
     Under the `∑` use `simp only`, not `rw` (one call with all four):    R1, R2, R3, R4
       the goal becomes  ‖∑ x, (phase at x) * (if n = x then 1 else 0)‖ = 1
  2. Collapse the sum to its `x = n` term:                                 R5, R6, R7, R9
  3. The modulus of a phase is 1:  ‖exp z‖ = Real.exp z.re,  z.re = 0,  Real.exp 0 = 1
                                                                           R10 → R11, R12 → R13
     (`simp` does all of step 3 once it is given R10.)
-/
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

/- SKELETON · bloch_norm_sq
  1. Unfold ψ_k in both slots and expand: sums out (left R14, right R2), scalars out (left R15,
     which conjugates; right R3), orthonormality (R4). One `simp only` with all of them:
                                                                           R1, R14, R2, R15, R3, R4
       the goal becomes a double sum over sites of phases times (if … then 1 else 0)
  2. Collapse the inner sum: R5, R6, then R7 or R8 (check which side of `=` the inner summation
     variable sits; with everything in one `simp only` it is R8, see W3), then R9.
       each term is now  exp z * conj (exp z)  (or the reverse)  with  z = I * k * n * a
  3. Turn each term into 1:  conj (exp z) → exp (conj z) → exp (-z), merge, cancel:
                                                       R16, R17 → R18 → R19 → R20, R21, R22 → R23
  4. Count the ones: ∑ over `Fin T.N` of 1 is ↑T.N:                        R24, R6
  Steps 2–4 can be a single `simp` call: it knows every lemma there except the two used right to
  left (R16, R21), which you must hand it with `←`.
-/
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
H1. Both goals are inner products of sums of scaled site states. Unfold `energyEigenstate`, push the
    inner product through the sums and the scalars (R2, R3; R14, R15 for the left slot), and let
    orthonormality (R4) turn every `⟪|n⟩, |m⟩⟫` into an `if`. Use `simp only`: `rw` cannot reach
    under the `∑`.
H2. `bloch_delocalized`: only the `m = n` term survives (R5–R9), leaving `‖exp (I * k * n * a)‖`,
    which is `Real.exp` of a real part that is 0 because the exponent is purely imaginary (R10–R13).
    `bloch_norm_sq`: the inner sum collapses to `exp z * conj (exp z)`, which is
    `exp (z + conj z) = exp 0 = 1` because `conj z = -z` (R16–R23); then `∑ n, 1 = N` (R24).
H3. First step: `simp only [TightBindingChain.energyEigenstate, inner_sum, inner_smul_right,
    localizedState_orthonormal_eq_ite]` (add `sum_inner, inner_smul_left` for the norm). Then finish
    `bloch_delocalized` with `simp` given `Complex.norm_exp`, and `bloch_norm_sq` with `simp` given the
    two right-to-left lemmas `← Complex.exp_conj, ← Complex.exp_add`.
-/
