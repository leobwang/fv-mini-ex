/- M171 | Translation symmetry and Bloch's theorem | 15-20 min | linear maps, basis ext, sum reindexing, physlib
GOAL
  `translation T` shifts the chain by one site, `|n⟩ ↦ |n + 1⟩`. Show it commutes with `T.hamiltonian`
  and that each eigenstate `ψ_k` is a translation eigenvector with eigenvalue `exp (-i k a)` (Bloch).
  Suggested first step: the helper `translation T (localizedState p) = localizedState (p + 1)`.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain

namespace M171

-- BEGIN SPEC
/-- Translation by one lattice site: `|n⟩ ↦ |n + 1⟩` (indices mod `N`). -/
noncomputable def translation (T : TightBindingChain) : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  ∑ n : Fin T.N, localizedComp (n + 1) n
-- END SPEC

theorem translation_apply (T : TightBindingChain) (p : Fin T.N) :
    translation T (localizedState p) = localizedState (p + 1) := by
  simp [translation, localizedComp_apply_localizedState]

/- SKELETON · hamiltonian_comm
  0. MILESTONE first, above this theorem (not a spec: state and prove it yourself):
       translation_apply (T) (p : Fin T.N) :
         translation T (localizedState p) = localizedState (p + 1)
     proof: unfold `translation`, then                                    R1 → R2 → R3 → R4
     It is used in step 2 here and in step 1 of `bloch_theorem`.
  1. Two linear maps are equal if they agree on the basis |m⟩:           R5, then `intro m`
  2. One `simp only [...]`, with the lemmas for
       `b.toBasis m` → `|m⟩`,  `(f ∘ₗ g) x` → `f (g x)`                  R6, R7
       `H |n⟩` → `E0 • |n⟩ - t • (|n + 1⟩ + |n - 1⟩)`                    R8
       push `translation T` through `-`, `•`, `+`                         R9, R11, R10
       `translation T |p⟩` → `|p + 1⟩`                                    translation_apply
       right side's `|m - 1 + 1⟩` → `|m⟩` (put it in the same simp set)   R20
     Both sides now agree except `|m + 1 - 1⟩` (left) against `|m⟩` (right).
     Without R20 the right side keeps `|m - 1 + 1⟩` and step 3 does not close the goal.
  3. `m + 1 - 1 = m` in `Fin T.N` (R20 does not match this shape):        R12
-/
-- BEGIN SPEC
theorem hamiltonian_comm (T : TightBindingChain) :
    T.hamiltonian ∘ₗ translation T = translation T ∘ₗ T.hamiltonian :=
-- END SPEC
  by
    apply (localizedState (T := T)).toBasis.ext
    intro m
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, translation_apply,
      hamiltonian_apply_localizedState, map_sub, map_smul, map_add, sub_add_cancel]
    -- WHY: the left side has `|m + 1 - 1⟩`, the right side `|m⟩`; `Fin T.N` arithmetic is mod N.
    rw [add_sub_cancel_right]

/- SKELETON · bloch_theorem
  1. One `simp only [...]`, with the lemmas for
       unfold `ψ_k = ∑ n, exp (I k n a) • |n⟩` on both sides              R13
       push `translation T` into the sum and past the scalar              R14, R11
       `translation T |n⟩` → `|n + 1⟩`                                    translation_apply (milestone)
       right side: the scalar into the sum, two scalars merged            R15, R16
     Goal: ∑ x, e^{ikxa} • |x + 1⟩ = ∑ x, (e^{-ika} * e^{ikxa}) • |x⟩.
  2. Reindex the left sum by n ↦ n - 1, `c = (1 : Fin T.N)`:              R17
  3. Compare the two sums term by term:                                   R18
  4. `(Equiv.subRight 1) n` → `n - 1`, then `n - 1 + 1` → `n`:            R19, R20
  5. Same vector `|n⟩` on both sides; compare the scalars:                R21
  6. Split `exp (I k (n - 1) a)`, then commute the product:               R22, then `ring`
-/
-- BEGIN SPEC
theorem bloch_theorem (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    translation T (T.energyEigenstate k) =
      Complex.exp (-Complex.I * k * T.a) • T.energyEigenstate k :=
-- END SPEC
  by
    simp only [TightBindingChain.energyEigenstate, map_sum, map_smul, translation_apply,
      Finset.smul_sum, smul_smul]
    -- reindex `n ↦ n - 1` so both sums run over `|n⟩`
    rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel]
    congr 1
    rw [quantaWaveNumber_exp_sub_one]
    ring

end M171

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems reduce to one fact about basis vectors: prove the helper
    `translation T (localizedState p) = localizedState (p + 1)` first (SKELETON step 0).
    For an equation of linear maps, check it on the basis `|m⟩`; for Bloch, write `ψ_k` as its sum
    and compare coefficients.
H2. Commutation: after basis ext and `simp only`, both sides are `E0 • |m + 1⟩ - t • (|m + 2⟩ + |m⟩)`
    except for the index arithmetic (mod N): the left has `|m + 1 - 1⟩`, the right `|m - 1 + 1⟩`.
    `sub_add_cancel` fixes the right one, `add_sub_cancel_right` the left one. Bloch: push `translation` into the sum,
    reindex `n ↦ n - 1` so both sums run over `|n⟩`, then compare termwise with
    `quantaWaveNumber_exp_sub_one`.
H3. Helper: `simp [translation, localizedComp_apply_localizedState]`.
    Commutation: `apply (localizedState (T := T)).toBasis.ext; intro m; simp only [OrthonormalBasis.coe_toBasis,
    LinearMap.comp_apply, translation_apply, hamiltonian_apply_localizedState, map_sub, map_smul, map_add,
    sub_add_cancel]`, then `rw [add_sub_cancel_right]`.
    Bloch: `simp only [TightBindingChain.energyEigenstate, map_sum, map_smul, translation_apply,
    Finset.smul_sum, smul_smul]`, then `rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]` and
    `refine Finset.sum_congr rfl fun n _ => ?_`.
-/
