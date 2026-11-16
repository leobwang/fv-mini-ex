/- M171 | Translation symmetry and Bloch's theorem | 15-20 min | linear maps, basis ext, sum reindexing, physlib
GOAL
  `translation T` shifts the chain by one site, `|n⟩ ↦ |n + 1⟩`. Show it commutes with `T.hamiltonian`
  and that each eigenstate `ψ_k` is a translation eigenvector with eigenvalue `exp (-i k a)` (Bloch).
  Suggested first step: the helper `translation T (localizedState p) = localizedState (p + 1)`.

REFERENCE
  #check TightBindingChain.localizedComp_apply_localizedState  -- |m⟩⟨n| |p⟩ = if n = p then |m⟩ else 0
  #check TightBindingChain.hamiltonian_apply_localizedState    -- H |n⟩ = E0 • |n⟩ - t • (|n + 1⟩ + |n - 1⟩)
  #check Module.Basis.ext  -- (∀ i, f₁ (b i) = f₂ (b i)) → f₁ = f₂  (linear maps agreeing on a basis)
  #check OrthonormalBasis.coe_toBasis  -- ⇑b.toBasis = ⇑b ; use `(localizedState (T := T)).toBasis.ext`
  #check TightBindingChain.quantaWaveNumber_exp_sub_one  -- exp (I k (n-1) a) = exp (I k n a) * exp (-I k a)
  #check Equiv.sum_comp    -- ∑ i, g (e i) = ∑ i, g i   (reindex a sum by a bijection e)
  #check Equiv.subRight    -- Equiv.subRight c : x ↦ x - c, a bijection of `Fin T.N`
  #check map_sum           -- g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x)  (also `map_smul`, `map_sub`, `map_add`)
  #check Finset.smul_sum   -- r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x   (and `smul_smul`)
NOTE: `n + 1 : Fin T.N` wraps around mod `N` (periodic chain); `f ∘ₗ g` composes linear maps.
  `|n⟩` is `localizedState n`; `|m⟩⟨n|` is `localizedComp m n : ψ ↦ ⟪|n⟩, ψ⟫ • |m⟩`.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain

namespace M171

-- BEGIN SPEC
/-- Translation by one lattice site: `|n⟩ ↦ |n + 1⟩` (indices mod `N`). -/
noncomputable def translation (T : TightBindingChain) : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace :=
  ∑ n : Fin T.N, localizedComp (n + 1) n
-- END SPEC

-- BEGIN SPEC
theorem hamiltonian_comm (T : TightBindingChain) :
    T.hamiltonian ∘ₗ translation T = translation T ∘ₗ T.hamiltonian :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem bloch_theorem (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    translation T (T.energyEigenstate k) =
      Complex.exp (-Complex.I * k * T.a) • T.energyEigenstate k :=
-- END SPEC
  sorry

end M171

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove a helper first: `translation T (localizedState p) = localizedState (p + 1)`
    (unfold `translation`, apply the sum of maps, and collapse the `if`s).
H2. Commutation: check it on the basis `|m⟩` (`Module.Basis.ext`); both sides become
    `E0 • |m + 1⟩ - t • (|m + 2⟩ + |m⟩)`. Bloch: push `translation` inside the sum, reindex
    `n ↦ n - 1` so the sum is over `|n⟩` again, and use `quantaWaveNumber_exp_sub_one` termwise.
H3. `apply (localizedState (T := T)).toBasis.ext; intro m; simp only [OrthonormalBasis.coe_toBasis,
    LinearMap.comp_apply, translation_apply, hamiltonian_apply_localizedState, map_sub, map_smul, map_add]`
    (`translation_apply` = your H1 helper);
    Bloch: `rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]` after `simp only [map_sum, map_smul, ...]`.
-/
