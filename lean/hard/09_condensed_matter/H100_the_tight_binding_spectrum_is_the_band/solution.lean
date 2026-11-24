/- H100 | The tight-binding spectrum is the band | 1.5-2 h | orthogonality, linear independence, dimension count, span induction, physlib
GOAL
  Every eigenvalue `E` of the tight-binding Hamiltonian `H` (`H ψ = E ψ`, `ψ ≠ 0`) is a band energy
  `E(k) = E0 - 2t cos (k a)` for some allowed `k`: the `N` Bloch states `ψ_k` are orthogonal, hence
  span the `N`-dimensional Hilbert space, so nothing else can be in the spectrum.

REFERENCE
  #check TightBindingChain.hamiltonian_energyEigenstate  -- H ψ_k = E(k) • ψ_k   (`(r : ℝ) • v = (r : ℂ) • v` is `rfl`)
  #check TightBindingChain.hamiltonian_hermitian  -- ⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ
  #check TightBindingChain.energyEigenstate_orthogonal  -- Pairwise fun k₁ k₂ => ⟪ψ_k₁, ψ_k₂⟫_ℂ = 0
  #check inner_smul_left   -- ⟪r • x, y⟫ = conj r * ⟪x, y⟫   (`inner_smul_right`, `Complex.conj_ofReal`)
  #check linearIndependent_of_ne_zero_of_inner_eq_zero  -- (∀ i, v i ≠ 0) → Pairwise (⟪v i, v j⟫ = 0) → LinearIndependent 𝕜 v
  #check LinearIndependent.span_eq_top_of_card_eq_finrank'  -- [Fintype ι] LinearIndependent K b → card ι = finrank K V → span (range b) = ⊤
  #check Module.finrank_eq_card_basis  -- (b : Module.Basis ι R M) : finrank R M = Fintype.card ι  (`|n⟩ = localizedState n` is a basis: `localizedState.toBasis`)
  #check Set.Finite.fintype  -- s.Finite → Fintype s   (`haveI : Fintype T.QuantaWaveNumber := hfin.fintype`)
  #check Nat.card_coe_set_eq -- Nat.card s = s.ncard   (and `Nat.card_eq_fintype_card`, `Fintype.card_fin`)
  #check Submodule.span_induction  -- `induction h using Submodule.span_induction`: generators, `0`, `+`, `•`
  #check inner_self_eq_zero  -- ⟪x, x⟫ = 0 ↔ x = 0
NOTE: `ψ_k` = `T.energyEigenstate k`; `E(k)` = `T.energyEigenvalue k : ℝ` (cast to ℂ); `⟪x, y⟫_ℂ` = inner product, conj-linear in `x`.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace H100

-- MILESTONE (optional: change or delete)
theorem bloch_norm_sq (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    ⟪T.energyEigenstate k, T.energyEigenstate k⟫_ℂ = T.N := by
  simp only [TightBindingChain.energyEigenstate, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, localizedState_orthonormal_eq_ite]
  simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]

-- MILESTONE (optional: change or delete)
theorem card_wavenumbers (T : TightBindingChain) : T.QuantaWaveNumber.ncard = T.N := by
  have hset : T.QuantaWaveNumber = Set.range (fun n : Fin T.N =>
      2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ))) := by
    ext x; simp [TightBindingChain.QuantaWaveNumber]
  rw [hset, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro m n h
  have hc : 2 * Real.pi / (T.a * T.N) ≠ 0 := by
    have := T.a_pos
    have : (0 : ℝ) < T.N := by exact_mod_cast NeZero.pos T.N
    positivity
  exact Fin.ext (by exact_mod_cast sub_left_inj.mp (mul_left_cancel₀ hc h))

-- MILESTONE (optional: change or delete)
theorem span_top (T : TightBindingChain) :
    Submodule.span ℂ (Set.range T.energyEigenstate) = ⊤ := by
  -- WHY: `QuantaWaveNumber` is a `Set ℝ`; the dimension count needs a `Fintype` on its subtype
  have hfin : T.QuantaWaveNumber.Finite := Set.finite_of_ncard_pos (by
    rw [card_wavenumbers]; exact NeZero.pos T.N)
  haveI : Fintype T.QuantaWaveNumber := hfin.fintype
  apply LinearIndependent.span_eq_top_of_card_eq_finrank'
  · apply linearIndependent_of_ne_zero_of_inner_eq_zero _ T.energyEigenstate_orthogonal
    intro k hk
    have h := bloch_norm_sq T k
    rw [hk, inner_zero_left] at h
    exact (show (T.N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne T.N) h.symm
  · rw [Module.finrank_eq_card_basis (localizedState (T := T)).toBasis, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, card_wavenumbers]

-- MILESTONE (optional: change or delete)
theorem orth_of_ne (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace)
    (hE : T.hamiltonian ψ = E • ψ) (k : T.QuantaWaveNumber) (hk : E ≠ T.energyEigenvalue k) :
    ⟪T.energyEigenstate k, ψ⟫_ℂ = 0 := by
  have h := T.hamiltonian_hermitian (T.energyEigenstate k) ψ
  rw [hamiltonian_energyEigenstate, hE, inner_smul_right,
    show T.energyEigenvalue k • T.energyEigenstate k =
      (T.energyEigenvalue k : ℂ) • T.energyEigenstate k from rfl,
    inner_smul_left, Complex.conj_ofReal] at h
  have h' : (E - T.energyEigenvalue k) * ⟪T.energyEigenstate k, ψ⟫_ℂ = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hk)

-- BEGIN SPEC
theorem spectrum_eq_band (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace) (hψ : ψ ≠ 0)
    (hE : T.hamiltonian ψ = E • ψ) : ∃ k : T.QuantaWaveNumber, E = T.energyEigenvalue k :=
-- END SPEC
  by
    by_contra hne
    push Not at hne
    -- ψ is orthogonal to every Bloch state, hence to their span, which is everything
    have key : ∀ φ ∈ Submodule.span ℂ (Set.range T.energyEigenstate), ⟪φ, ψ⟫_ℂ = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact orth_of_ne T E ψ hE k (hne k)
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
    have hmem : ψ ∈ Submodule.span ℂ (Set.range T.energyEigenstate) := by
      rw [span_top]; trivial
    exact hψ (inner_self_eq_zero.mp (key ψ hmem))

end H100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Argue by contradiction: if `E ≠ E(k)` for every `k`, hermiticity makes `ψ` orthogonal to every
    Bloch state. If the Bloch states span everything, `ψ` is orthogonal to itself, so `ψ = 0`.
H2. `orth_of_ne`: expand both sides of `⟪H ψ_k, ψ⟫ = ⟪ψ_k, H ψ⟫` to get `E(k) ⟪ψ_k, ψ⟫ = E ⟪ψ_k, ψ⟫`.
    `span_top`: the Bloch states are nonzero (`bloch_norm_sq`, this is M168) and pairwise orthogonal,
    so linearly independent; there are `N` of them (`card_wavenumbers`, M170) and `finrank = N`.
    `QuantaWaveNumber` is a `Set ℝ`: get `Fintype` from `T.QuantaWaveNumber.Finite`
    (a range is finite; or use `Set.finite_of_ncard_pos`).
H3. Count: `rw [Module.finrank_eq_card_basis (localizedState (T := T)).toBasis, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, card_wavenumbers]`. Main: `by_contra hne;
    push Not at hne`, prove `∀ φ ∈ Submodule.span ℂ (Set.range T.energyEigenstate), ⟪φ, ψ⟫_ℂ = 0` by
    `induction hφ using Submodule.span_induction`, apply it to `ψ` (`span_top`), then `inner_self_eq_zero`.
-/
