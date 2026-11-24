/- H100 | The tight-binding spectrum is the band | 1.5-2 h | orthogonality, linear independence, dimension count, span induction, physlib
GOAL
  Every eigenvalue `E` of the tight-binding Hamiltonian `H` (`H ψ = E ψ`, `ψ ≠ 0`) is a band energy
  `E(k) = E0 - 2t cos (k a)` for some allowed `k`: the `N` Bloch states `ψ_k` are orthogonal, hence
  span the `N`-dimensional Hilbert space, so nothing else can be in the spectrum.

GUIDE
  Entries R1–R54: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace H100

/- SKELETON · bloch_norm_sq   (milestone 1: ⟪ψ_k, ψ_k⟫ = N; used in span_top to get ψ_k ≠ 0)
  1. One `simp only`: unfold ψ_k, pull both sums out of the inner product, pull both
     scalars out, turn each site overlap ⟨m|n⟩ into `if m = n then 1 else 0`:     R1, R2, R3, R4, R5, R6
  2. One `simp`, naming `← Complex.exp_conj`, `← Complex.exp_add`, `Complex.conj_ofReal`:
     collapse the delta sum, conj into exp, merge, exp 0 = 1, count the N ones:   R7, R8, R10, R9, R11, R12, R13
-/
-- MILESTONE (optional: change or delete)
theorem bloch_norm_sq (T : TightBindingChain) (k : T.QuantaWaveNumber) :
    ⟪T.energyEigenstate k, T.energyEigenstate k⟫_ℂ = T.N := by
  sorry

/- SKELETON · card_wavenumbers   (milestone 2: |K| = N; used twice in span_top)
  1. hset : T.QuantaWaveNumber = Set.range (fun n : Fin T.N =>
              2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)))             R14, then R15 with R16 (one simp)
  2. rw [hset], then count the range; the side goal `Function.Injective _` stays:  R17 → R18 → R19
  3. Injectivity: open it                                                         R20
       hc : 2 * Real.pi / (T.a * T.N) ≠ 0       from R21 (both facts), R22, then R23
       cancel the factor, then the shift, then compare values in ℕ:              R24, R25, R26 (with R22)
-/
-- MILESTONE (optional: change or delete)
theorem card_wavenumbers (T : TightBindingChain) : T.QuantaWaveNumber.ncard = T.N := by
  sorry

/- SKELETON · span_top   (milestone 3: the Bloch states span; uses milestones 1, 2; used in spectrum_eq_band)
  1. hfin : T.QuantaWaveNumber.Finite       from 0 < ncard: R27 with rw [milestone 2] and R21
  2. The instance `Fintype T.QuantaWaveNumber`:                                     R28
  3. Reduce to independence + counting (two goals, use bullets):                    R29
  4. lin_ind: orthogonal and nonzero ⇒ independent                                  R30 with R31
       ∀ k, ψ_k ≠ 0: R32, h := milestone 1 at k, R33 (`rw [hk, …] at h`), then R34 → R35
  5. card_eq: one rw                                                                R37 with R36, R19, R18 (right to left), R38, milestone 2
-/
-- MILESTONE (optional: change or delete)
theorem span_top (T : TightBindingChain) :
    Submodule.span ℂ (Set.range T.energyEigenstate) = ⊤ := by
  sorry

/- SKELETON · orth_of_ne   (milestone 4: ψ ⊥ ψ_k when E ≠ E(k); used in spectrum_eq_band, case `mem`)
  1. h := hermiticity at ψ_k and ψ:                                                 R39
  2. One `rw [...] at h`: H ψ_k, then hE, then the scalars (real → complex first):
       h : ↑E(k) * ⟪ψ_k, ψ⟫_ℂ = E * ⟪ψ_k, ψ⟫_ℂ                                    R40, rw [hE], R5, R41, R4, R9
  3. h' : (E - ↑E(k)) * ⟪ψ_k, ψ⟫_ℂ = 0                                             R42, rw [h], R43
  4. Cancel the nonzero factor:                                                     R44 → R45 with R46
-/
-- MILESTONE (optional: change or delete)
theorem orth_of_ne (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace)
    (hE : T.hamiltonian ψ = E • ψ) (k : T.QuantaWaveNumber) (hk : E ≠ T.energyEigenvalue k) :
    ⟪T.energyEigenstate k, ψ⟫_ℂ = 0 := by
  sorry

/- SKELETON · spectrum_eq_band
  Prove the four milestones first: milestone 3 (built on 1 and 2) and milestone 4 are used here.
  1. Contradiction; hne : ∀ k, E ≠ ↑E(k):                                           R47, R48
  2. key : ∀ φ ∈ Submodule.span ℂ (Set.range T.energyEigenstate), ⟪φ, ψ⟫_ℂ = 0
       intro φ hφ, then span induction with named cases:                            R49
       mem:  R50, then milestone 4 with hE and hne k
       zero: simp                                                                   (R33)
       add:  R51, rw [hx, hy], R52
       smul: R4, rw [hx], R52
  3. hmem : ψ ∈ Submodule.span ℂ (Set.range T.energyEigenstate):  rw [milestone 3], R53
  4. ψ = 0 from key ψ hmem, against hψ:                                              R54, R35
-/
-- BEGIN SPEC
theorem spectrum_eq_band (T : TightBindingChain) (E : ℂ) (ψ : T.HilbertSpace) (hψ : ψ ≠ 0)
    (hE : T.hamiltonian ψ = E • ψ) : ∃ k : T.QuantaWaveNumber, E = T.energyEigenvalue k :=
-- END SPEC
  sorry

end H100

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Argue by contradiction (R47, R48): if `E ≠ E(k)` for every `k`, hermiticity makes `ψ` orthogonal
    to every Bloch state (milestone 4). The Bloch states span everything (milestone 3), so `ψ` is
    orthogonal to itself, hence `ψ = 0`.
H2. `orth_of_ne`: rewrite both sides of `⟪H ψ_k, ψ⟫ = ⟪ψ_k, H ψ⟫` to `E(k) ⟪ψ_k, ψ⟫ = E ⟪ψ_k, ψ⟫`; the
    real scalar `E(k) • ψ_k` must become `(E(k) : ℂ) • ψ_k` (`rfl`, R41) before `inner_smul_left`.
    `span_top`: `apply LinearIndependent.span_eq_top_of_card_eq_finrank'`; independence from
    `linearIndependent_of_ne_zero_of_inner_eq_zero _ T.energyEigenstate_orthogonal` and
    `bloch_norm_sq` (`N ≠ 0`); `card_wavenumbers` for the count. `QuantaWaveNumber` is a `Set ℝ`:
    get `Fintype` from `Set.finite_of_ncard_pos` and `hfin.fintype` (R27, R28).
    Main: `induction hφ using Submodule.span_induction` on `⟪φ, ψ⟫_ℂ = 0`.
H3. Count: `rw [Module.finrank_eq_card_basis (localizedState (T := T)).toBasis, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, card_wavenumbers]`. Main: `by_contra hne;
    push Not at hne`, prove `∀ φ ∈ Submodule.span ℂ (Set.range T.energyEigenstate), ⟪φ, ψ⟫_ℂ = 0` by
    `induction hφ using Submodule.span_induction with | mem x hx => … | zero => … | add x y _ _ hx hy
    => … | smul c x _ hx => …`, apply it to `ψ` (`span_top`), then `inner_self_eq_zero`.
-/
