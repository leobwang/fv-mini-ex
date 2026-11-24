/- M191 | Lepton-flavour charges are anomaly free | 10-15 min | ACCSystem, Sols, decomp lemmas, Finset sums, simp only, physlib
GOAL
  With `n` families, give family `f` the charge `x f` on the lepton doublet `L` and `−x f` on `E`, `N` (quarks 0).
  If `∑ f, x f = 0`, this satisfies all six anomaly equations of `PlusU1 n`. (`L_e − L_μ` is `n = 2`, `x = ![1, -1]`.)
  physlib stores `E`, `N` as left-handed conjugate fields, so their charges carry the opposite sign.

REFERENCE
  `(PlusU1 n).IsSolution S` means `∃ sol : (PlusU1 n).Sols, sol.val = S`; species `Q, U, D, L, E, N` = `Fin 6` 0..5.
  `toSpeciesEquiv.symm g : (PlusU1 n).Charges` is the charge vector with value `g j f` for species `j`, family `f`.
  #check PlusU1.chargeToAF -- (S) → accGrav S = 0 → accSU2 S = 0 → accSU3 S = 0 → accYY S = 0 → accQuad S = 0
                           --   → accCube S = 0 → (PlusU1 n).Sols    (the result's `.val` is `S` by `rfl`)
  #check accCube_decomp    -- accCube S = 6 * ∑ i, (Q S i)^3 + ... + ∑ i, (N S i)^3   (`Q = toSpecies 0`, ...)
                           --   likewise `accGrav_decomp`, `accSU2_decomp`, `accSU3_decomp`, `accYY_decomp`, `accQuad_decomp`
  #check toSMSpecies_toSpecies_inv -- toSpecies j (toSpeciesEquiv.symm g) = g j
  #check Finset.sum_neg_distrib    -- ∑ i ∈ s, -f i = -∑ i ∈ s, f i
  #check Odd.neg_pow                -- Odd n → (-a) ^ n = -a ^ n     (`(by decide : Odd 3)` proves `Odd 3`)
NOTE: the decomp sums run over `Fin (SMνSpecies n).numberCharges`, equal to `Fin n` only after unfolding, so
  `hx` does not rewrite them; `have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx` does.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMRHN SMνCharges SMνACCs

namespace M191

-- BEGIN SPEC
/-- Lepton-flavour charge: `x f` on `L`, `−x f` on `E` and `N` in family `f`; quarks uncharged. -/
def leptonFlavour {n : ℕ} (x : Fin n → ℚ) : (PlusU1 n).Charges :=
  toSpeciesEquiv.symm fun s f => ![0, 0, 0, 1, -1, -1] s * x f
-- END SPEC

-- BEGIN SPEC
theorem leptonFlavour_isSolution (n : ℕ) (x : Fin n → ℚ) (hx : ∑ f, x f = 0) :
    (PlusU1 n).IsSolution (leptonFlavour x) :=
-- END SPEC
  by
    -- WHY: `hx` sums over `Fin n`; the decomp lemmas sum over `Fin (SMνSpecies n).numberCharges`.
    have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx
    refine ⟨PlusU1.chargeToAF (leptonFlavour x) ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
    · rw [accGrav_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp [hx']
    · rw [accSU2_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp [hx']
    · rw [accSU3_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp
    · rw [accYY_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp [hx']
    · rw [accQuad_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp
    · rw [accCube_decomp]
      simp only [leptonFlavour, toSMSpecies_toSpecies_inv]
      simp [Odd.neg_pow (by decide : Odd 3), Finset.sum_neg_distrib]
      ring

end M191

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Build the `Sols` with `PlusU1.chargeToAF`: that leaves six goals, one anomaly each. In each one, expand
    the anomaly into per-species sums, then read off the species charges of `leptonFlavour x`.
H2. Per goal: `rw [accGrav_decomp]` (etc.), then `simp only [leptonFlavour, toSMSpecies_toSpecies_inv]`
    before any plain `simp` (plain `simp` unfolds `toSpecies` first, and the inverse lemma no longer matches).
    Grav, SU(2), YY reduce to multiples of `∑ x`; SU(3) has no leptons; quad and cubic cancel family by family.
H3. `refine ⟨PlusU1.chargeToAF (leptonFlavour x) ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩`; finish the linear goals with
    `simp [hx']`, the quadratic with `simp`; for the cubic, `simp` plus `Odd.neg_pow` and `sum_neg_distrib`, then `ring`.
-/
