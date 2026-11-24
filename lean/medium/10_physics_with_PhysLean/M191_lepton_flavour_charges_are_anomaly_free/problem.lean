/- M191 | Lepton-flavour charges are anomaly free | 10-15 min | ACCSystem, Sols, decomp lemmas, Finset sums, simp only, physlib
GOAL
  With `n` families, give family `f` the charge `x f` on the lepton doublet `L` and `−x f` on `E`, `N` (quarks 0).
  If `∑ f, x f = 0`, this satisfies all six anomaly equations of `PlusU1 n`. (`L_e − L_μ` is `n = 2`, `x = ![1, -1]`.)
  physlib stores `E`, `N` as left-handed conjugate fields, so their charges carry the opposite sign.

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic

open SMRHN SMνCharges SMνACCs

namespace M191

-- BEGIN SPEC
/-- Lepton-flavour charge: `x f` on `L`, `−x f` on `E` and `N` in family `f`; quarks uncharged. -/
def leptonFlavour {n : ℕ} (x : Fin n → ℚ) : (PlusU1 n).Charges :=
  toSpeciesEquiv.symm fun s f => ![0, 0, 0, 1, -1, -1] s * x f
-- END SPEC

/- SKELETON · leptonFlavour_isSolution
  1. Retype `hx` BEFORE splitting, so all six goals get it:                 R1
       hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0
  2. `IsSolution` → a `Sols` built by `PlusU1.chargeToAF`, its `.val` by `rfl`: R2, R3
     This leaves six goals, in order Grav, SU2, SU3, YY, Quad, Cube; focus each with `·`.
  3. In each goal:
       expand the ACC into per-species sums                                 R4 / R5 / R6 / R7 / R8 / R9
       read off the species charges of `leptonFlavour x`, in ONE
       `simp only` and before any plain `simp`                              R10 → R11
  4. Finish each goal:
       Grav, SU2, YY: `simp` with `hx'` (simp does R12 → R13 → R14 → R15)   simp [hx']
       SU3 (no leptons) and Quad (cancels family by family)                 simp  (R12–R16)
       Cube: `simp` with R17 (R12–R15 automatic), then `ring` for the leftover
             identity `2 * s + -s + -s = 0` in the atom `s = ∑ f, x f ^ 3`        R17, ring
-/
-- BEGIN SPEC
theorem leptonFlavour_isSolution (n : ℕ) (x : Fin n → ℚ) (hx : ∑ f, x f = 0) :
    (PlusU1 n).IsSolution (leptonFlavour x) :=
-- END SPEC
  sorry

end M191

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `IsSolution` asks for a `(PlusU1 n).Sols` whose `.val` is `leptonFlavour x`; `PlusU1.chargeToAF` builds
    one from six ACC proofs. In each, expand the ACC into per-species sums, then read off the species
    charges. `hx` sums over the wrong index type for those sums: retype it first (R1).
H2. `have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx`. Per goal: `rw [accGrav_decomp]`
    (etc.), then `simp only [leptonFlavour, toSMSpecies_toSpecies_inv]` before any plain `simp` (plain `simp`
    unfolds `toSpecies` first, and the inverse lemma no longer matches). Grav, SU(2), YY reduce to
    multiples of `∑ x`; SU(3) has no leptons; quad and cubic cancel family by family.
H3. `refine ⟨PlusU1.chargeToAF (leptonFlavour x) ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩`; finish the linear goals with
    `simp [hx']`, SU(3) and the quadratic with `simp`; the cubic with
    `simp [Odd.neg_pow (by decide : Odd 3), Finset.sum_neg_distrib]`, then `ring`.
-/
