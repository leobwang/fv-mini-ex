/- M157 | N independent spins | 5-10 min | nsmul, partitionFunction_nsmul, helmholtzFreeEnergy, physlib
GOAL
  `nsmul N 𝓒` is `N` distinguishable, non-interacting copies of `𝓒`. For `N` spins in a field `h`, each
  the two-level system `twoState (-h) h` (energies `-h`, `+h`), show `Z = (2 cosh (β h))^N` and
  `F = -N kB T log (2 cosh (β h))`, where `β = 1 / (kB T)`.

BANNED: helmholtzFreeEnergy_nsmul, twoState_partitionFunction_apply_eq_cosh, twoState_helmholtzFreeEnergy_eq, twoState_helmholtzFreeEnergy_eq_T_neq_zero, try?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState

open CanonicalEnsemble Constants Real

namespace M157

/- SKELETON · paramagnet_Z
  1. Rewrite with `rw`, BEFORE any `simp` (simp would unfold `partitionFunction` itself):
       N copies → (one spin's Z) ^ N                                             R1
       one spin's Z → its finite Boltzmann sum                                   R2
  2. One `simp` call that names R3 and R6 (R4, R5 are simp lemmas already):
       the `Fin 2` sum → two terms, the energies `-h`, `h`, the signs,
       `cosh` in exponentials                                                    R3 → R4 → R5 → R6
  3. Both sides now differ only by `2 * (… / 2)`:                                 R7
-/
-- BEGIN SPEC
theorem paramagnet_Z (h : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState (-h) h)).partitionFunction T = (2 * Real.cosh ((T.β : ℝ) * h)) ^ N :=
-- END SPEC
  sorry

/- SKELETON · paramagnet_F
  1. Unfold the free energy: F = -kB * ↑T.val * log Z                             R8
  2. The `Z` inside `log` is the left side of `paramagnet_Z`: rewrite with it    R9
  3. Pull the exponent `N` out of the `log`                                       R10
  4. Rearrange the product                                                        R11
-/
-- BEGIN SPEC
theorem paramagnet_F (h : ℝ) (N : ℕ) (T : Temperature) :
    (nsmul N (twoState (-h) h)).helmholtzFreeEnergy T =
      -N * kB * T.val * Real.log (2 * Real.cosh ((T.β : ℝ) * h)) :=
-- END SPEC
  sorry

end M157

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Independence means the `N`-copy partition function is the single-spin one to the `N`th power
    (R1); then only one spin's `Z = e^{βh} + e^{-βh}` has to be matched with `2 cosh (βh)`.
    `paramagnet_F` needs no new computation: `F = -kB T log Z` and `Z` is Part 1.
H2. `paramagnet_Z`: `rw` with R1 and R2 first, then one `simp` that expands the `Fin 2` sum and `cosh`
    (R3–R6), then `ring_nf` (R7). `paramagnet_F`: unfold `F` (R8), `rw [paramagnet_Z]` (R9),
    pull the power out of the log (R10), and `ring` (R11).
H3. Key call for Z: `simp [Fin.sum_univ_two, Real.cosh_eq]` after the two `rw`s; it leaves
    `(rexp (↑T.β * h) + rexp (-(↑T.β * h))) ^ N = (2 * ((rexp (↑T.β * h) + rexp (-(↑T.β * h))) / 2)) ^ N`.
    Key step for F: right after unfolding, `rw [paramagnet_Z]` turns `log Z` into `log ((2 * cosh (↑T.β * h)) ^ N)`.
-/
