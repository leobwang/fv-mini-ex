/- M170 | Counting the allowed wavenumbers | 10-15 min | Set.ncard, injectivity, casts, physlib
GOAL
  Periodic boundary conditions allow exactly `N` wavenumbers, one per site:
  the set `T.QuantaWaveNumber` has `T.N` elements.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M170

/- SKELETON · card_wavenumbers
  1. Milestone first: the set is the range of a map on `Fin T.N`. State it with the body of the
     definition copied exactly (R2 shows it):
       hset : T.QuantaWaveNumber = Set.range (fun n : Fin T.N => <the formula of R2>)
     typed as in guide.lean R2: index `(n : ℝ)`, shift `(T.N / 2 : ℕ)` (not `↑↑n`, see Traps)
     proof:                                                                R1 → R2 → R3 → R4
     (R4 closes the `↔`; `simp only` with R2, R3, R4 in one call also does it)
  2. rw [hset], then count the range. The count closes by itself; the side goal
     `Function.Injective (fun n => …)` remains:                           R5 → R6 → R7
  3. Injectivity: introduce the two indices and their equation:           R8
  4. Fact: the prefactor is nonzero,
       hc : 2 * Real.pi / (T.a * T.N) ≠ 0
     proof: put `0 < T.a` and `(0 : ℝ) < T.N` in the context, then         R9, R10 → R11, R12
  5. Cancel the prefactor, then the shift, then go back to `Fin`:
                                                                           R13, R14, R15, R16 (or R11)
-/
-- BEGIN SPEC
theorem card_wavenumbers (T : TightBindingChain) : T.QuantaWaveNumber.ncard = T.N :=
-- END SPEC
  sorry

end M170

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfolded, `T.QuantaWaveNumber` is `{x | ∃ n : Fin T.N, f n = x}`: the range of a map
    `f : Fin T.N → ℝ`. A range of an injective map on `Fin N` has `N` elements (R5–R7).
H2. Prove `hset` (step 1 of the skeleton: `ext x`, then unfold with R2, R3, R4). Then
    `rw [hset, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]` leaves only
    injectivity. There: `intro m n h`, prove the prefactor nonzero with `positivity` (after R9, R10, R11),
    cancel it (R13), cancel the shift `↑(T.N / 2)` (R14), and return to `Fin` (R15, R16).
H3. `hset` by `ext x; simp only [TightBindingChain.QuantaWaveNumber, Set.mem_setOf_eq, Set.mem_range]`;
    the last line: `exact Fin.ext (by exact_mod_cast sub_left_inj.mp (mul_left_cancel₀ hc h))`.
-/
