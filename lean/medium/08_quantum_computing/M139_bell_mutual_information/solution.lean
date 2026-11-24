/- M139 | Mutual information of the Bell state | 10-15 min | von Neumann entropy, mutual information, IsGreatest, library search, physlib
GOAL
  The quantum mutual information `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ)` of the maximally entangled state
  `Φ` on `d × d` is `2 log d`, and no state on `d × d` has more: `2 log d` is the maximum of `I`.

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.States.Entanglement

namespace M139

/- SKELETON · MES_mutual_info
  One `rw [...]` chain, in this order, then `ring`:
  1. Unfold the mutual information:                                         R1
       goal: S(Φ_B) + S(Φ_A) − S(Φ) = 2 log ↑(card d)
  2. Make both marginals the same (Φ is pure), so one rewrite hits both:    R2
  3. Each marginal of Φ is the maximally mixed state:                       R3
  4. Φ is pure, so its own entropy is 0:                                    R4
  5. Maximally mixed → diagonal → Shannon entropy → log:                    R5 → R6 → R7
  6. `Finset.univ.card` → `Fintype.card d`, to match the right-hand side:   R8
  7. Goal is now `log c + log c − 0 = 2 * log c`:                           ring
-/
-- BEGIN SPEC
theorem MES_mutual_info {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] :
    qMutualInfo (MState.pure (Ket.MES d)) = 2 * Real.log (Fintype.card d) :=
-- END SPEC
  by
    rw [qMutualInfo, Sᵥₙ_of_partial_eq, traceRight_pure_MES, Sᵥₙ_of_pure_zero, MState.uniform,
      Sᵥₙ_ofClassical, Hₛ_uniform, Finset.card_univ]
    ring

/- SKELETON · MES_max_mutual_info
  1. Split `IsGreatest` and fill the membership half with the theorem
     `MES_mutual_info` above as the witness proof:                          R9 with R10 inside
  2. Upper-bound half: introduce an arbitrary state `ρ : MState (d × d)`:   R11
       goal: qMutualInfo ρ ≤ 2 * Real.log ↑(Fintype.card d)
  3. Collect the bounds S(ρ.traceLeft) ≤ log, S(ρ.traceRight) ≤ log
     (R12, twice) and 0 ≤ S(ρ) (R13):                                       R12, R12, R13
  4. Restate the two upper bounds with `Fintype.card`:                      R14
  5. Unfold `qMutualInfo` in the goal, then close by linear arithmetic:     R1, R15
-/
-- BEGIN SPEC
theorem MES_max_mutual_info {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] :
    IsGreatest (Set.range (qMutualInfo (dA := d) (dB := d))) (2 * Real.log (Fintype.card d)) :=
-- END SPEC
  by
    refine ⟨⟨_, MES_mutual_info⟩, ?_⟩
    rintro _ ⟨ρ, rfl⟩
    have hA := Sᵥₙ_le_log_d ρ.traceLeft
    have hB := Sᵥₙ_le_log_d ρ.traceRight
    have hAB := Sᵥₙ_nonneg ρ
    rw [Finset.card_univ] at hA hB
    rw [qMutualInfo]
    linarith

end M139

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Neither entropy is computed by hand. Part 1 is one `rw` chain: unfold `qMutualInfo`, then one library
    lemma per entropy term (pure state, marginal of `Φ`, maximally mixed state). Part 2: `I(ρ)` is
    `S(ρ_B) + S(ρ_A) − S(ρ)`, each marginal entropy is at most `log d` and `S(ρ) ≥ 0`.
H2. Part 1: `qMutualInfo`, `Sᵥₙ_of_partial_eq`, `traceRight_pure_MES`, `Sᵥₙ_of_pure_zero`, then
    `MState.uniform`, `Sᵥₙ_ofClassical`, `Hₛ_uniform`, and `Finset.card_univ` (the library says
    `Finset.univ.card` where the statement says `Fintype.card d`); finish with `ring`.
    Part 2: split `IsGreatest` with Part 1 as the witness, take `ρ` with `rintro`, gather
    `Sᵥₙ_le_log_d` (for both marginals) and `Sᵥₙ_nonneg ρ`, fix the card spelling, `linarith`.
H3. `rw [qMutualInfo, Sᵥₙ_of_partial_eq, traceRight_pure_MES, Sᵥₙ_of_pure_zero, MState.uniform, Sᵥₙ_ofClassical,
    Hₛ_uniform, Finset.card_univ]; ring`. Part 2: `refine ⟨⟨_, MES_mutual_info⟩, ?_⟩; rintro _ ⟨ρ, rfl⟩`, then
    `have hA := Sᵥₙ_le_log_d ρ.traceLeft` (and `hB` for `ρ.traceRight`, `hAB := Sᵥₙ_nonneg ρ`),
    `rw [Finset.card_univ] at hA hB`, `rw [qMutualInfo]`, `linarith`.
-/
