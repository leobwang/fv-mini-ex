/- M139 | Mutual information of the Bell state | 10-15 min | von Neumann entropy, mutual information, IsGreatest, library search, physlib
GOAL
  The quantum mutual information `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ)` of the maximally entangled state
  `Φ` on `d × d` is `2 log d`, and no state on `d × d` has more: `2 log d` is the maximum of `I`.

REFERENCE
  -- `Sᵥₙ ρ` is the von Neumann entropy −tr(ρ log ρ); `ρ.traceLeft` (`ρ_B`) and `ρ.traceRight` (`ρ_A`) are partial traces.
  #check @qMutualInfo        -- MState (dA × dB) → ℝ;  `rw [qMutualInfo]` unfolds it to Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ
  -- `f (x := a)` fills the implicit argument named `x`: `qMutualInfo (dA := d) (dB := d)` is `I` on `MState (d × d)`
  #check @Sᵥₙ_of_partial_eq  -- (ψ : Ket (d₁ × d₂)) : Sᵥₙ (pure ψ).traceLeft = Sᵥₙ (pure ψ).traceRight
  #check @Sᵥₙ_nonneg         -- 0 ≤ Sᵥₙ ρ
  #check @Finset.card_univ   -- Finset.univ.card = Fintype.card α   (the entropy API states bounds with the former)
  -- `IsGreatest s a` = `a ∈ s ∧ ∀ x ∈ s, x ≤ a`:
  example (s : Set ℝ) (a : ℝ) (h1 : a ∈ s) (h2 : ∀ x ∈ s, x ≤ a) : IsGreatest s a := ⟨h1, h2⟩
  example (f : ℕ → ℝ) (n : ℕ) : f n ∈ Set.range f := ⟨n, rfl⟩   -- `rintro _ ⟨n, rfl⟩` takes one apart
  -- Search: `example (ψ : Ket d) : Sᵥₙ (MState.pure ψ) = 0 := by exact?`;  `#print MState.uniform` shows what it unfolds to
-/
import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.States.Entanglement

namespace M139

-- BEGIN SPEC
theorem MES_mutual_info {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] :
    qMutualInfo (MState.pure (Ket.MES d)) = 2 * Real.log (Fintype.card d) :=
-- END SPEC
  by
    rw [qMutualInfo, Sᵥₙ_of_partial_eq, traceRight_pure_MES, Sᵥₙ_of_pure_zero, MState.uniform,
      Sᵥₙ_ofClassical, Hₛ_uniform, Finset.card_univ]
    ring

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
H1. Part 1 is a rewrite chain: unfold `qMutualInfo`, make both marginals the same, then evaluate each entropy.
    A pure state has entropy 0; the marginal of `Φ` is `MState.uniform`, whose entropy is the Shannon entropy of
    the uniform distribution. Part 2: entropies are between `0` and `log d`.
H2. Library names for part 1: `traceRight_pure_MES`, `Sᵥₙ_of_pure_zero`, `Sᵥₙ_ofClassical` (`MState.uniform`
    unfolds to `MState.ofClassical ProbDistribution.uniform`), `Hₛ_uniform`. For part 2: `Sᵥₙ_le_log_d`.
H3. `rw [qMutualInfo, Sᵥₙ_of_partial_eq, traceRight_pure_MES, Sᵥₙ_of_pure_zero, MState.uniform, Sᵥₙ_ofClassical,
    Hₛ_uniform, Finset.card_univ]; ring`. Part 2: `refine ⟨⟨_, MES_mutual_info⟩, ?_⟩; rintro _ ⟨ρ, rfl⟩`, then
    `have := Sᵥₙ_le_log_d ρ.traceLeft` (and `ρ.traceRight`, plus `Sᵥₙ_nonneg ρ`), `rw [Finset.card_univ] at *`, `linarith`.
-/
