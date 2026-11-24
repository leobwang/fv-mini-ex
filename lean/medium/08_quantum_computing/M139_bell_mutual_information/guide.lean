/- Guide for M139 (Mutual information of the Bell state).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (an arbitrary pure state, the
conditional entropy, the least entropy).
Assumed: Lean basics. physlib names (`MState`, `Ket`, `Sᵥₙ`, …) are explained in cheatsheet.md.
-/
import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.States.Entanglement

namespace M139Guide

/-! # Part R · Reference entries -/

/-! ## Part 1: evaluating entropies by rewriting -/

/-! ### R1. `rw [qMutualInfo]` · goal: `qMutualInfo ρ` → its definition `S(ρ_B) + S(ρ_A) − S(ρ)` -/
example {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState (d₁ × d₂)) (P : ℝ → Prop)
    (h : P (Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ)) : P (qMutualInfo ρ) := by
  rw [qMutualInfo]
  exact h

/-! ### R2. `Sᵥₙ_of_partial_eq` · goal: for a pure state, entropy of `traceLeft` → entropy of `traceRight`
`Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight` (both marginals of a pure state
have the same spectrum, Schmidt decomposition). -/
example {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (P : ℝ → Prop)
    (h : P (Sᵥₙ (MState.pure ψ).traceRight)) : P (Sᵥₙ (MState.pure ψ).traceLeft) := by
  rw [Sᵥₙ_of_partial_eq]
  exact h

/-! ### R3. `traceRight_pure_MES` · goal: the marginal of the maximally entangled state → `MState.uniform`
`(MState.pure (Ket.MES d)).traceRight = MState.uniform`; `d` is an explicit argument, `rw` finds it. -/
example {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (P : MState d → Prop)
    (h : P MState.uniform) : P (MState.pure (Ket.MES d)).traceRight := by
  rw [traceRight_pure_MES]
  exact h

/-! ### R4. `Sᵥₙ_of_pure_zero` · goal: entropy of a pure state → `0` -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (P : ℝ → Prop)
    (h : P 0) : P (Sᵥₙ (MState.pure ψ)) := by
  rw [Sᵥₙ_of_pure_zero]
  exact h

/-! ### R5. `rw [MState.uniform]` · goal: the maximally mixed state → `ofClassical` of the uniform distribution -/
example {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (P : MState d → Prop)
    (h : P (MState.ofClassical ProbDistribution.uniform)) : P MState.uniform := by
  rw [MState.uniform]
  exact h

/-! ### R6. `Sᵥₙ_ofClassical` · goal: von Neumann entropy of a diagonal state → Shannon entropy `Hₛ` -/
example {d : Type} [Fintype d] [DecidableEq d] (p : ProbDistribution d) (P : ℝ → Prop)
    (h : P (Hₛ p)) : P (Sᵥₙ (MState.ofClassical p)) := by
  rw [Sᵥₙ_ofClassical]
  exact h

/-! ### R7. `Hₛ_uniform` · goal: Shannon entropy of the uniform distribution → `log |univ|` -/
example {α : Type} [Fintype α] [Nonempty α] (P : ℝ → Prop)
    (h : P (Real.log ((Finset.univ : Finset α).card : ℝ))) :
    P (Hₛ (ProbDistribution.uniform (α := α))) := by
  rw [Hₛ_uniform]
  exact h

/-! ### R8. `Finset.card_univ` · goal: `Finset.univ.card` → `Fintype.card α` (same number, two spellings) -/
example {α : Type} [Fintype α] (P : ℕ → Prop)
    (h : P (Fintype.card α)) : P (Finset.univ : Finset α).card := by
  rw [Finset.card_univ]
  exact h

/-! ## Part 2: a greatest element of a range -/

/-! ### R9. `refine ⟨?_, ?_⟩` on `IsGreatest s a` · goal list: `a ∈ s` and `a ∈ upperBounds s`
`IsGreatest s a` is defined as `a ∈ s ∧ a ∈ upperBounds s`, so the `∧` pattern applies. -/
example {α : Type} [LE α] (s : Set α) (a : α) (h1 : a ∈ s) (h2 : a ∈ upperBounds s) :
    IsGreatest s a := by
  refine ⟨?_, ?_⟩
  · exact h1
  · exact h2

/-! ### R10. `⟨x, h⟩` proves `b ∈ Set.range f` from `h : f x = b` · closes the goal
`Set.range f = {b | ∃ x, f x = b}`; write `⟨_, h⟩` to let Lean read `x` off `h`. -/
example {α β : Type} (f : α → β) (x : α) (b : β) (h : f x = b) : b ∈ Set.range f := by
  exact ⟨_, h⟩

/-! ### R11. `rintro _ ⟨x, rfl⟩` · goal `a ∈ upperBounds (Set.range f)` → context gains `x`, goal `f x ≤ a`
`a ∈ upperBounds s` unfolds to `∀ b, b ∈ s → b ≤ a`; `rintro` introduces `b` and `b ∈ Set.range f`,
splits the latter into `x` and `f x = b`, and `rfl` substitutes `b := f x`. -/
example {α : Type} (f : α → ℝ) (a : ℝ) (h : ∀ x, f x ≤ a) : a ∈ upperBounds (Set.range f) := by
  rintro _ ⟨x, rfl⟩
  exact h x

/-! ### R12. `have hA := Sᵥₙ_le_log_d ρ` · context gains `hA : Sᵥₙ ρ ≤ Real.log ↑Finset.univ.card` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (g : Sᵥₙ ρ ≤ Real.log ((Finset.univ : Finset d).card : ℝ) → G) : G := by
  have hA := Sᵥₙ_le_log_d ρ
  exact g hA

/-! ### R13. `have h0 := Sᵥₙ_nonneg ρ` · context gains `h0 : 0 ≤ Sᵥₙ ρ` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (g : 0 ≤ Sᵥₙ ρ → G) : G := by
  have h0 := Sᵥₙ_nonneg ρ
  exact g h0

/-! ### R14. `rw [Finset.card_univ] at hA hB` · context: R8 applied inside hypotheses, goal unchanged -/
example {α : Type} [Fintype α] (Q R : ℕ → Prop) (hA : Q (Finset.univ : Finset α).card)
    (hB : R (Finset.univ : Finset α).card) (G : Prop) (g : Q (Fintype.card α) → R (Fintype.card α) → G) :
    G := by
  rw [Finset.card_univ] at hA hB
  exact g hA hB

/-! ### R15. `linarith` · closes a linear (in)equality over `ℝ` that follows from hypotheses
Atoms such as `Sᵥₙ ρ` or `Real.log c` are treated as unknowns; definitions are NOT unfolded. -/
example (x y z c : ℝ) (hx : x ≤ c) (hy : y ≤ c) (hz : 0 ≤ z) : x + y - z ≤ 2 * c := by
  linarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Any pure bipartite state: `I = 2 S(ρ_A)` (R1, R2, R4, then `ring`) -/
example {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) : qMutualInfo (MState.pure ψ) = 2 * Sᵥₙ (MState.pure ψ).traceRight := by
  rw [qMutualInfo]
  rw [Sᵥₙ_of_partial_eq]
  rw [Sᵥₙ_of_pure_zero]
  ring

/-! ### W2. A bound by the facts-then-`linarith` pattern: `S(ρ_B) − S(ρ) ≤ log |B|` (R12, R13, R14, R15) -/
example {d₁ d₂ : Type} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceLeft - Sᵥₙ ρ ≤ Real.log (Fintype.card d₂) := by
  have hB := Sᵥₙ_le_log_d ρ.traceLeft
  have h0 := Sᵥₙ_nonneg ρ
  rw [Finset.card_univ] at hB
  linarith

/-! ### W3. `IsLeast` (the mirror of `IsGreatest`): `0` is the least entropy (R9-style split, R10, R11, R13)
`IsLeast s a` is `a ∈ s ∧ a ∈ lowerBounds s`. `(d := d)` fixes the implicit argument `d` of `Sᵥₙ`. -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) : IsLeast (Set.range (Sᵥₙ (d := d))) 0 := by
  refine ⟨⟨_, Sᵥₙ_of_pure_zero ψ⟩, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact Sᵥₙ_nonneg ρ

end M139Guide
