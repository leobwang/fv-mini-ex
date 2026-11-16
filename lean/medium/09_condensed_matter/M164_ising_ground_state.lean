/- M164 | Ising ground state | 10-15 min | IsLeast, Set.range, Finset.sum_le_sum, Bool cases, nlinarith, mathlib
GOAL
  An open Ising chain has `n + 1` spins `σ : Fin (n + 1) → Bool` (`true` = up, spin `+1`) and `n` bonds
  `i ~ i+1`, with energy `E(σ) = -J ∑_i s(σ i) s(σ (i+1))`. For a ferromagnet (`J ≥ 0`) the least
  energy over all configurations is `-J n`, and it is attained (by the all-up state).

REFERENCE
  example (s : Set ℝ) (a : ℝ) : IsLeast s a ↔ a ∈ s ∧ ∀ x ∈ s, a ≤ x := Iff.rfl  -- attained + lower bound
  example (f : ℕ → ℝ) : f 3 ∈ Set.range f := ⟨3, rfl⟩     -- members of a range: `⟨witness, proof⟩`
  -- `rintro _ ⟨σ, rfl⟩` introduces an arbitrary element `energy J σ` of `Set.range (energy J)`
  #check Finset.sum_le_sum  -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  example (n : ℕ) : ∑ _i : Fin n, (1 : ℝ) = n := by simp
  example (a b : Bool) : a = b ∨ a ≠ b := by cases a <;> cases b <;> simp   -- all 4 Bool cases
  example (J S n : ℝ) (hJ : 0 ≤ J) (h : S ≤ n) : -J * n ≤ -J * S := by nlinarith
  `i.castSucc, i.succ : Fin (n + 1)` are the two ends of bond `i : Fin n` (sites `i` and `i + 1`).
  #check (energy 1 (n := 3) : (Fin 4 → Bool) → ℝ)  -- `(n := 3)` fills the implicit length `n` by name
-/
import Mathlib

namespace M164

-- BEGIN SPEC
/-- Ising spin value of a site: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)
-- END SPEC

-- BEGIN SPEC
theorem ground_state (J : ℝ) (hJ : 0 ≤ J) (n : ℕ) :
    IsLeast (Set.range (energy J (n := n))) (-J * n) :=
-- END SPEC
  sorry

end M164

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two jobs: show `-J * n` is the energy of some configuration, and that every energy is `≥ -J * n`.
H2. Witness: the all-up state `fun _ => true` (`simp [energy, spin]`). Lower bound: every bond
    product `spin a * spin b` is at most 1, so the bond sum is at most `n`; multiply by `-J ≤ 0`.
H3. `have hb : ∀ a b : Bool, spin a * spin b ≤ 1 := by intro a b; cases a <;> cases b <;> norm_num [spin]`,
    then `calc ∑ i : Fin n, ... ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb _ _`
    `_ = n := by simp`, and finish with `unfold energy; nlinarith`.
-/
