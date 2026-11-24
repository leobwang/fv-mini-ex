/- M164 | Ising ground state | 10-15 min | IsLeast, Set.range, Finset.sum_le_sum, Bool cases, nlinarith, mathlib
GOAL
  An open Ising chain has `n + 1` spins `σ : Fin (n + 1) → Bool` (`true` = up, spin `+1`) and `n` bonds
  `i ~ i+1`, with energy `E(σ) = -J ∑_i s(σ i) s(σ (i+1))`. For a ferromagnet (`J ≥ 0`) the least
  energy over all configurations is `-J n`, and it is attained (by the all-up state).

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · ground_state
  1. Split `IsLeast` into "attained" and "lower bound":                      R1
  2. Attained: the all-up witness `fun _ => true`, then evaluate its energy:  R2, then `simp [energy, spin]` (R3 → R4 → R5)
  3. Lower bound: take an arbitrary element `energy J σ` of the range:       R6
  4. Prove the bond bound first
       hb : ∀ a b : Bool, spin a * spin b ≤ 1                               `intro a b`, R7 (on `a` and `b`, with `<;>`), R8
  5. Prove the bond-sum bound
       hsum : ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ) ≤ n        R9: first step R10 (with hb), second step R5
  6. Expose the energy's formula, then combine `hJ` and `hsum`:              R11 → R12
-/
-- BEGIN SPEC
theorem ground_state (J : ℝ) (hJ : 0 ≤ J) (n : ℕ) :
    IsLeast (Set.range (energy J (n := n))) (-J * n) :=
-- END SPEC
  by
    refine ⟨⟨fun _ => true, by simp [energy, spin]⟩, ?_⟩
    rintro _ ⟨σ, rfl⟩
    have hb : ∀ a b : Bool, spin a * spin b ≤ 1 := by
      intro a b; cases a <;> cases b <;> norm_num [spin]
    have hsum : ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ) ≤ n := by
      calc ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)
          ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb _ _
        _ = n := by simp
    unfold energy
    nlinarith

end M164

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `IsLeast` is two jobs (R1): `-J * n` is the energy of some configuration, and every energy is
    `≥ -J * n`.
H2. Witness: the all-up state `fun _ => true`, whose energy `simp [energy, spin]` evaluates (R2–R5).
    Lower bound: after `rintro _ ⟨σ, rfl⟩` (R6), each bond product `spin a * spin b` is at most 1
    (four `Bool` cases), so the bond sum is at most `n` (R9, R10, R5); multiply by `-J ≤ 0` (R11, R12).
H3. `have hb : ∀ a b : Bool, spin a * spin b ≤ 1 := by intro a b; cases a <;> cases b <;> norm_num [spin]`,
    then `calc ∑ i : Fin n, ... ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb _ _`
    `_ = n := by simp`, and finish with `unfold energy; nlinarith`.
-/
