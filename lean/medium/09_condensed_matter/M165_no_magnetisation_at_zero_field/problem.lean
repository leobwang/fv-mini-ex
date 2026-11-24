/- M165 | No magnetisation at zero field | 15 min | Equiv, Equiv.sum_comp, involution, spin flip, mathlib
GOAL
  At zero field the open-chain energy `E = energy J`, `E(σ) = -J ∑_i s(σ i) s(σ (i+1))` with spin value
  `s = spin` (`true ↦ +1`, `false ↦ -1`), is unchanged by flipping every spin. Hence at inverse temperature
  `β` the unnormalised magnetisation of any site `k` vanishes: `∑_σ s(σ k) · exp (-β E(σ)) = 0`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M165

-- BEGIN SPEC
/-- Ising spin value of a site: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)
-- END SPEC

/- SKELETON · no_magnetization
  1. Build the global spin flip with `let` (not `have`), toFun = invFun = σ ↦ (i ↦ !σ i):
       flip : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool)                    R1
       each of the two laws: an equation of functions                        R2 → R3
  2. The sign of one flipped spin, by cases on the Bool:
       hs : ∀ b : Bool, spin (!b) = -spin b                                  intro b, R4
       both goals read `(spin !false) = -spin false` / `… true …`: `simp [spin]`
       unfolds `spin`, evaluates `!false`, picks the `if` branch              R5
  3. The energy is flip-invariant:
       hE : ∀ σ, energy J (flip σ) = energy J σ
       unfold `energy` and `flip`, evaluate `flip σ i`, use `hs` under the ∑,
       cancel the two signs of each bond (one `simp only` with all of them)   R6, R7, R8
  4. Each flipped summand is minus the original:
       h2 : ∀ σ, spin (flip σ k) * Real.exp (-β * energy J (flip σ))
                 = -(spin (σ k) * Real.exp (-β * energy J σ))
       rw [hE]; evaluate `flip σ k`, use `hs`, pull the sign out    rw [hE], R6, simp only [hs], R9
  5. Reindex the sum by `flip`: h : ∑ σ, <summand at flip σ> = ∑ σ, <summand at σ>   R10
  6. Rewrite h with h2, then move the minus out of the sum: h : -S = S          R11 → R12
  7. Close the goal S = 0                                                       R13
-/
-- BEGIN SPEC
theorem no_magnetization (β J : ℝ) (n : ℕ) (k : Fin (n + 1)) :
    ∑ σ : Fin (n + 1) → Bool, spin (σ k) * Real.exp (-β * energy J σ) = 0 :=
-- END SPEC
  sorry

end M165

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Flipping every spin is a bijection of configurations (it is its own inverse) that keeps the energy
    and negates `spin (σ k)`. Summing over flipped configurations reorders the same terms (R10), so the
    sum `S` satisfies `S = -S`.
H2. Strategy, as in the SKELETON: `let flip` as an `Equiv` (R1–R3); `hs : spin (!b) = -spin b` by
    `cases b` (R4, R5); `hE` and `h2` by `simp only` with `flip`, `Equiv.coe_fn_mk`, `hs` and a sign
    lemma (R6–R9); then `Equiv.sum_comp`, `simp only … at h`, `linarith` (R10–R13).
H3. `let flip : (Fin (n + 1) → Bool) ≃ (Fin (n + 1) → Bool) := ⟨fun σ i => !σ i, fun σ i => !σ i,
    fun σ => by funext i; simp, fun σ => by funext i; simp⟩`;
    `hE`: `intro σ; simp only [energy, flip, Equiv.coe_fn_mk, hs, neg_mul_neg]`; then
    `have h := Equiv.sum_comp flip (fun σ => spin (σ k) * Real.exp (-β * energy J σ))` and
    `simp only [h2, Finset.sum_neg_distrib] at h; linarith`.
-/
