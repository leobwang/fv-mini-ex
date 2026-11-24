/- M159 | Density of states of N two-level systems | 15-20 min | Finset.card, bijections, powersetCard, sum_fiberwise, mathlib
GOAL
  `N` two-level systems with level spacing `ε`: a configuration is `σ : Fin N → Bool` (`true` = excited),
  with energy `ε * nUp σ`. (a) Exactly `C(N, m)` configurations have `m` excitations (the degeneracy
  `g(m)`). (b) So `Z = ∑_σ exp (-b E(σ))` (`b` = inverse temperature β, units kB = 1) can be summed over levels: `Z = ∑_{m=0}^{N} g(m) exp (-b ε m)`.

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Real

namespace M159

-- BEGIN SPEC
/-- Number of excited two-level systems (`true` = excited, energy `ε`) in a configuration. -/
def nUp {N : ℕ} (σ : Fin N → Bool) : ℕ := (Finset.univ.filter fun i => σ i = true).card
-- END SPEC

/- SKELETON · degeneracy
  1. Turn the right side into a card of a powerset, as a fact proved first (have):
       hc : N.choose m = (Finset.powersetCard m (Finset.univ : Finset (Fin N))).card
       proof: `simp` with R1 (it then applies R2 → R3 itself)
     then rw [hc]. Do NOT rewrite N into Fintype.card (Fin N) (Traps).
  2. Count by a bijection, sites ↦ excited set and back:                    R4
       i = fun σ => Finset.univ.filter fun i => σ i = true
       j = fun s i => decide (i ∈ s)
     Four goals, in this order:
  3. MapsTo i: intro, clean the hypothesis down to `nUp σ = m`:             R5, R6 → R7 → R8
     then close the goal from it, unfolding nUp:                            R12 with R9, R10, R11
  4. MapsTo j: intro, clean the hypothesis to `s ⊆ univ ∧ s.card = m`:       R5, R9, R10
     then `simp` with nUp and its second half (hs.2); simp applies:          R6, R7, R8, R13, R11, R14
  5. LeftInvOn: intro, compare the two configurations site by site:         R15, R16
     then `simp` (it applies R17, R8, R18)
  6. RightInvOn: intro, compare the two finsets element by element:          R15, R19
     then `simp` (it applies R13, R11, R14)
-/
-- BEGIN SPEC
theorem degeneracy (N m : ℕ) :
    (Finset.univ.filter fun σ : Fin N → Bool => nUp σ = m).card = N.choose m :=
-- END SPEC
  by
    have hc : N.choose m = (Finset.powersetCard m (Finset.univ : Finset (Fin N))).card := by
      simp [Finset.card_powersetCard]
    rw [hc]
    refine Finset.card_nbij' (fun σ => Finset.univ.filter fun i => σ i = true)
      (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ
      simpa [Finset.mem_powersetCard, nUp] using hσ
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
      simp [nUp, hs.2]
    · intro σ _
      funext i
      simp
    · intro s _
      ext i
      simp

/- SKELETON · Z_from_dos
  1. Regroup the left sum by g := nUp into t := Finset.range (N + 1):        R20
     Two goals: the regrouped equation, and the maps-to side goal (case h).
  2. Regrouped equation: compare summands at one level m:                    R21
  3. On the fibre `nUp σ = m` replace the summand by the constant
       c = Real.exp (-b * (ε * m))                                           R22
     Two goals again:
  4. The constant sum: count the fibre, use part (a), cast:                  R23, rw [degeneracy], R24
  5. "summand = c" on the fibre: intro, unpack the filter membership,
     rewrite with its second half:                                           R17, rw [hσ.2]
  6. Maps-to side goal: intro, turn `nUp σ ∈ range (N + 1)` into
     `{i | σ i = true}.card ≤ N` (unfold nUp too):                           R25, R26
     then bound the card by the size of `Fin N`:                             R27, R28, R3
-/
-- BEGIN SPEC
theorem Z_from_dos (N : ℕ) (b ε : ℝ) :
    ∑ σ : Fin N → Bool, Real.exp (-b * (ε * nUp σ)) =
      ∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * Real.exp (-b * (ε * m)) :=
-- END SPEC
  by
    rw [← Finset.sum_fiberwise_of_maps_to (g := nUp) (t := Finset.range (N + 1))]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => Real.exp (-b * (ε * m)))]
      · rw [Finset.sum_const, degeneracy, nsmul_eq_mul]
      · intro σ hσ
        simp only [Finset.mem_filter] at hσ
        rw [hσ.2]
    · intro σ _
      simp only [Finset.mem_range, Nat.lt_succ_iff, nUp]
      exact (Finset.card_le_univ _).trans (by simp)

end M159

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (a) A configuration with `m` excitations is the same thing as an `m`-element subset of the sites
    (the excited ones): count by a bijection with `Finset.powersetCard m univ`. (b) Group the
    configurations by their number of excitations; each group has `C(N, m)` members by (a).
H2. (a) `have hc : N.choose m = (Finset.powersetCard m (Finset.univ : Finset (Fin N))).card`
    (by `simp [Finset.card_powersetCard]`), `rw [hc]`, then `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_`
    with `i = fun σ => Finset.univ.filter fun i => σ i = true` and `j = fun s i => decide (i ∈ s)`.
    (b) `rw [← Finset.sum_fiberwise_of_maps_to (g := nUp) (t := Finset.range (N + 1))]`, then
    `Finset.sum_congr rfl` twice: once to fix a level `m`, once to make the summand the constant
    `Real.exp (-b * (ε * m))`.
H3. (a) First MapsTo goal: after cleaning `hσ` to `nUp σ = m`, `simpa [Finset.mem_powersetCard, nUp] using hσ`;
    second: `simp [nUp, hs.2]`. Inverse laws: `funext i; simp` and `ext i; simp`.
    (b) One level: `rw [Finset.sum_const, degeneracy, nsmul_eq_mul]`. The maps-to goal is `nUp σ ≤ N`:
    `(Finset.card_le_univ _).trans (by simp)`.
-/
