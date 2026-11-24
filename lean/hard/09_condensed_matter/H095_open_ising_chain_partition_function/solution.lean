/- H095 | Open Ising chain partition function | 45-75 min | Fin.cons, Equiv.sum_comp, induction, cosh, mathlib
GOAL
  An open chain of `n + 1` Ising spins `s_i = spin (σ i) = ±1` (sites `0 … n`) has zero-field energy
  `E(σ) = -J ∑_{i<n} s_i s_{i+1}`. Its partition function `Z = ∑_σ exp(-β E(σ))` (all `2^(n+1)`
  configurations) equals `2 (2 cosh βJ)^n`. Prove it by summing out spin 0 and inducting on `n`.

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H095

-- BEGIN SPEC
/-- Spin value of an up (`true`) / down (`false`) site. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)

/-- Partition function: a finite sum over all `2^(n+1)` configurations. -/
noncomputable def Z (β J : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Bool, Real.exp (-β * energy J σ)
-- END SPEC

/- SKELETON · spin_pm
  1. One goal per value of `b`:                                          R1
  2. In both: unfold `spin`, decide the `if`, pick the true side of `∨`
     (`simp` with `spin`):                                                R2
-/
-- MILESTONE (optional: change or delete)
theorem spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

/- SKELETON · energy_cons
  1. Unfold `energy` on both sides; split the first bond off the longer
     chain's sum:                                                         simp only [energy], R3
  2. Evaluate `Fin.cons a σ` at every site, all in ONE `simp only`
     (the sites sit under `∑ i`, where `rw` cannot reach):                R4, R5, R6 (←), R7
  3. What is left is a ring identity:                                     ring
-/
-- MILESTONE (optional: change or delete)
theorem energy_cons (J : ℝ) {n : ℕ} (a : Bool) (σ : Fin (n + 1) → Bool) :
    energy J (Fin.cons a σ : Fin (n + 2) → Bool) = -J * (spin a * spin (σ 0)) + energy J σ := by
  simp only [energy, Fin.sum_univ_succ]
  -- WHY: bond `i+1` of the longer chain reads `σ (i.castSucc.succ)`; `← Fin.succ_castSucc` makes it `Fin.cons _ _ (_.succ)`.
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  ring

/- SKELETON · sum_exp_bond
  1. Substitute the two values of `s`:                                    R8
  2. In both goals, one `simp` with `spin` and `Real.cosh_eq`: the `Bool`
     sum becomes two terms, `spin` is evaluated, `cosh` is expanded:      R9, R2, R10
  3. Finish:                                                              ring
-/
-- MILESTONE (optional: change or delete)
theorem sum_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ a : Bool, Real.exp (K * (spin a * s)) = 2 * Real.cosh K := by
  rcases hs with rfl | rfl <;> simp [spin, Real.cosh_eq] <;> ring

/- SKELETON · Z_eq
  Prove the milestones above first (each has its own SKELETON):
    spin_pm        `spin b = 1 ∨ spin b = -1`                      used in step 3b (hypothesis of sum_exp_bond)
    energy_cons    energy of `Fin.cons a σ` = new bond + energy σ  used in step 3a
    sum_exp_bond   `∑ a, exp (K * (spin a * s)) = 2 * cosh K`      used in step 3b
  1. Induction on `n`:                                                                     R11
  2. zero: one spin, no bonds, 2 configurations: `simp` with `Z`, `energy`:                R12, R13, R14, R15
  3. succ:
     a. Prove first
          hsplit : Z β J (n + 1) = ∑ σ : Fin (n + 1) → Bool, ∑ a : Bool,
                     Real.exp (β * J * (spin a * spin (σ 0))) * Real.exp (-β * energy J σ)
        unfold `Z`, re-index by (spin 0, rest), split the pair sum, put `∑ a` inside:     R16, R17, R18, R19
        compare the terms (name the outer configuration `σ`, the inner spin `a`):         R20
        the left side reads `Real.exp (-β * energy J ((Fin.consEquiv _) (a, σ)))`: restate
        it with `(Fin.cons a σ : Fin (n + 2) → Bool)`, right side kept as `_`:            R21
        rw [energy_cons], merge the exponentials, close:                                   R22, R23
     b. rw [hsplit]; pull `exp (-β E(σ))` out of the `a`-sum, evaluate the `a`-sum with
        `sum_exp_bond _ _ (spin_pm _)`, pull `2 cosh βJ` out of the `σ`-sum:              R24, R25, R26
     c. fold the `σ`-sum back into `Z β J n`, use `ih`, finish:                            R27, rw [ih], ring
-/
-- BEGIN SPEC
theorem Z_eq (β J : ℝ) (n : ℕ) : Z β J n = 2 * (2 * Real.cosh (β * J)) ^ n :=
-- END SPEC
  by
    induction n with
    | zero => simp [Z, energy]
    | succ n ih =>
      have hsplit : Z β J (n + 1) = ∑ σ : Fin (n + 1) → Bool, ∑ a : Bool,
          Real.exp (β * J * (spin a * spin (σ 0))) * Real.exp (-β * energy J σ) := by
        rw [Z, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
        show Real.exp (-β * energy J (Fin.cons a σ : Fin (n + 2) → Bool)) = _
        rw [energy_cons, ← Real.exp_add]
        ring_nf
      rw [hsplit]
      simp_rw [← Finset.sum_mul, sum_exp_bond _ _ (spin_pm _), ← Finset.mul_sum]
      rw [← Z, ih]
      ring

end H095

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A configuration of `n + 2` spins is a pair (spin 0, the other `n + 1` spins). Spin 0 only touches
    the bond to its neighbour, so `exp(-βE)` factors as `exp(βJ s_a s_{σ 0}) * exp(-β E(σ))`, and the
    sum over `s_a = ±1` gives `2 cosh βJ` whatever `s_{σ 0}` is. The three milestones say exactly this.
H2. `induction n`; the base case is `simp [Z, energy]`. In the step, prove `hsplit` (statement in the
    SKELETON): reindex along `Fin.consEquiv`, split the pair sum, swap the sums so `∑ a : Bool` is
    inside, then compare terms with `energy_cons` and `← Real.exp_add`. Then factor with `simp_rw`:
    `← Finset.sum_mul`, `sum_exp_bond`, `← Finset.mul_sum`, and fold `Z` to use `ih`.
H3. `energy_cons`: `simp only [energy, Fin.sum_univ_succ]`, then
    `simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]; ring`.
    hsplit: `rw [Z, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`;
    inside, `show Real.exp (-β * energy J (Fin.cons a σ : Fin (n + 2) → Bool)) = _` exposes `Fin.cons`.
    Factoring: `simp_rw [← Finset.sum_mul, sum_exp_bond _ _ (spin_pm _), ← Finset.mul_sum]`.
-/
