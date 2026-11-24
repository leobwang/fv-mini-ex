/- H096 | Spin correlations in the Ising chain | 1.5-2 h | Fin.snoc, Fin.snocEquiv, Nat.le_induction, tanh, correlation length, mathlib
GOAL
  Open zero-field chain of `n + 1` spins `s_i = spin (σ i) = ±1`, energy `E(σ) = -J ∑_{i<n} s_i s_{i+1}`.
  The thermal average `⟨s₀ s_r⟩ = (∑_σ s₀ s_r e^{-βE(σ)}) / Z` equals `tanh(βJ)^r` for every `r ≤ n`,
  whatever the length `n`: correlations decay like `e^{-r/ξ}` (correlation length
  `ξ = -1 / log tanh βJ` for `βJ > 0`), so there is no long-range order at `T > 0`.

GUIDE
  Entries R1–R36: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H096

-- BEGIN SPEC
/-- Spin value of an up (`true`) / down (`false`) site. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field energy of an open chain of `n + 1` spins with coupling `J`. -/
noncomputable def energy (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)

/-- Partition function of the chain of `n + 1` spins. -/
noncomputable def Z (β J : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Bool, Real.exp (-β * energy J σ)

/-- Thermal average `⟨s₀ s_r⟩` in a chain of `n + 1` spins (`r ≤ n`). -/
noncomputable def corr (β J : ℝ) (n r : ℕ) (hr : r ≤ n) : ℝ :=
  (∑ σ : Fin (n + 1) → Bool,
    spin (σ 0) * spin (σ ⟨r, by omega⟩) * Real.exp (-β * energy J σ)) / Z β J n
-- END SPEC

-- Helpers (not milestones).
theorem spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> simp [spin]

theorem sum_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ b : Bool, Real.exp (K * (s * spin b)) = 2 * Real.cosh K := by
  rcases hs with rfl | rfl <;> simp [spin, Real.cosh_eq] <;> ring

theorem sum_spin_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ b : Bool, spin b * Real.exp (K * (s * spin b)) = 2 * Real.sinh K * s := by
  rcases hs with rfl | rfl <;> simp [spin, Real.sinh_eq] <;> ring

-- Helper (not a milestone; its statement is in H2).
theorem energy_snoc (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) (b : Bool) :
    energy J (Fin.snoc σ b : Fin (n + 2) → Bool) =
      energy J σ - J * (spin (σ (Fin.last n)) * spin b) := by
  simp only [energy, Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

/- SKELETON · snoc_split
  0. Helper first (statement in H2): `energy_snoc`, the energy of `(Fin.snoc σ b : Fin (n + 2) → Bool)`.
       unfold `energy`, split off the last bond:                       simp only [energy], R1
       evaluate `Fin.snoc` at the `castSucc` and `last` sites, in ONE
       `simp only [...]` (they sit under `∑ i`, where `rw` fails):     R2, R3, R4, R5
       finish:                                                          ring
  1. Left side: re-index by pairs `(b, τ)`, split, put `τ` outside:     R6, R7, R8
  2. Compare the `τ`-terms:                                             R9
  3. Right side: move `e^{-βE(τ)}` into the `b`-sum; compare `b`-terms: R10, R9
  4. Write the term with `Fin.snoc τ b` instead of `Fin.snocEquiv`:     R11
  5. Evaluate the sites and the energy (one `simp only`):              R3, R5, energy_snoc
  6. Regroup, merge the two exponentials, close:                        R12, R13, R14
-/
-- MILESTONE (optional: change or delete)
/-- Summing out the last spin of a chain of `n + 2` spins. -/
theorem snoc_split (β J : ℝ) (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool → ℝ) :
    ∑ σ : Fin (n + 2) → Bool,
        f (fun i => σ i.castSucc) (σ (Fin.last (n + 1))) * Real.exp (-β * energy J σ) =
      ∑ τ : Fin (n + 1) → Bool, (∑ b : Bool,
        f τ b * Real.exp (β * J * (spin (τ (Fin.last n)) * spin b))) * Real.exp (-β * energy J τ) := by
  rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  -- WHY: `Fin.snocEquiv` applied to `(b, τ)` only unfolds to `Fin.snoc τ b` by `show`.
  show f (fun i => (Fin.snoc τ b : Fin (n + 2) → Bool) i.castSucc)
      ((Fin.snoc τ b : Fin (n + 2) → Bool) (Fin.last (n + 1))) *
      Real.exp (-β * energy J (Fin.snoc τ b : Fin (n + 2) → Bool)) = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last, energy_snoc]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/- SKELETON · sum_snoc   (uses snoc_split)
  0. Helpers first:
       spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1                                  R15
       sum_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
         ∑ b : Bool, Real.exp (K * (s * spin b)) = 2 * Real.cosh K                    R16, R17, R18, ring
  1. Rewrite with `snoc_split` at `f := fun τ _ => g τ`; push `2 cosh βJ` in:   R20, R21
  2. Compare the `τ`-terms:                                                     R9
  3. Pull `g τ` out of the `b`-sum, then `rw [sum_exp_bond _ _ (spin_pm _)]`:   R21 (←), ring
-/
-- MILESTONE (optional: change or delete)
/-- An observable that ignores the last spin: appending a spin multiplies the sum by `2 cosh βJ`. -/
theorem sum_snoc (β J : ℝ) (n : ℕ) (g : (Fin (n + 1) → Bool) → ℝ) :
    ∑ σ : Fin (n + 2) → Bool, g (fun i => σ i.castSucc) * Real.exp (-β * energy J σ) =
      2 * Real.cosh (β * J) * ∑ τ : Fin (n + 1) → Bool, g τ * Real.exp (-β * energy J τ) := by
  rw [snoc_split β J n (fun τ _ => g τ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, sum_exp_bond _ _ (spin_pm _)]
  ring

/- SKELETON · Z_eq   (uses sum_snoc)
  Induction on `n`.
  1. zero: one spin, no bonds, two configurations: `simp` with `Z`, `energy`:   R22, R23
  2. succ: `have h := sum_snoc …` at `g := fun _ => 1`; drop the `1 *`:          R20, R24
     unfold `Z`, use `h`, fold the short sum back into `Z`, use `ih`:            R25, ring
-/
-- MILESTONE (optional: change or delete)
/-- H095's result, here via `sum_snoc` with `g := fun _ => 1`. -/
theorem Z_eq (β J : ℝ) (n : ℕ) : Z β J n = 2 * (2 * Real.cosh (β * J)) ^ n := by
  induction n with
  | zero => simp [Z, energy]
  | succ n ih =>
    have h := sum_snoc β J n (fun _ => 1)
    simp only [one_mul] at h
    rw [Z, h, ← Z, ih]
    ring

/- SKELETON · G_eq   (uses snoc_split)
  0. Helpers first:
       spin_mul_self (b : Bool) : spin b * spin b = 1                                 R15
       sum_spin_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
         ∑ b : Bool, spin b * Real.exp (K * (s * spin b)) = 2 * Real.sinh K * s       R16, R17, R19, ring
  Induction on `n`.
  1. zero: `simp` with `energy`, `spin_mul_self`:                               R22, R23
  2. succ: `have h := snoc_split …` at `f := fun τ b => spin (τ 0) * spin b`;
     turn `Fin.castSucc 0` into `0` in `h`:                                      R20, R26
     rw [h], split the power, regroup, fold `ih`, factor into the sum:           R27, R12 (←), rw [← ih], R10
     compare the `τ`-terms:                                                      R9
     under the `b`-sum: pull `spin (τ 0)` out, apply `sum_spin_exp_bond`:        R28, ring
-/
-- MILESTONE (optional: change or delete)
/-- End-to-end numerator `∑_σ s₀ s_n e^{-βE}`. -/
theorem G_eq (β J : ℝ) (n : ℕ) :
    ∑ σ : Fin (n + 1) → Bool, spin (σ 0) * spin (σ (Fin.last n)) * Real.exp (-β * energy J σ) =
      2 * (2 * Real.sinh (β * J)) ^ n := by
  induction n with
  | zero => simp [energy, spin_mul_self]
  | succ n ih =>
    have h := snoc_split β J n (fun τ b => spin (τ 0) * spin b)
    simp only [Fin.castSucc_zero] at h
    rw [h, pow_succ, ← mul_assoc, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp_rw [mul_assoc (spin (τ 0)), ← Finset.mul_sum, sum_spin_exp_bond _ _ (spin_pm _)]
    ring

/- SKELETON · corr_succ   (uses sum_snoc)
  1. h1 : numerator over `Fin (n + 2) → Bool` = `2 * Real.cosh (β * J)` * numerator over
     `Fin (n + 1) → Bool`, TYPE WRITTEN OUT (cheatsheet Traps), proved by `sum_snoc` at
     `g := fun τ => spin (τ 0) * spin (τ ⟨r, by omega⟩)`:                       R20
  2. h2 : the same for the weights alone, `sum_snoc` at `g := fun _ => 1`:       R20, R24
  3. hc : 2 * Real.cosh (β * J) ≠ 0                                              R29
  4. unfold both `corr`, rw [h1], unfold `Z`, rw [h2], fold `Z`, cancel `hc`:    R25, R30
-/
-- MILESTONE (optional: change or delete)
theorem corr_succ (β J : ℝ) (n r : ℕ) (hr : r ≤ n) :
    corr β J (n + 1) r (by omega) = corr β J n r hr := by
  have h1 : ∑ σ : Fin (n + 2) → Bool,
      spin (σ 0) * spin (σ ⟨r, by omega⟩) * Real.exp (-β * energy J σ) =
      2 * Real.cosh (β * J) * ∑ σ : Fin (n + 1) → Bool,
        spin (σ 0) * spin (σ ⟨r, by omega⟩) * Real.exp (-β * energy J σ) :=
    sum_snoc β J n (fun τ => spin (τ 0) * spin (τ ⟨r, by omega⟩))
  have h2 := sum_snoc β J n (fun _ => 1)
  simp only [one_mul] at h2
  have hc : 2 * Real.cosh (β * J) ≠ 0 := by positivity
  rw [corr, corr, h1, Z, h2, ← Z, mul_div_mul_left _ _ hc]

/- SKELETON · corr_eq
  Prove the milestones above first, in order (each has its own SKELETON):
    snoc_split   sum out the last spin                   used by sum_snoc, G_eq
    sum_snoc     appending a spin gives `2 cosh βJ`       used by Z_eq, corr_succ
    Z_eq         `Z = 2 (2 cosh βJ)^n`                    used in step 2
    G_eq         end-to-end numerator `2 (2 sinh βJ)^n`   used in step 2
    corr_succ    `corr` does not depend on `n`            used in step 3
  1. Induction on `n` starting at `n = r` (`with | base => … | succ n hrn ih => …`):   R31
  2. base: rw [corr], make the site `⟨r, _⟩` into `Fin.last r`:                       R32
     rw [G_eq, Z_eq], write `tanh` as `sinh / cosh`, split the power:                R33, R34
     hc : 0 < Real.cosh (β * J), clear the denominators, finish:                     R35, R36, ring
  3. succ: rw [corr_succ β J n r hrn, ih]
-/
-- BEGIN SPEC
theorem corr_eq (β J : ℝ) (n r : ℕ) (hr : r ≤ n) :
    corr β J n r hr = Real.tanh (β * J) ^ r :=
-- END SPEC
  by
    induction n, hr using Nat.le_induction with
    | base =>
      rw [corr, show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl, G_eq, Z_eq,
        Real.tanh_eq_sinh_div_cosh, div_pow]
      have hc : 0 < Real.cosh (β * J) := Real.cosh_pos _
      field_simp
      ring
    | succ n hrn ih => rw [corr_succ β J n r hrn, ih]

end H096

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two facts: adding spins beyond site `r` multiplies numerator and `Z` by the same `2 cosh βJ`
    (`corr_succ`: `corr` does not depend on `n`), and at `n = r` the numerator is `2 (2 sinh βJ)^r` while
    `Z = 2 (2 cosh βJ)^r` (`G_eq`, `Z_eq`). Both rest on one move, `snoc_split`: a chain of `n + 2` spins
    is a chain of `n + 1` spins plus one appended spin `b`, whose bond contributes `e^{βJ s_n b}`.
H2. `snoc_split`: first state and prove a helper `energy_snoc (J : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool)
    (b : Bool) : energy J (Fin.snoc σ b : Fin (n + 2) → Bool) = energy J σ - J * (spin (σ (Fin.last n)) * spin b)`
    (recipe in H3). Then `rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`,
    compare terms with `Finset.sum_congr`, `show` the `Fin.snoc τ b` form and use `Fin.snoc_castSucc`,
    `Fin.snoc_last`, `energy_snoc`, `Real.exp_add`. The inner `∑ b : Bool` is `2 cosh K` or `2 sinh K · s`
    once `s = spin (τ (Fin.last n))` is known to be `±1` (`rcases hs with rfl | rfl <;> simp [spin, Real.cosh_eq] <;> ring`).
    `Z_eq`, `G_eq`: induction on `n`, with `have h := sum_snoc β J n (fun _ => 1)` resp.
    `have h := snoc_split β J n (fun τ b => spin (τ 0) * spin b)` in the step.
H3. `energy_snoc`: `simp only [energy, Fin.sum_univ_castSucc]` then
    `simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]; ring`.
    Main: `induction n, hr using Nat.le_induction with | base => _ | succ n hrn ih => _`;
    base: `rw [corr, show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl, G_eq, Z_eq,
    Real.tanh_eq_sinh_div_cosh, div_pow]`; `have hc : 0 < Real.cosh (β * J) := Real.cosh_pos _`;
    `field_simp; ring`; step: `rw [corr_succ β J n r hrn, ih]`.
-/
