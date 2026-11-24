/- H095 | Open Ising chain partition function | 45-75 min | Fin.cons, Equiv.sum_comp, induction, cosh, mathlib
GOAL
  An open chain of `n + 1` Ising spins `s_i = spin (σ i) = ±1` (sites `0 … n`) has zero-field energy
  `E(σ) = -J ∑_{i<n} s_i s_{i+1}`. Its partition function `Z = ∑_σ exp(-β E(σ))` (all `2^(n+1)`
  configurations) equals `2 (2 cosh βJ)^n`. Prove it by summing out spin 0 and inducting on `n`.

REFERENCE
  #check Fin.consEquiv      -- (α : Fin (n+1) → Type*) : α 0 × (∀ i, α i.succ) ≃ ∀ i, α i
  #check Equiv.sum_comp     -- (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ i, g i   (reindex)
  #check Fintype.sum_prod_type  -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)
  #check Finset.sum_comm    -- ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
  #check Fin.sum_univ_succ  -- ∑ i : Fin (n+1), f i = f 0 + ∑ i : Fin n, f i.succ
  #check Fin.cons_succ      -- Fin.cons x p i.succ = p i   (also Fin.cons_zero : Fin.cons x p 0 = x)
  #check Fin.succ_castSucc  -- i.castSucc.succ = i.succ.castSucc   (often used as `← Fin.succ_castSucc`)
  #check Finset.sum_mul     -- (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a   (Finset.mul_sum: a * ∑ ...)
  example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := Real.exp_add x y
  #check Real.cosh_eq       -- cosh x = (exp x + exp (-x)) / 2
  -- `rw [Z, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]` : sum over (spin 0, rest)
NOTE: `i.castSucc` / `i.succ` send `i : Fin n` to sites `i` / `i + 1` of `Fin (n + 1)`.
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

-- MILESTONE (optional: change or delete)
theorem spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

-- MILESTONE (optional: change or delete)
theorem energy_cons (J : ℝ) {n : ℕ} (a : Bool) (σ : Fin (n + 1) → Bool) :
    energy J (Fin.cons a σ : Fin (n + 2) → Bool) = -J * (spin a * spin (σ 0)) + energy J σ := by
  simp only [energy, Fin.sum_univ_succ]
  -- WHY: bond `i+1` of the longer chain reads `σ (i.castSucc.succ)`; `← Fin.succ_castSucc` makes it `Fin.cons _ _ (_.succ)`.
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
  ring

-- MILESTONE (optional: change or delete)
theorem sum_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∑ a : Bool, Real.exp (K * (spin a * s)) = 2 * Real.cosh K := by
  rcases hs with rfl | rfl <;> simp [spin, Real.cosh_eq] <;> ring

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
H1. A configuration of `n + 2` spins is a pair (spin 0, the other `n + 1` spins); spin 0 only touches
    the bond to its neighbour, so `exp(-βE)` factors as `exp(βJ s_a s_{σ 0}) * exp(-β E(σ))`.
H2. `induction n`. In the step, reindex along `Fin.consEquiv`, swap the sums so `∑ a : Bool` is inside,
    pull the `σ`-only factor out with `← Finset.sum_mul`, and evaluate `∑ a` with `sum_exp_bond`.
H3. `energy_cons`: `simp only [energy, Fin.sum_univ_succ]`, then
    `simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]; ring`.
    Step: `rw [Z, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`;
    inside, `show Real.exp (-β * energy J (Fin.cons a σ : Fin (n + 2) → Bool)) = _` exposes `Fin.cons`.
-/
