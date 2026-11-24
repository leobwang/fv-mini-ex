/- H097 | Transfer matrix of the Ising ring | 1.5-2 h | Matrix powers, path sums, trace, Fin.consEquiv, Real.exp_sum, mathlib
GOAL
  Ring of `n + 1` spins `s_i = spin (σ i) = ±1`, bonds `i — i+1` and the closing bond `n — 0`, field `h`:
  `E(σ) = -J (∑_{i<n} s_i s_{i+1} + s_n s_0) - h ∑_i s_i`. With the transfer matrix (rows and columns
  indexed by spin values `Bool`) `T a b = exp(β (J s_a s_b + h (s_a + s_b)/2))`, prove
  `Z = Matrix.trace (T^(n+1))` (trace = sum of diagonal entries). (At `h = 0` the eigenvalues of `T` are
  `λ₊ = 2 cosh βJ` and `λ₋ = 2 sinh βJ`, so `Z = λ₊^(n+1) + λ₋^(n+1)`; see M166.)

REFERENCE
  #check Matrix.mul_apply   -- (M * N) i k = ∑ j, M i j * N j k
  #check pow_succ'          -- a ^ (n + 1) = a * a ^ n      (pow_succ : a ^ (n + 1) = a ^ n * a)
  example (M : Matrix Bool Bool ℝ) : M.trace = ∑ i, M i i := rfl   -- `rw [Matrix.trace]`, `Matrix.diag`
  #check Matrix.of_apply    -- Matrix.of f i j = f i j   (Matrix.one_apply: (1 : Matrix _ _ _) i j = if i = j then 1 else 0)
  #check Fin.consEquiv      -- (α : Fin (n+1) → Type*) : α 0 × (∀ i, α i.succ) ≃ ∀ i, α i
  #check Equiv.funUnique    -- (α β) [Unique α] : (α → β) ≃ β     (e.g. `Fin 1 → Bool` ≃ `Bool`)
  #check Finset.sum_eq_single  -- a → (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s → f a = 0) → ∑ x ∈ s, f x = f a
  #check Fin.prod_univ_succ -- ∏ i : Fin (n+1), f i = f 0 * ∏ i : Fin n, f i.succ   (Fin.sum_univ_succ, _castSucc)
  #check Real.exp_sum       -- exp (∑ x ∈ s, f x) = ∏ x ∈ s, exp (f x)    (Real.exp_add for two terms)
  #check ite_and            -- (if P ∧ Q then a else b) = if P then (if Q then a else b) else b
  #check Finset.sum_comm    -- ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y   (Fintype.sum_prod_type)
  #check Finset.sum_div     -- (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a   (Finset.sum_add_distrib splits ∑ (f + g))
NOTE: for `i : Fin n`, `i.castSucc` / `i.succ` are sites `i` / `i+1` of `Fin (n+1)`; `Fin.last n` is site `n` (the bond `n — 0` closes the ring).
-/
import Mathlib

namespace H097

-- BEGIN SPEC
/-- Spin value of an up (`true`) / down (`false`) site. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Energy of a ring of `n + 1` spins: bonds `i — i+1` for `i < n`, the closing bond `n — 0`,
and a uniform field `h`. -/
noncomputable def ringEnergy (J h : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) : ℝ :=
  -J * (∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ) + spin (σ (Fin.last n)) * spin (σ 0))
    - h * ∑ i, spin (σ i)

/-- Partition function of the ring. -/
noncomputable def Zring (β J h : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : Fin (n + 1) → Bool, Real.exp (-β * ringEnergy J h σ)

/-- The (symmetric) transfer matrix, indexed by spin values. -/
noncomputable def transfer (β J h : ℝ) : Matrix Bool Bool ℝ :=
  Matrix.of fun a b => Real.exp (β * (J * (spin a * spin b) + h * (spin a + spin b) / 2))
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- Path sum: `(M^n) a b` sums the products along all spin paths of length `n` from `a` to `b`. -/
theorem pow_apply_eq_sum (M : Matrix Bool Bool ℝ) (n : ℕ) (a b : Bool) :
    (M ^ n) a b = ∑ σ : Fin (n + 1) → Bool,
      if σ 0 = a ∧ σ (Fin.last n) = b then ∏ i : Fin n, M (σ i.castSucc) (σ i.succ) else 0 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem trace_pow_succ (M : Matrix Bool Bool ℝ) (n : ℕ) :
    Matrix.trace (M ^ (n + 1)) = ∑ σ : Fin (n + 1) → Bool,
      (∏ i : Fin n, M (σ i.castSucc) (σ i.succ)) * M (σ (Fin.last n)) (σ 0) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Share each site's field term between its two bonds. -/
theorem field_split {n : ℕ} (σ : Fin (n + 1) → Bool) :
    ∑ i, spin (σ i) = ∑ i : Fin n, (spin (σ i.castSucc) + spin (σ i.succ)) / 2
      + (spin (σ (Fin.last n)) + spin (σ 0)) / 2 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem weight_eq (β J h : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) :
    Real.exp (-β * ringEnergy J h σ) =
      (∏ i : Fin n, transfer β J h (σ i.castSucc) (σ i.succ)) * transfer β J h (σ (Fin.last n)) (σ 0) := by
  sorry

-- BEGIN SPEC
theorem Zring_eq_trace (β J h : ℝ) (n : ℕ) :
    Zring β J h n = Matrix.trace (transfer β J h ^ (n + 1)) :=
-- END SPEC
  sorry

end H097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two separate facts: a pure matrix identity (`tr M^(n+1)` is a sum over closed spin paths of the
    product of entries along the path), and a physics identity (the Boltzmann weight of `σ` is the
    product of `T` entries along the ring, after sharing each field term `h s_i` between two bonds).
H2. `pow_apply_eq_sum` by `induction n generalizing a`: base via
    `← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp` and `cases a <;> cases b <;> simp [Fin.last]`;
    step via `pow_succ'`, `Matrix.mul_apply`, the IH, and reindexing the path sum along `Fin.consEquiv`
    (the first spin is forced to be `a`, so `Finset.sum_eq_single a` collapses `∑` over it).
    `field_split`: `have h1 := Fin.sum_univ_castSucc (fun i => spin (σ i))`, the same with `Fin.sum_univ_succ`,
    then `simp only [← Finset.sum_div, Finset.sum_add_distrib]` (split the sum of halves) and `linarith`.
H3. `trace_pow_succ`: `rw [Matrix.trace, pow_succ]; simp only [Matrix.diag, Matrix.mul_apply, pow_apply_eq_sum, Finset.sum_mul]`,
    swap sums to put `∑ σ` outside, then `simp only [ite_mul, zero_mul, ite_and]; simp`.
    `weight_eq`: `simp only [transfer, Matrix.of_apply, ← Real.exp_sum, ← Real.exp_add, ringEnergy, field_split]`,
    `congr 1`, then distribute (`Finset.mul_sum`, `Finset.sum_add_distrib`) and `ring`. Main: `rw [trace_pow_succ, Zring]; simp_rw [weight_eq]`.
-/
