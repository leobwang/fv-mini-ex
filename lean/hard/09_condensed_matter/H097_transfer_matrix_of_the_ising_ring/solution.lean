/- H097 | Transfer matrix of the Ising ring | 1.5-2 h | Matrix powers, path sums, trace, Fin.consEquiv, Real.exp_sum, mathlib
GOAL
  Ring of `n + 1` spins `s_i = spin (σ i) = ±1`, bonds `i — i+1` and the closing bond `n — 0`, field `h`:
  `E(σ) = -J (∑_{i<n} s_i s_{i+1} + s_n s_0) - h ∑_i s_i`. With the transfer matrix (rows and columns
  indexed by spin values `Bool`) `T a b = exp(β (J s_a s_b + h (s_a + s_b)/2))`, prove
  `Z = Matrix.trace (T^(n+1))` (trace = sum of diagonal entries). (At `h = 0` the eigenvalues of `T` are
  `λ₊ = 2 cosh βJ` and `λ₋ = 2 sinh βJ`, so `Z = λ₊^(n+1) + λ₋^(n+1)`; see M166.)

GUIDE
  Entries R1–R39: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · pow_apply_eq_sum   (milestone 1: prove it first; trace_pow_succ uses it)
  1. Induction on `n`, with `a` generalized (the step needs `ih` at another start spin):      R1
  2. zero: `M ^ 0` → `1` → an `if`:                                                           R2, R3
     reindex `∑ σ : Fin 1 → Bool` as a sum over `Bool` along `(Equiv.funUnique (Fin 1) Bool).symm`:
                                                                                               R4, R5
     split `a` and `b`, then `simp [Fin.last]` on all four goals:                              R6, R7
  3. succ: prove the path split of the right side first,
       hR : (∑ σ : Fin (n + 2) → Bool, if σ 0 = a ∧ σ (Fin.last (n + 1)) = b then
               ∏ i : Fin (n + 1), M (σ i.castSucc) (σ i.succ) else 0) =
            ∑ τ : Fin (n + 1) → Bool,
               if τ (Fin.last n) = b then M a (τ 0) * ∏ i : Fin n, M (τ i.castSucc) (τ i.succ) else 0
     proof: first spin + rest, sum over pairs, swap the two sums:                              R8, R9, R10
            go under `∑ τ`:                                                                     R11
            one `simp only` that evaluates `Fin.cons` and peels the first bond:          R12, R13, R14, R15
            collapse the sum over the first spin at `a`:                                       R16
              main goal and `case h₁`: `simp`; `case h₀`: `intro c _ hc`, then `simp [hc]`
  4. `rw [hR]`, then `M ^ (n + 1) = M * M ^ n` and the entry of the product:                   R17, R18
  5. `ih` under `∑ j`, then move `M a j` into the inner sum:                                   R19, R20
  6. swap the sums, go under `∑ τ`, collapse the sum over `j` at `j = τ 0`:                    R10, R11, R16
       main goal: split on `τ (Fin.last n) = b`, `simp` with it:                               R21
       other terms: `intro c _ hc`, `simp` with `hc` flipped:                                  R22
       `τ 0 ∉ Finset.univ` goal: `simp`
-/
-- MILESTONE (optional: change or delete)
/-- Path sum: `(M^n) a b` sums the products along all spin paths of length `n` from `a` to `b`. -/
theorem pow_apply_eq_sum (M : Matrix Bool Bool ℝ) (n : ℕ) (a b : Bool) :
    (M ^ n) a b = ∑ σ : Fin (n + 1) → Bool,
      if σ 0 = a ∧ σ (Fin.last n) = b then ∏ i : Fin n, M (σ i.castSucc) (σ i.succ) else 0 := by
  induction n generalizing a with
  | zero =>
    rw [pow_zero, Matrix.one_apply, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
    cases a <;> cases b <;> simp [Fin.last]
  | succ n ih =>
    -- Split each path of length `n + 1` into its first spin and the remaining path `τ`.
    have hR : (∑ σ : Fin (n + 2) → Bool,
        if σ 0 = a ∧ σ (Fin.last (n + 1)) = b then
          ∏ i : Fin (n + 1), M (σ i.castSucc) (σ i.succ) else 0) =
        ∑ τ : Fin (n + 1) → Bool,
          if τ (Fin.last n) = b then M a (τ 0) * ∏ i : Fin n, M (τ i.castSucc) (τ i.succ) else 0 := by
      rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Fin.consEquiv_apply, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ,
        Fin.prod_univ_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc
        simp [hc]
      · simp
    rw [hR, pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_eq_single (τ 0)]
    · by_cases hb : τ (Fin.last n) = b <;> simp [hb]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp

/- SKELETON · trace_pow_succ   (milestone 2: uses pow_apply_eq_sum; Zring_eq_trace uses it)
  1. trace → sum of the diagonal; `M ^ (n + 1) = M ^ n * M` (the last factor is the closing bond): R23, R24
  2. one `simp only`: diagonal entries, the product entry, `pow_apply_eq_sum`, `* M c a` into the sum:
                                                                                         R23, R18, R25
     the goal is now `∑ a, ∑ c, ∑ σ, (if σ 0 = a ∧ σ (Fin.last n) = c then … else 0) * M c a = ∑ σ, …`
  3. a three-step `calc` (pattern: W7). Bring `∑ σ` outside:
       step 1 `_ = ∑ a, ∑ σ, ∑ c, …` (write the summand out): swap under `∑ a`:      R11 with R10
       step 2 `_ = _`: swap the two outer sums:                                             R10
  4. step 3 `_ = _ := by …`, under `∑ σ`: push `* M c a` into the `if`, split the `∧`:     R11, R26, R27
     then `simp` collapses both sums:                                                           R28
-/
-- MILESTONE (optional: change or delete)
theorem trace_pow_succ (M : Matrix Bool Bool ℝ) (n : ℕ) :
    Matrix.trace (M ^ (n + 1)) = ∑ σ : Fin (n + 1) → Bool,
      (∏ i : Fin n, M (σ i.castSucc) (σ i.succ)) * M (σ (Fin.last n)) (σ 0) := by
  rw [Matrix.trace, pow_succ]
  simp only [Matrix.diag, Matrix.mul_apply, pow_apply_eq_sum, Finset.sum_mul]
  calc _ = ∑ a : Bool, ∑ σ : Fin (n + 1) → Bool, ∑ c : Bool,
        (if σ 0 = a ∧ σ (Fin.last n) = c then ∏ i : Fin n, M (σ i.castSucc) (σ i.succ) else 0) *
          M c a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [ite_mul, zero_mul, ite_and]
      simp

/- SKELETON · field_split   (milestone 3: weight_eq uses it)
  1. peel the last and the first term of `∑ i, spin (σ i)`, as facts `h1`, `h2`
     (with `f := fun i => spin (σ i)`):                                                         R29, R30
  2. one `simp only`: pull `/ 2` out of the sum, split it into two sums:                       R31, R32
  3. combine `h1`, `h2` linearly:                                                               R33
-/
-- MILESTONE (optional: change or delete)
/-- Share each site's field term between its two bonds. -/
theorem field_split {n : ℕ} (σ : Fin (n + 1) → Bool) :
    ∑ i, spin (σ i) = ∑ i : Fin n, (spin (σ i.castSucc) + spin (σ i.succ)) / 2
      + (spin (σ (Fin.last n)) + spin (σ 0)) / 2 := by
  have h1 := Fin.sum_univ_castSucc (fun i => spin (σ i))
  have h2 := Fin.sum_univ_succ (fun i => spin (σ i))
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

/- SKELETON · weight_eq   (milestone 4: uses field_split; Zring_eq_trace uses it)
  1. one `simp only`: unfold `transfer`, entries of `Matrix.of`, product of `exp`s → `exp` of a sum,
     `exp a * exp b` → `exp (a + b)`, unfold `ringEnergy`, rewrite with `field_split`:      R34, R35, R36
  2. strip `Real.exp` from both sides:                                                          R37
  3. distribute (`Finset.mul_sum` and the sign lemmas), then normalise every summand:      R20, R38, R39
  4. split the sums and pull the constants out of them
     (`Finset.sum_add_distrib`, `← Finset.sum_mul`, `← Finset.mul_sum`), then `ring`:     R32, R25, R20, R39
-/
-- MILESTONE (optional: change or delete)
theorem weight_eq (β J h : ℝ) {n : ℕ} (σ : Fin (n + 1) → Bool) :
    Real.exp (-β * ringEnergy J h σ) =
      (∏ i : Fin n, transfer β J h (σ i.castSucc) (σ i.succ)) * transfer β J h (σ (Fin.last n)) (σ 0) := by
  simp only [transfer, Matrix.of_apply, ← Real.exp_sum, ← Real.exp_add, ringEnergy, field_split]
  congr 1
  simp only [Finset.mul_sum, mul_add, mul_neg, neg_mul, sub_eq_add_neg]
  ring_nf
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/- SKELETON · Zring_eq_trace
  0. Prove the milestones first: pow_apply_eq_sum → trace_pow_succ (uses it), and
     field_split → weight_eq (uses it). This proof uses only trace_pow_succ and weight_eq.
  1. rewrite the trace with `trace_pow_succ`, unfold `Zring`:      rw [trace_pow_succ, Zring]
  2. both sides are `∑ σ, …`; rewrite with `weight_eq` under the binder:                        R19
-/
-- BEGIN SPEC
theorem Zring_eq_trace (β J h : ℝ) (n : ℕ) :
    Zring β J h n = Matrix.trace (transfer β J h ^ (n + 1)) :=
-- END SPEC
  by
    rw [trace_pow_succ, Zring]
    simp_rw [weight_eq]

end H097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two separate facts. A matrix identity: `(M^n) a b` is a sum over spin paths from `a` to `b` of the
    product of entries along the path (`pow_apply_eq_sum`), so `tr M^(n+1)` is the sum over closed paths
    (`trace_pow_succ`). A physics identity: after sharing each field term `h s_i` between its two bonds
    (`field_split`), the Boltzmann weight of `σ` is the product of `T` entries around the ring (`weight_eq`).
    The main theorem is then two rewrites.
H2. `pow_apply_eq_sum`: `induction n generalizing a` (R1). Base: R2, R3, reindex along
    `(Equiv.funUnique (Fin 1) Bool).symm` (R4, R5), `cases a <;> cases b <;> simp [Fin.last]`. Step: prove `hR`
    (skeleton) by reindexing along `Fin.consEquiv` (R8–R10), going under `∑ τ` (R11), evaluating `Fin.cons`
    (R12–R15), collapsing at `a` (R16); then `pow_succ'`, `Matrix.mul_apply`, `simp_rw [ih, Finset.mul_sum]`,
    swap, collapse at `τ 0`, `by_cases`. `trace_pow_succ`: `pow_succ`, Part 1, swap sums, `if` lemmas (R23–R28).
    `field_split`: R29, R30 as `have`s, R31, R32, `linarith`. `weight_eq`: R34–R39.
H3. `hR` proof start: `rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`,
    `refine Finset.sum_congr rfl fun τ _ => ?_`, `simp only [Fin.consEquiv_apply, Fin.cons_zero, ← Fin.succ_last,
    Fin.cons_succ, Fin.prod_univ_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]`, `rw [Finset.sum_eq_single a]`.
    `trace_pow_succ`: `rw [Matrix.trace, pow_succ]; simp only [Matrix.diag, Matrix.mul_apply, pow_apply_eq_sum,
    Finset.sum_mul]`, a `calc` with `Finset.sum_congr rfl fun a _ => Finset.sum_comm` and `Finset.sum_comm`,
    then `simp only [ite_mul, zero_mul, ite_and]; simp`. `field_split`: `have h1 := Fin.sum_univ_castSucc
    (fun i => spin (σ i))`, the same with `Fin.sum_univ_succ`, `simp only [← Finset.sum_div,
    Finset.sum_add_distrib]`, `linarith`. `weight_eq`: `simp only [transfer, Matrix.of_apply, ← Real.exp_sum,
    ← Real.exp_add, ringEnergy, field_split]`, `congr 1`, `simp only [Finset.mul_sum, mul_add, mul_neg, neg_mul,
    sub_eq_add_neg]`, `ring_nf`, `simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]`, `ring`.
    Main: `rw [trace_pow_succ, Zring]; simp_rw [weight_eq]`.
-/
