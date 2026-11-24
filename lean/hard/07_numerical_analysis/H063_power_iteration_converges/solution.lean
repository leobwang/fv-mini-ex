/- H063 | Power iteration converges | 1.5-2 h | Matrix, mulVec, dotProduct, eigenvectors, Rayleigh quotient, Filter.Tendsto, mathlib
GOAL
  Power iteration `xₙ₊₁ = A xₙ / ‖A xₙ‖`, `A` real symmetric 2×2 (vectors: `Fin 2 → ℝ`), unit eigenvectors
  `A u = μ₁ u`, `A v = μ₂ v`, `|μ₂| < |μ₁|`, start `x₀ = α u + β v`, `α ≠ 0`: the Rayleigh quotient
  `xₙᵀAxₙ / xₙᵀxₙ → μ₁` and `(u ⬝ᵥ xₙ)² → 1`, i.e. the unit vector `xₙ` lines up with `±u` (sign flips if `μ₁ < 0`).

GUIDE
  Entries R1–R54: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Filter Topology
open scoped Matrix

namespace H063

-- BEGIN SPEC
/-- the Rayleigh quotient `xᵀ A x / xᵀ x` -/
noncomputable def rayleigh (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

/-- power iteration: multiply by `A`, then rescale to Euclidean length `√(y ⬝ᵥ y) = 1` -/
noncomputable def powerIter (A : Matrix (Fin 2) (Fin 2) ℝ) (x₀ : Fin 2 → ℝ) : ℕ → (Fin 2 → ℝ)
  | 0 => x₀
  | n + 1 =>
    let y := A *ᵥ powerIter A x₀ n
    (√(y ⬝ᵥ y))⁻¹ • y
-- END SPEC

-- MILESTONE (optional: change or delete)
-- eigenvectors of a symmetric matrix for different eigenvalues are orthogonal
/- SKELETON · eigvec_orthogonal
  1. The symmetry fact   h : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v
       move A onto the left factor, as a row vector, then back with the transpose:
                                                                    R1 → R2 → rw [hA]
  2. Insert the eigen-equations in h and pull the scalars out:      R3 (rw [hu, hv] at h), R4, R5, R6, R6
       h now says  μ₂ * (u ⬝ᵥ v) = μ₁ * (u ⬝ᵥ v)   (printed `μ₂ * u ⬝ᵥ v = μ₁ * u ⬝ᵥ v`)
  3. have : (μ₁ - μ₂) * (u ⬝ᵥ v) = 0                                 R7
  4. One factor of a zero product is zero, and it is not μ₁ - μ₂:   R8, R10, R9
-/
theorem eigvec_orthogonal (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Aᵀ = A) (u v : Fin 2 → ℝ)
    (μ₁ μ₂ : ℝ) (hu : A *ᵥ u = μ₁ • u) (hv : A *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) : u ⬝ᵥ v = 0 := by
  have h : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]
  rw [hu, hv, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  have : (μ₁ - μ₂) * (u ⬝ᵥ v) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

-- MILESTONE (optional: change or delete)
-- dot products in an orthonormal basis
/- SKELETON · dot_comb
  1. The swapped orthogonality fact  hvu : v ⬝ᵥ u = 0               R11
  2. Split the ∧:                                                   constructor
  3. Each half: expand everything in one `simp only [...]` with the expansion lemmas
     AND the facts hu1, hv1, huv, hvu, then finish with `ring`:    R12, R4, R5, R6, ring
     (the second half needs only the right-hand expansions)
-/
theorem dot_comb (u v : Fin 2 → ℝ) (hu1 : u ⬝ᵥ u = 1) (hv1 : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (a b p q : ℝ) :
    (a • u + b • v) ⬝ᵥ (p • u + q • v) = a * p + b * q ∧ u ⬝ᵥ (p • u + q • v) = p := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  constructor
  · simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hu1, hv1, huv, hvu]
    ring
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hu1, huv]
    ring

-- MILESTONE (optional: change or delete)
-- up to a positive scale, the n-th iterate is `(α μ₁ⁿ) u + (β μ₂ⁿ) v`
/- SKELETON · powerIter_eq
  1. Induction on n:                                                R13
  2. zero: witness 1; unfold powerIter and simplify                 R20 (one_pos), R14 (`simp [powerIter]`)
  3. succ: take ih apart into c, hc, hx                             R15
     a. hy : A *ᵥ xₙ = c • ((α * μ₁ ^ (n + 1)) • u + (β * μ₂ ^ (n + 1)) • v)
          rw [hx], then push A inside and use hu, hv, merge scalars:
                                                    R16, R17, R16, R16, rw [hu, hv], R18, R18
          goal now  c • ((α * μ₁ ^ n * μ₁) • u + …) = c • ((α * μ₁ ^ (n + 1)) • u + …)
          match the exponents:                                      R19, then `<;> ring_nf`
     b. hpos : 0 < (A *ᵥ xₙ) ⬝ᵥ (A *ᵥ xₙ)
          rw [hy], scalars out, MILESTONE dot_comb (.1), then R6:   R4, R5, dot_comb, R6
          the scalar α * μ₁ ^ (n + 1) is nonzero:                   R21
          positivity of c * (c * (a * a + b * b)):                  R20, R20, R23, R22
     c. set y := A *ᵥ xₙ  WITHOUT `with hy` (the name hy is taken):  R24
          set also turns hy into  hy : y = c • (…), and hpos into  0 < y ⬝ᵥ y
        witness:  refine ⟨(√(y ⬝ᵥ y))⁻¹ * c, ?_, ?_⟩
          its positivity:                                           R20, R25 (with hpos), hc
          unfold one step, split the witness, fold back into y:     R14, R26, rw [← hy]
          (rw closes the goal by rfl: y is by definition A *ᵥ xₙ)
-/
theorem powerIter_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) (μ₁ μ₂ : ℝ)
    (hu : A *ᵥ u = μ₁ • u) (hv : A *ᵥ v = μ₂ • v) (hu1 : u ⬝ᵥ u = 1) (hv1 : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) (hμ : μ₁ ≠ 0) (α β : ℝ) (hα : α ≠ 0) (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ powerIter A (α • u + β • v) n = c • ((α * μ₁ ^ n) • u + (β * μ₂ ^ n) • v) := by
  induction n with
  | zero => exact ⟨1, one_pos, by simp [powerIter]⟩
  | succ n ih =>
    obtain ⟨c, hc, hx⟩ := ih
    have hy : A *ᵥ powerIter A (α • u + β • v) n
        = c • ((α * μ₁ ^ (n + 1)) • u + (β * μ₂ ^ (n + 1)) • v) := by
      rw [hx, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hv,
        smul_smul, smul_smul]
      congr 2 <;> ring_nf
    have hpos : 0 < (A *ᵥ powerIter A (α • u + β • v) n) ⬝ᵥ (A *ᵥ powerIter A (α • u + β • v) n) := by
      rw [hy, dotProduct_smul, smul_dotProduct, (dot_comb u v hu1 hv1 huv _ _ _ _).1, smul_eq_mul,
        smul_eq_mul]
      have : α * μ₁ ^ (n + 1) ≠ 0 := mul_ne_zero hα (pow_ne_zero _ hμ)
      exact mul_pos hc
        (mul_pos hc (add_pos_of_pos_of_nonneg (mul_self_pos.mpr this) (mul_self_nonneg _)))
    set y := A *ᵥ powerIter A (α • u + β • v) n
    refine ⟨(√(y ⬝ᵥ y))⁻¹ * c, mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hpos)) hc, ?_⟩
    simp only [powerIter]
    rw [mul_smul, ← hy]

-- MILESTONE (optional: change or delete)
-- after one step the iterate is a unit vector (or 0, if `A` killed it)
/- SKELETON · normalized
  1. Unfold one step and name y := A *ᵥ powerIter A x₀ n:           R14, R24
  2. Scalars out of both factors:                                   R4, R5, R6, R6
       goal: s * (s * (y ⬝ᵥ y)) = 0 ∨ … = 1  with s = (√(y ⬝ᵥ y))⁻¹
  3. Split on the sign of y ⬝ᵥ y:                                   R27
  4. y ⬝ᵥ y ≤ 0: the left side; √ is 0, so s is 0:                  R28, R29, R30
  5. y ⬝ᵥ y > 0: the right side; regroup, merge inverses, cancel:  R28, R31, R32, R33, R34
-/
theorem normalized (A : Matrix (Fin 2) (Fin 2) ℝ) (x₀ : Fin 2 → ℝ) (n : ℕ) :
    powerIter A x₀ (n + 1) ⬝ᵥ powerIter A x₀ (n + 1) = 0 ∨
      powerIter A x₀ (n + 1) ⬝ᵥ powerIter A x₀ (n + 1) = 1 := by
  simp only [powerIter]
  set y := A *ᵥ powerIter A x₀ n
  rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  rcases le_or_gt (y ⬝ᵥ y) 0 with h | h
  · left
    rw [Real.sqrt_eq_zero'.mpr h, inv_zero, zero_mul]
  · right
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt h.le, inv_mul_cancel₀ h.ne']

-- MILESTONE (optional: change or delete)
-- the squared ratio of the two components decays like `(μ₂ / μ₁)^(2n)`
/- SKELETON · ratio_tendsto
  1. hμ : μ₁ ≠ 0  (if μ₁ = 0 then |μ₂| < 0):                       R35, R36
  2. hr : (μ₂ / μ₁) ^ 2 < 1                                         R37, R38 with R39, R40
  3. h : the geometric sequence ((μ₂ / μ₁) ^ 2) ^ n → 0, times (β / α) ^ 2:
                                                      R41 (side goal R39), R42, R3 (rw [mul_zero] at h)
  4. Transfer to the target pointwise:                              R43
     per n, rewrite the target into h's form:
                    R37 (←), R44, R37 (←), R45 (mul_pow, then ← pow_mul twice), mul_comm n 2
-/
theorem ratio_tendsto (μ₁ μ₂ α β : ℝ) (hgap : |μ₂| < |μ₁|) :
    Tendsto (fun n : ℕ => (β * μ₂ ^ n) ^ 2 / (α * μ₁ ^ n) ^ 2) atTop (𝓝 0) := by
  have hμ : μ₁ ≠ 0 := by
    rintro rfl
    rw [abs_zero] at hgap
    linarith [abs_nonneg μ₂]
  have hr : (μ₂ / μ₁) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    exact sq_lt_sq.mpr hgap
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).const_mul ((β / α) ^ 2)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [← div_pow, mul_div_mul_comm, ← div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]

/- SKELETON · power_iteration
  Prove the five MILESTONE lemmas above first; this proof only combines them.
  1. Facts:  hμ : μ₁ ≠ 0                                            R35, R36
             hne : μ₁ ≠ μ₂                                          R35, R46
             huv : u ⬝ᵥ v = 0                                       MILESTONE eigvec_orthogonal
  2. Name the ratio sequence and get its limit:
       set t := fun n : ℕ => (β * μ₂ ^ n) ^ 2 / (α * μ₁ ^ n) ^ 2 with ht_def        R24
       ht : Tendsto t atTop (𝓝 0)                                   MILESTONE ratio_tendsto
       ha : ∀ n, α * μ₁ ^ n ≠ 0                                     R21
  3. hR : ∀ n, rayleigh A xₙ = (μ₁ + t n * μ₂) / (1 + t n)
       xₙ = c • z from MILESTONE powerIter_eq:                      R15
       hAz : A *ᵥ z = (α * μ₁ ^ n * μ₁) • u + (β * μ₂ ^ n * μ₂) • v    (z = (α * μ₁ ^ n) • u + …)
                                                                    R17, R16, R16, rw [hu, hv], R18, R18
       rw [rayleigh] (unfolds it), rw [hx], R16, rw [hAz],
         R4 then R5 in each of the two dot products, MILESTONE dot_comb (.1) twice
       simp only [smul_eq_mul, ht_def] (R6), put `ha n` in the context (have),
         then field_simp closes the goal:                           R47
  4. hC : ∀ n, (u ⬝ᵥ xₙ₊₁) ^ 2 = 1 / (1 + t (n + 1))
       powerIter_eq at n + 1 (R15); name a := α * μ₁ ^ (n + 1), b := β * μ₂ ^ (n + 1) (R24)
       hdot : MILESTONE normalized at n
       rewrite hdot with hx, R4, R5, dot_comb (.1):                 R3, R4, R5
       rewrite the goal with hx, R4, dot_comb (.2):                 R4
       simp only [smul_eq_mul, ht_def] at hdot ⊢                    R6
         hdot : c * (c * (a * a + b * b)) = 0 ∨ c * (c * (a * a + b * b)) = 1
         ⊢ (c * a) ^ 2 = 1 / (1 + (β * μ₂ ^ (n + 1)) ^ 2 / (α * μ₁ ^ (n + 1)) ^ 2)
       ha' : a ≠ 0 from ha (n + 1);  hpos : 0 < c * (c * (a * a + b * b)):  R20, R20, R23, R22
       split hdot with rcases (as in R27):  rcases hdot with h0 | h1
       case h0 (= 0): contradicts hpos                              R7
       case h1 (= 1): fact  h : (c * a) ^ 2 * (1 + b ^ 2 / a ^ 2) = c * (c * (a * a + b * b))
                      by R47; then R48 (side goal R39), rw [h, h1]
                      (`rw [h]` matches: a, b are abbreviations of the printed terms)
  5. Split the ∧ (constructor). Each limit:
       a. build (μ₁ + t n * μ₂) / (1 + t n) → (μ₁ + 0 * μ₂) / (1 + 0):  R49, R51, R50, R49, R50, R52
          normalise its limit: simp only [zero_mul, add_zero, div_one] at h; then R43 with hR
       b. start from index 1:                                       R53
          build 1 / (1 + t (n + 1)) → 1 / (1 + 0):                  R49, R49, R54, R50, R52
          normalise: simp only [add_zero, div_one] at h; then R43 with hC
-/
-- BEGIN SPEC
theorem power_iteration (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Aᵀ = A)
    (u v : Fin 2 → ℝ) (μ₁ μ₂ : ℝ) (hu : A *ᵥ u = μ₁ • u) (hv : A *ᵥ v = μ₂ • v)
    (hu1 : u ⬝ᵥ u = 1) (hv1 : v ⬝ᵥ v = 1) (hgap : |μ₂| < |μ₁|) (α β : ℝ) (hα : α ≠ 0) :
    Tendsto (fun n => rayleigh A (powerIter A (α • u + β • v) n)) atTop (𝓝 μ₁) ∧
      Tendsto (fun n => (u ⬝ᵥ powerIter A (α • u + β • v) n) ^ 2) atTop (𝓝 1) :=
-- END SPEC
  by
    have hμ : μ₁ ≠ 0 := by
      rintro rfl
      rw [abs_zero] at hgap
      linarith [abs_nonneg μ₂]
    have hne : μ₁ ≠ μ₂ := by
      rintro rfl
      exact lt_irrefl _ hgap
    have huv := eigvec_orthogonal A hA u v μ₁ μ₂ hu hv hne
    set t := fun n : ℕ => (β * μ₂ ^ n) ^ 2 / (α * μ₁ ^ n) ^ 2 with ht_def
    have ht : Tendsto t atTop (𝓝 0) := ratio_tendsto μ₁ μ₂ α β hgap
    have ha : ∀ n : ℕ, α * μ₁ ^ n ≠ 0 := fun n => mul_ne_zero hα (pow_ne_zero _ hμ)
    have hR : ∀ n, rayleigh A (powerIter A (α • u + β • v) n) = (μ₁ + t n * μ₂) / (1 + t n) := by
      intro n
      obtain ⟨c, hc, hx⟩ := powerIter_eq A u v μ₁ μ₂ hu hv hu1 hv1 huv hμ α β hα n
      have hAz : A *ᵥ ((α * μ₁ ^ n) • u + (β * μ₂ ^ n) • v)
          = (α * μ₁ ^ n * μ₁) • u + (β * μ₂ ^ n * μ₂) • v := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hv, smul_smul, smul_smul]
      rw [rayleigh, hx, Matrix.mulVec_smul, hAz, dotProduct_smul, smul_dotProduct, dotProduct_smul,
        smul_dotProduct, (dot_comb u v hu1 hv1 huv _ _ _ _).1, (dot_comb u v hu1 hv1 huv _ _ _ _).1]
      simp only [smul_eq_mul, ht_def]
      have := ha n
      field_simp
    have hC : ∀ n, (u ⬝ᵥ powerIter A (α • u + β • v) (n + 1)) ^ 2 = 1 / (1 + t (n + 1)) := by
      intro n
      obtain ⟨c, hc, hx⟩ := powerIter_eq A u v μ₁ μ₂ hu hv hu1 hv1 huv hμ α β hα (n + 1)
      set a := α * μ₁ ^ (n + 1)
      set b := β * μ₂ ^ (n + 1)
      have hdot := normalized A (α • u + β • v) n
      rw [hx, dotProduct_smul, smul_dotProduct, (dot_comb u v hu1 hv1 huv a b a b).1] at hdot
      rw [hx, dotProduct_smul, (dot_comb u v hu1 hv1 huv a b a b).2]
      simp only [smul_eq_mul, ht_def] at hdot ⊢
      have ha' : a ≠ 0 := ha (n + 1)
      have hpos : 0 < c * (c * (a * a + b * b)) :=
        mul_pos hc (mul_pos hc (add_pos_of_pos_of_nonneg (mul_self_pos.mpr ha') (mul_self_nonneg _)))
      rcases hdot with h0 | h1
      · linarith
      · have h : (c * a) ^ 2 * (1 + b ^ 2 / a ^ 2) = c * (c * (a * a + b * b)) := by
          field_simp
        rw [eq_div_iff (by positivity), h, h1]
    constructor
    · have h := (tendsto_const_nhds (x := μ₁)).add (ht.mul_const μ₂) |>.div
        ((tendsto_const_nhds (x := (1 : ℝ))).add ht) (by norm_num)
      simp only [zero_mul, add_zero, div_one] at h
      exact h.congr fun n => (hR n).symm
    · rw [← tendsto_add_atTop_iff_nat 1]
      have h := (tendsto_const_nhds (x := (1 : ℝ))).div
        ((tendsto_const_nhds (x := (1 : ℝ))).add (ht.comp (tendsto_add_atTop_nat 1))) (by norm_num)
      simp only [add_zero, div_one] at h
      exact h.congr fun n => (hC n).symm

end H063

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work in the eigenbasis. Up to a positive factor `c`, `xₙ = aₙ • u + bₙ • v` with `aₙ = α μ₁ⁿ`,
    `bₙ = β μ₂ⁿ` (powerIter_eq), and both targets depend only on `tₙ = bₙ² / aₙ²`, which tends to 0
    because `|μ₂ / μ₁| < 1` (ratio_tendsto). Prove the milestones in file order.
H2. Symmetry gives `u ⬝ᵥ v = 0` (compare `u ⬝ᵥ (A *ᵥ v)` with `(A *ᵥ u) ⬝ᵥ v`, R1–R2), so every dot
    product is `a * p + b * q` (dot_comb). Then `rayleigh A xₙ = (μ₁ + tₙ μ₂) / (1 + tₙ)` (`c` cancels,
    R47), and for `n ≥ 1`, `xₙ ⬝ᵥ xₙ = 1` (normalized) gives `(u ⬝ᵥ xₙ)² = 1 / (1 + tₙ)`. Pass to the
    limit with R49–R52 from `t → 0` and transfer it pointwise with R43; shift the second one with R53.
H3. Orthogonality: `rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]`. In the step of
    `powerIter_eq`, with `y := A *ᵥ xₙ`, use the witness `(√(y ⬝ᵥ y))⁻¹ * c` and finish with
    `rw [mul_smul, ← hy]`. First limit:
    `have h := (tendsto_const_nhds (x := μ₁)).add (ht.mul_const μ₂) |>.div ((tendsto_const_nhds (x := (1 : ℝ))).add ht) (by norm_num)`,
    then `simp only [zero_mul, add_zero, div_one] at h` and `exact h.congr fun n => (hR n).symm`.
    Second: `rw [← tendsto_add_atTop_iff_nat 1]`, and use `ht.comp (tendsto_add_atTop_nat 1)` for `t (n + 1)`.
-/
