/- H063 | Power iteration converges | 1.5-2 h | Matrix, mulVec, dotProduct, eigenvectors, Rayleigh quotient, Filter.Tendsto, mathlib
GOAL
  Power iteration `xₙ₊₁ = A xₙ / ‖A xₙ‖`, `A` real symmetric 2×2 (vectors: `Fin 2 → ℝ`), unit eigenvectors
  `A u = μ₁ u`, `A v = μ₂ v`, `|μ₂| < |μ₁|`, start `x₀ = α u + β v`, `α ≠ 0`: the Rayleigh quotient
  `xₙᵀAxₙ / xₙᵀxₙ → μ₁` and `(u ⬝ᵥ xₙ)² → 1`, i.e. the unit vector `xₙ` lines up with `±u` (sign flips if `μ₁ < 0`).

REFERENCE
  -- `A *ᵥ x` matrix·vector, `x ⬝ᵥ y` dot product, `c • x` scalar·vector, `Aᵀ` transpose (`open scoped Matrix`)
  #check Matrix.dotProduct_mulVec  -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w    (`v ᵥ* A` is the row vector vᵀA)
  #check Matrix.mulVec_transpose   -- Aᵀ *ᵥ x = x ᵥ* A
  #check Matrix.mulVec_add         -- A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y    (also `Matrix.mulVec_smul`)
  #check dotProduct_add            -- u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w    (also `add_dotProduct`)
  #check dotProduct_smul           -- v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)   (also `smul_dotProduct`, `smul_smul`, `smul_eq_mul`)
  #check Real.mul_self_sqrt        -- 0 ≤ a → √a * √a = a    (and `Real.sqrt_eq_zero' : √a = 0 ↔ a ≤ 0`)
  #check sq_lt_sq                  -- a ^ 2 < b ^ 2 ↔ |a| < |b|
  #check tendsto_pow_atTop_nhds_zero_of_lt_one  -- 0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  example (f g : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) (hb : b ≠ 0) :
      Tendsto (fun n => f n / g n) atTop (𝓝 (a / b)) := hf.div hg hb   -- also `.add`, `.mul_const`, `.congr`
  #check tendsto_add_atTop_iff_nat -- (k : ℕ) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l
NOTE: symmetry is needed only for `u ⬝ᵥ v = 0`. Every `x₀` is some `α u + β v` (`u, v` form a basis).
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
theorem eigvec_orthogonal (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Aᵀ = A) (u v : Fin 2 → ℝ)
    (μ₁ μ₂ : ℝ) (hu : A *ᵥ u = μ₁ • u) (hv : A *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) : u ⬝ᵥ v = 0 := by
  have h : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]
  rw [hu, hv, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  have : (μ₁ - μ₂) * (u ⬝ᵥ v) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

-- MILESTONE (optional: change or delete)
-- dot products in an orthonormal basis
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
H1. Work in the eigenbasis. Up to a positive factor, `xₙ = aₙ u + bₙ v` with `aₙ = α μ₁ⁿ`, `bₙ = β μ₂ⁿ`, and
    both target quantities depend only on `tₙ = bₙ² / aₙ²`, which tends to 0 because `|μ₂ / μ₁| < 1`.
H2. Symmetry gives `u ⬝ᵥ v = 0` (compare `u ⬝ᵥ (A *ᵥ v)` with `(A *ᵥ u) ⬝ᵥ v`), so every dot product is
    `a p + b q`. Then `rayleigh A xₙ = (μ₁ + tₙ μ₂) / (1 + tₙ)` (the positive factor cancels), and for
    `n ≥ 1`, `xₙ ⬝ᵥ xₙ = 1` gives `(u ⬝ᵥ xₙ)² = 1 / (1 + tₙ)`. Pass to the limit with `t → 0`.
H3. Orthogonality: `rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]`. In the step of
    `powerIter_eq`, with `y := A *ᵥ xₙ`, use the witness `(√(y ⬝ᵥ y))⁻¹ * c` (`mul_smul`). Limits:
    `have h := (tendsto_const_nhds.add (ht.mul_const μ₂)).div (tendsto_const_nhds.add ht) (by norm_num)`;
    its limit reads `(μ₁ + 0 * μ₂) / (1 + 0)`, so normalise it first with
    `simp only [zero_mul, add_zero, div_one] at h`, then `exact h.congr ...`. Use
    `rw [← tendsto_add_atTop_iff_nat 1]` first for the second claim (it needs `n ≥ 1`).
-/
