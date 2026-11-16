/- H074 | Least squares and the normal equations | 45-75 min | Matrix, dotProduct, transpose, quadratic expansion, optimality, mathlib
GOAL
  For a real m×n matrix `A` and `b : ℝᵐ`, `x` minimises the squared residual ‖A x − b‖² over all `y`
  iff it solves the normal equations Aᵀ(A x − b) = 0. If `A` has independent columns (`v ↦ A v`
  injective), the least-squares solution is unique.

REFERENCE
  -- after `open Matrix`: `A *ᵥ v` = A v (mulVec), `v ᵥ* A` = vᵀA (vecMul), `v ⬝ᵥ w` = Σ i, v i * w i, `Aᵀ` = transpose
  -- `t • v` = scalar multiple t·v;  ‖v‖² is written `v ⬝ᵥ v`, so ‖A x − b‖² is `(A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)`
  #check Matrix.mulVec_add          -- A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y        (also mulVec_sub, mulVec_smul)
  #check add_dotProduct             -- (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w        (also dotProduct_add)
  #check smul_dotProduct            -- x • v ⬝ᵥ w = x • (v ⬝ᵥ w)             (also dotProduct_smul, smul_eq_mul)
  #check dotProduct_comm            -- v ⬝ᵥ w = w ⬝ᵥ v
  #check Matrix.dotProduct_mulVec   -- v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w
  #check Matrix.mulVec_transpose    -- Aᵀ *ᵥ x = x ᵥ* A
  #check dotProduct_self_eq_zero    -- v ⬝ᵥ v = 0 ↔ v = 0   (over ℝ)
  #check dotProduct_self_star_nonneg -- 0 ≤ v ⬝ᵥ star v;  on ℝ `star v = v`, so `simpa using` it
  example (A : Matrix (Fin 2) (Fin 2) ℝ) (x b d : Fin 2 → ℝ) : A *ᵥ x + A *ᵥ d - b = (A *ᵥ x - b) + A *ᵥ d := by abel
NOTE: `Function.Injective A.mulVec` says A *ᵥ v = A *ᵥ w → v = w, i.e. the columns of A are independent.
-/
import Mathlib
open Matrix

namespace H074

-- MILESTONE (optional: change or delete)
theorem cross_term {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ) (d : Fin n → ℝ) :
    (A *ᵥ d) ⬝ᵥ r = (Aᵀ *ᵥ r) ⬝ᵥ d := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose]

-- MILESTONE (optional: change or delete)
theorem self_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa using dotProduct_self_star_nonneg v

-- MILESTONE (optional: change or delete)
/-- ‖A(x + d) − b‖² = ‖A x − b‖² + 2⟨Aᵀ(A x − b), d⟩ + ‖A d‖² -/
theorem expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x d : Fin n → ℝ) :
    (A *ᵥ (x + d) - b) ⬝ᵥ (A *ᵥ (x + d) - b) =
      (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) + 2 * ((Aᵀ *ᵥ (A *ᵥ x - b)) ⬝ᵥ d) + (A *ᵥ d) ⬝ᵥ (A *ᵥ d) := by
  rw [mulVec_add, show A *ᵥ x + A *ᵥ d - b = (A *ᵥ x - b) + A *ᵥ d by abel]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (A *ᵥ x - b) (A *ᵥ d), cross_term]
  ring

-- BEGIN SPEC
theorem normal_equations_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Aᵀ *ᵥ (A *ᵥ x - b) = 0 ↔
      ∀ y, (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) ≤ (A *ᵥ y - b) ⬝ᵥ (A *ᵥ y - b) :=
-- END SPEC
  by
    constructor
    · intro hx y
      have h := expand A b x (y - x)
      rw [add_sub_cancel, hx, zero_dotProduct] at h
      rw [h]
      linarith [self_nonneg (A *ᵥ (y - x))]
    · intro hmin
      set g := Aᵀ *ᵥ (A *ᵥ x - b)
      set G := g ⬝ᵥ g
      set Q := (A *ᵥ g) ⬝ᵥ (A *ᵥ g)
      have hQ : 0 ≤ Q := self_nonneg _
      by_contra hg
      have hG : 0 < G := lt_of_le_of_ne (self_nonneg g) fun h => hg (dotProduct_self_eq_zero.mp h.symm)
      set t := G / (Q + 1)
      have ht : 0 < t := by positivity
      -- WHY: a small step against the gradient `g` strictly lowers the residual.
      have h := hmin (x + (-t) • g)
      rw [expand] at h
      simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
      change _ ≤ _ + 2 * (-t * G) + (-t * (-t * Q)) at h
      have h2 : 2 * G ≤ t * Q := by nlinarith
      have h3 : t * Q < G := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      linarith

-- BEGIN SPEC
theorem least_squares_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) (x x' : Fin n → ℝ)
    (hx : Aᵀ *ᵥ (A *ᵥ x - b) = 0) (hx' : Aᵀ *ᵥ (A *ᵥ x' - b) = 0) : x = x' :=
-- END SPEC
  by
    have e1 := expand A b x (x' - x)
    have e2 := expand A b x' (x - x')
    rw [add_sub_cancel, hx, zero_dotProduct] at e1
    rw [add_sub_cancel, hx', zero_dotProduct] at e2
    have n1 := self_nonneg (A *ᵥ (x' - x))
    have n2 := self_nonneg (A *ᵥ (x - x'))
    have h0 : (A *ᵥ (x' - x)) ⬝ᵥ (A *ᵥ (x' - x)) = 0 := by linarith
    have h1 := dotProduct_self_eq_zero.mp h0
    rw [mulVec_sub, sub_eq_zero] at h1
    exact (hA h1).symm

end H074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything follows from `expand`: the residual at `x + d` is the residual at `x`, plus twice the cross term with the gradient `g := Aᵀ(A x − b)`, plus ‖A d‖² ≥ 0. For `expand`, regroup `A x + A d − b` as `(A x − b) + A d` (`abel`), distribute with `add_dotProduct`/`dotProduct_add`, then `cross_term` and `ring`.
H2. (→) use `expand` with `d = y − x` (`add_sub_cancel`): the cross term is `0 ⬝ᵥ d = 0`. (←) by contradiction: if `g ≠ 0` then `G := g ⬝ᵥ g > 0`; step a little against the gradient, `y = x + (−t) • g` with `t > 0`, and the residual drops. Uniqueness: expand at `x` toward `x'` and at `x'` toward `x`, add.
H3. (←) with `Q := (A *ᵥ g) ⬝ᵥ (A *ᵥ g)` take `t := G / (Q + 1)`; `simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h` turns minimality into `0 ≤ −2tG + t²Q`, so `2G ≤ tQ`, but `tQ < G` (`div_lt_iff₀`). Uniqueness: the two expansions give `‖A(x' − x)‖² = 0`, so `dotProduct_self_eq_zero`, `mulVec_sub`, `sub_eq_zero`, `hA`.
-/
