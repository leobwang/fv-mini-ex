/- H074 | Least squares and the normal equations | 45-75 min | Matrix, dotProduct, transpose, quadratic expansion, optimality, mathlib
GOAL
  For a real m×n matrix `A` and `b : ℝᵐ`, `x` minimises the squared residual ‖A x − b‖² over all `y`
  iff it solves the normal equations Aᵀ(A x − b) = 0. If `A` has independent columns (`v ↦ A v`
  injective), the least-squares solution is unique.

GUIDE
  Entries R1–R30: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib
open Matrix

namespace H074

/- SKELETON · cross_term   (milestone; used by expand)
  1. Swap the left dot product so that `A *ᵥ d` sits on the right:                 R1
  2. Move `A` across the dot product: `r ⬝ᵥ A *ᵥ d` → `r ᵥ* A ⬝ᵥ d`:                  R2
  3. Rewrite `Aᵀ *ᵥ r` on the right as `r ᵥ* A`; both sides are now the same
     text and `rw` closes the goal by `rfl`:                                        R3
-/
-- MILESTONE (optional: change or delete)
theorem cross_term {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ) (d : Fin n → ℝ) :
    (A *ᵥ d) ⬝ᵥ r = (Aᵀ *ᵥ r) ⬝ᵥ d := by
  sorry

/- SKELETON · self_nonneg   (milestone; used by normal_equations_iff, least_squares_unique)
  1. Mathlib's fact `0 ≤ v ⬝ᵥ star v` (`star` = conjugation, so this is Σ |vᵢ|²):    R4
  2. On ℝ `star v = v`; `simpa using` the fact from step 1:                          R5
-/
-- MILESTONE (optional: change or delete)
theorem self_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ v := by
  sorry

/- SKELETON · expand   (milestone; used by both spec theorems)
  Write r := A *ᵥ x - b (the residual at x).
  1. Distribute `A` over `x + d`, then regroup `A *ᵥ x + A *ᵥ d - b` as
     `(A *ᵥ x - b) + A *ᵥ d`:                                                         R6, R7
  2. Distribute both dot products (one `simp only` with both lemmas):                R8, R9
  3. The goal now has two cross terms, `A *ᵥ d ⬝ᵥ r` (2nd summand) and `r ⬝ᵥ A *ᵥ d`
     (3rd). Swap ONLY `r ⬝ᵥ A *ᵥ d` (give R1 both arguments, `r` and `A *ᵥ d`), then
     turn both copies of `A *ᵥ d ⬝ᵥ r` into `Aᵀ *ᵥ r ⬝ᵥ d` with the milestone:         R1, rw [cross_term]
  4. Both sides are now a ring identity in the dot-product atoms:                    R10
-/
-- MILESTONE (optional: change or delete)
/-- ‖A(x + d) − b‖² = ‖A x − b‖² + 2⟨Aᵀ(A x − b), d⟩ + ‖A d‖² -/
theorem expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x d : Fin n → ℝ) :
    (A *ᵥ (x + d) - b) ⬝ᵥ (A *ᵥ (x + d) - b) =
      (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) + 2 * ((Aᵀ *ᵥ (A *ᵥ x - b)) ⬝ᵥ d) + (A *ᵥ d) ⬝ᵥ (A *ᵥ d) := by
  sorry

/- SKELETON · normal_equations_iff
  0. Prove the MILESTONES first: cross_term, then expand; and self_nonneg.
     Both directions below use expand (step 2, step 6) and self_nonneg (steps 2–4).
  1. Split the ↔:                                                                    R11
  2. (→) `intro hx y`; expand at x toward y: `have h := expand A b x (y - x)`.
     In h: `x + (y - x)` → `y`, substitute hx, kill `0 ⬝ᵥ _`:                          R12, rw [hx], R13
     Then `rw [h]` and close with the extra fact self_nonneg (A *ᵥ (y - x)):          R14
  3. (←) `intro hmin`; name g := Aᵀ *ᵥ (A *ᵥ x - b), G := g ⬝ᵥ g,
     Q := (A *ᵥ g) ⬝ᵥ (A *ᵥ g):                                                       R15
     hQ : 0 ≤ Q from self_nonneg.
  4. Suppose `g ≠ 0`:                                                                R16
     hG : 0 < G, from self_nonneg g and "G = 0 forces g = 0":                         R18, R17
  5. Step size t := G / (Q + 1) and ht : 0 < t:                                       R15, R19
  6. Minimality at the point x + (-t) • g (one step against the gradient):
     `have h := hmin (x + (-t) • g)` (write the point; `hmin _` does not elaborate),
     `rw [expand] at h`, pull the scalars out (one `simp only … at h`),
     then fold the result back into the names G and Q:                               R20, R21, R22, R23, R24
       h : _ ≤ _ + 2 * (-t * G) + (-t * (-t * Q))
  7. h2 : 2 * G ≤ t * Q                                                              R25
     h3 : t * Q < G   (`rw` sees through the `set` name t, so R26 makes `t * Q` one
                       fraction; clear the denominator Q + 1 > 0; then R25):         R26, R27, R25
     contradiction from h2, h3, hG:                                                  R14
-/
-- BEGIN SPEC
theorem normal_equations_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Aᵀ *ᵥ (A *ᵥ x - b) = 0 ↔
      ∀ y, (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) ≤ (A *ᵥ y - b) ⬝ᵥ (A *ᵥ y - b) :=
-- END SPEC
  sorry

/- SKELETON · least_squares_unique
  0. Uses the MILESTONES expand and self_nonneg.
  1. Expand at x toward x' and at x' toward x:
       e1 := expand A b x (x' - x),  e2 := expand A b x' (x - x')
     In each: `x + (x' - x)` → `x'`, substitute hx (resp. hx'), kill `0 ⬝ᵥ _`:      R12, rw [hx], R13
  2. Both ‖A(x' − x)‖² and ‖A(x − x')‖² are ≥ 0 (self_nonneg); adding e1, e2:
       h0 : (A *ᵥ (x' - x)) ⬝ᵥ (A *ᵥ (x' - x)) = 0                                  R14
  3. h1 : A *ᵥ (x' - x) = 0, then in h1 split the product and move to `=`:          R17, R28, R29
       h1 : A *ᵥ x' = A *ᵥ x
  4. Injectivity turns h1 into `x' = x`; the goal is its `.symm`:                    R30
-/
-- BEGIN SPEC
theorem least_squares_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) (x x' : Fin n → ℝ)
    (hx : Aᵀ *ᵥ (A *ᵥ x - b) = 0) (hx' : Aᵀ *ᵥ (A *ᵥ x' - b) = 0) : x = x' :=
-- END SPEC
  sorry

end H074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything follows from `expand`: with g := Aᵀ(A x − b), ‖A(x + d) − b‖² = ‖A x − b‖² + 2⟨g, d⟩ + ‖A d‖²,
    and ‖A d‖² ≥ 0. Prove the milestones in order: cross_term (R1–R3), self_nonneg (R4, R5),
    expand (R6–R10, using cross_term for the cross term).
H2. (→) `expand` with d = y − x: `add_sub_cancel` (R12), then hx makes the cross term `0 ⬝ᵥ d = 0` (R13);
    `linarith` with self_nonneg finishes (R14). (←) by contradiction (R16): if g ≠ 0 then G := g ⬝ᵥ g > 0
    (R17, R18); step against the gradient, y = x + (−t) • g with t > 0, and the residual drops.
    Uniqueness: expand at x toward x' and at x' toward x, add: ‖A(x' − x)‖² = 0.
H3. (←) with Q := (A *ᵥ g) ⬝ᵥ (A *ᵥ g) take t := G / (Q + 1). After `rw [expand] at h`,
    `simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h` and
    `change _ ≤ _ + 2 * (-t * G) + (-t * (-t * Q)) at h` say 0 ≤ −2tG + t²Q, so `2 * G ≤ t * Q` (nlinarith),
    but `t * Q < G` (`rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith`).
    Uniqueness: `dotProduct_self_eq_zero.mp h0`, `rw [mulVec_sub, sub_eq_zero] at h1`, `exact (hA h1).symm`.
-/
