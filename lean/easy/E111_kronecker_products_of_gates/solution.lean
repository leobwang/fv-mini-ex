/- E111 | Kronecker products of gates | 2-3 min | kroneckerMap, ⊗ₖ, mul_kronecker_mul, one_kronecker_one, rw ←, mathlib
GOAL
  A gate on a two-part system is a Kronecker product `A ⊗ₖ B` (`A` acts on the first part, `B` on
  the second). Show: if `A² = 1` and `B² = 1` then `(A ⊗ₖ B)² = 1`; and gates acting on different
  parts commute: `(A ⊗ₖ 1) * (1 ⊗ₖ B) = (1 ⊗ₖ B) * (A ⊗ₖ 1)`.

GUIDE
  Entries R1–R4: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E111

/- SKELETON · kron_involution
  The infoview prints `A ⊗ₖ B` as `kroneckerMap (fun x1 x2 => x1 * x2) A B`.
  1. Merge the product of the two Kronecker products into one Kronecker product;
     the goal becomes `(A * A) ⊗ₖ (B * B) = 1`:                               R1
  2. Replace each factor by `1` with the hypotheses:                          rw [hA], rw [hB]
  3. `1 ⊗ₖ 1` → `1`; the goal `1 = 1` is then closed by `rw` itself:         R2
-/
-- BEGIN SPEC
open Matrix
open scoped Kronecker

theorem kron_involution {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A * A = 1) (hB : B * B = 1) :
    (A ⊗ₖ B) * (A ⊗ₖ B) = 1 :=
-- END SPEC
  by rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

/- SKELETON · local_gates_commute
  1. Merge the left-hand product, then the right-hand one (they are different
     products, so one `rw` rewrites only one of them):                        R1, R1
     The goal becomes `(A * 1) ⊗ₖ (1 * B) = (1 * A) ⊗ₖ (B * 1)`.
  2. Remove the four identity factors, one `rw` per factor (or one
     `simp only` with both lemmas); `rw` closes `A ⊗ₖ B = A ⊗ₖ B` itself:    R3, R4
-/
-- BEGIN SPEC
theorem local_gates_commute {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (A ⊗ₖ 1) * (1 ⊗ₖ B) = (1 ⊗ₖ B) * (A ⊗ₖ 1) :=
-- END SPEC
  by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]

end E111

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A product of two Kronecker products is the Kronecker product of the products (mixed-product rule,
    R1). In the infoview `A ⊗ₖ B` shows up as `kroneckerMap (fun x1 x2 => x1 * x2) A B`.
H2. Turn every `(X ⊗ₖ Y) * (X' ⊗ₖ Y')` into `(X * X') ⊗ₖ (Y * Y')` first; then only the factors are left to
    simplify: with `hA`, `hB` and `1 ⊗ₖ 1 = 1` (R2) in the first theorem, with `M * 1 = M`, `1 * M = M`
    (R3, R4) in the second.
H3. `rw [← Matrix.mul_kronecker_mul]` (once per product: twice in `local_gates_commute`). Then
    `rw [hA, hB, Matrix.one_kronecker_one]`, resp. `simp only [Matrix.mul_one, Matrix.one_mul]`.
-/
