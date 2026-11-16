/- E111 | Kronecker products of gates | 2-3 min | kroneckerMap, ⊗ₖ, mul_kronecker_mul, one_kronecker_one, rw ←, mathlib
GOAL
  A gate on a two-part system is a Kronecker product `A ⊗ₖ B` (`A` acts on the first part, `B` on
  the second). Show: if `A² = 1` and `B² = 1` then `(A ⊗ₖ B)² = 1`; and gates acting on different
  parts commute: `(A ⊗ₖ 1) * (1 ⊗ₖ B) = (1 ⊗ₖ B) * (A ⊗ₖ 1)`.

REFERENCE
  #check Matrix.mul_kronecker_mul  -- (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'   (rewrite right-to-left with ←)
  #check Matrix.one_kronecker_one  -- 1 ⊗ₖ 1 = 1
  #check Matrix.mul_one            -- M * 1 = M     (and `Matrix.one_mul : 1 * M = M`)
  `A ⊗ₖ B` (typed `\otimes\_k`, needs `open scoped Kronecker`) is `Matrix.kroneckerMap (· * ·) A B`;
  `#check` prints it that way. It is indexed by pairs: (A ⊗ₖ B) (i, k) (j, l) = A i j * B k l.
  `rw [← h]` rewrites occurrences of the right side of `h` into its left side.
-/
import Mathlib

namespace E111

-- BEGIN SPEC
open Matrix
open scoped Kronecker

theorem kron_involution {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A * A = 1) (hB : B * B = 1) :
    (A ⊗ₖ B) * (A ⊗ₖ B) = 1 :=
-- END SPEC
  by rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]

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
H1. A product of two Kronecker products is the Kronecker product of the products (mixed-product rule).
H2. Rewrite each `(P ⊗ₖ Q) * (R ⊗ₖ S)` into `(P * R) ⊗ₖ (Q * S)` with `← Matrix.mul_kronecker_mul`, then
    simplify the factors.
H3. `rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]`;
    `rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]`, then `Matrix.mul_one`/`Matrix.one_mul`.
-/
