/- M145 | No-signalling | 20-25 min | partial trace, Kraus operators, Kronecker product, Finset.sum_comm, physlib
GOAL
  Alice applies any channel with Kraus operators `K i` (`∑ i, (K i)ᴴ * K i = 1`) to her half of a joint
  state `M`. Bob's reduced state `Tr_A` (partial trace over Alice) does not change, so she cannot signal.

REFERENCE
  -- `Aᴴ` is the conjugate transpose: Aᴴ i j = conj (A j i).
  -- `A ⊗ₖ B` (open scoped Kronecker) has (A ⊗ₖ B) (a, b) (c, e) = A a c * B b e; in `d₁ × d₂` Alice is the first factor.
  #check Matrix.traceLeft             -- QuantumInfo: M.traceLeft i j = ∑ k, M (k, i) (k, j)   (trace out factor 1)
  #check Matrix.conjTranspose_kronecker  -- (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ
  #check Matrix.conjTranspose_one     -- 1ᴴ = 1
  #check Matrix.mul_kronecker_mul     -- (A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'   (rewrite right-to-left with ←)
  #check Matrix.one_kronecker_one     -- 1 ⊗ₖ 1 = 1
  #check Matrix.mul_sum               -- M * ∑ a ∈ s, f a = ∑ a ∈ s, M * f a
  #check Matrix.sum_apply             -- (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j
  #check Finset.sum_comm              -- ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
  #check Fintype.sum_prod_type        -- ∑ x, f x = ∑ x, ∑ y, f (x, y)   (a sum over pairs)
  #check Finset.sum_ite_eq            -- (∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0
  -- entrywise: `ext x y; simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]`
-/
import QuantumInfo.ForMathlib.Matrix

open Matrix
open scoped Kronecker

namespace M145

/-- Bob's partial trace is cyclic for operators acting only on Alice's factor. -/
theorem traceLeft_cyc {d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₂]
    (A : Matrix d₁ d₁ ℂ) (N : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    ((A ⊗ₖ (1 : Matrix d₂ d₂ ℂ)) * N).traceLeft = (N * (A ⊗ₖ (1 : Matrix d₂ d₂ ℂ))).traceLeft := by
  ext x y
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem traceLeft_sum {d₁ d₂ ι : Type} [Fintype d₁] [Fintype ι]
    (f : ι → Matrix (d₁ × d₂) (d₁ × d₂) ℂ) : (∑ i, f i).traceLeft = ∑ i, (f i).traceLeft := by
  ext x y
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

-- BEGIN SPEC
theorem no_signalling {d₁ d₂ ι : Type} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    [Fintype ι] (K : ι → Matrix d₁ d₁ ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (M : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (∑ i, (K i ⊗ₖ (1 : Matrix d₂ d₂ ℂ)) * M * (K i ⊗ₖ (1 : Matrix d₂ d₂ ℂ))ᴴ).traceLeft
      = M.traceLeft :=
-- END SPEC
  by
    rw [traceLeft_sum]
    simp_rw [Matrix.mul_assoc, traceLeft_cyc, Matrix.mul_assoc, conjTranspose_kronecker,
      conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [← traceLeft_sum, ← Matrix.mul_sum]
    have hk : ∑ i, ((K i)ᴴ * K i) ⊗ₖ (1 : Matrix d₂ d₂ ℂ) = 1 := by
      rw [← one_kronecker_one, ← hK]
      ext ⟨a, b⟩ ⟨c, e⟩
      simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
    rw [hk, Matrix.mul_one]

end M145

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Mirror the proof that a Kraus map preserves the trace: `traceLeft` is linear, and it is *cyclic*
    for operators that act only on Alice's factor. Prove those two facts as helper lemmas first.
H2. Cyclicity: entrywise, `1 ⊗ₖ`-terms collapse with `Finset.sum_ite_eq`, then one `Finset.sum_comm`
    and `mul_comm`. Main proof: move `(K i ⊗ₖ 1)` from the front to the back of every term, merge
    `(K i)ᴴ ⊗ₖ 1 * (K i ⊗ₖ 1)` into `((K i)ᴴ * K i) ⊗ₖ 1`, pull `M *` out of the sum, and use `hK`.
H3. `theorem traceLeft_cyc (A : Matrix d₁ d₁ ℂ) (N : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
       ((A ⊗ₖ (1 : Matrix d₂ d₂ ℂ)) * N).traceLeft = (N * (A ⊗ₖ (1 : Matrix d₂ d₂ ℂ))).traceLeft`
    and `theorem traceLeft_sum (f : ι → Matrix (d₁ × d₂) (d₁ × d₂) ℂ) : (∑ i, f i).traceLeft = ∑ i, (f i).traceLeft`.
    Main proof: `rw [traceLeft_sum]`, then
    `simp_rw [Matrix.mul_assoc, traceLeft_cyc, Matrix.mul_assoc, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]`,
    then `rw [← traceLeft_sum, ← Matrix.mul_sum]`. Mathlib has no `sum_kronecker`, so prove the last step entrywise:
    `have hk : ∑ i, ((K i)ᴴ * K i) ⊗ₖ (1 : Matrix d₂ d₂ ℂ) = 1 := by
       rw [← one_kronecker_one, ← hK]; ext ⟨a, b⟩ ⟨c, e⟩; simp [Matrix.sum_apply, Finset.sum_mul]`
    and finish with `rw [hk, Matrix.mul_one]`.
-/
