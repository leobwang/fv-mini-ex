/- M145 | No-signalling | 20-25 min | partial trace, Kraus operators, Kronecker product, Finset.sum_comm, physlib
GOAL
  Alice applies any channel with Kraus operators `K i` (`∑ i, (K i)ᴴ * K i = 1`) to her half of a joint
  state `M`. Bob's reduced state `Tr_A` (partial trace over Alice) does not change, so she cannot signal.

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · no_signalling
  0. Two MILESTONES first: your own helper lemmas between `namespace M145` and this comment (outside
     the spec regions), each with its own type arguments `{d₁ d₂ …}` and the instances it needs:
       traceLeft_sum (f : ι → Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
           (∑ i, f i).traceLeft = ∑ i, (f i).traceLeft                    (used in steps 1 and 3)
         entrywise:                                                    R1
         ONE `simp only [...]` with R2 and R3 (in separate calls an `of (…) x y` stays on the
         right); the two sides then differ only in the order of the two sums:     R4
       traceLeft_cyc (A : Matrix d₁ d₁ ℂ) (N : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
           ((A ⊗ₖ 1) * N).traceLeft = (N * (A ⊗ₖ 1)).traceLeft   (1 : Matrix d₂ d₂ ℂ; used in step 2)
         entrywise:                                                    R1
         ONE `simp only [...]` with R2, R5, R6, R7, R8, R9, R10, R11, R12; it leaves
           ∑ x_1, ∑ x_2, A x_1 x_2 * N (x_2, x) (x_1, y) = ∑ x_1, ∑ x_2, N (x_1, x) (x_2, y) * A x_2 x_1
         swap the sums on the left, then compare term by term:         R4, R13, R13, R14
  1. Linearity: push `traceLeft` into the sum:                         rw [traceLeft_sum]
  2. In every term, UNDER the `∑` (one `simp_rw [...]` with these lemmas in this order):   R16
       regroup so the term reads `(K i ⊗ₖ 1) * N`                      R15
       rotate `(K i ⊗ₖ 1)` to the back                                 traceLeft_cyc
       regroup: `M * ((K i ⊗ₖ 1)ᴴ * (K i ⊗ₖ 1))`                       R15
       `(K i ⊗ₖ 1)ᴴ` → `(K i)ᴴ ⊗ₖ 1`                                    R17, R18
       merge the Kronecker products; `1 * 1` → `1`                     R19, R20
     goal:  ∑ x, (M * ((K x)ᴴ * K x) ⊗ₖ 1).traceLeft = M.traceLeft
  3. Linearity backwards, then pull `M *` out of the sum:              rw [← traceLeft_sum], R21
  4. The fact (no `sum_kronecker` lemma exists, so prove it entrywise):
       hk : ∑ i, ((K i)ᴴ * K i) ⊗ₖ (1 : Matrix d₂ d₂ ℂ) = 1
     proof: R22, then rw [← hK], then R23, then `simp` with R3, R7, R24
  5. rw [hk], then R25; `rw` closes `M.traceLeft = M.traceLeft` itself.
-/
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
H1. Mirror the proof that a Kraus map preserves the trace (M144): `traceLeft` is linear, and it is
    *cyclic* for operators that act only on Alice's factor. Prove those two facts as helper lemmas
    first (the milestones in the SKELETON); the main proof is then rewriting, plus one entrywise fact.
H2. Milestones, entrywise (`ext x y`): linearity is one `simp only` with R2, R3, then one
    `Finset.sum_comm`; cyclicity is one `simp only` with R2, R5–R12 (the `1`-factors collapse via
    `Finset.sum_ite_eq`), then
    `rw [Finset.sum_comm]` and `Finset.sum_congr` twice with `mul_comm`. Main proof: `rw [traceLeft_sum]`,
    then move `(K i ⊗ₖ 1)` from the front to the back of every term with `simp_rw`, merge
    `(K i)ᴴ ⊗ₖ 1 * (K i ⊗ₖ 1)` into `((K i)ᴴ * K i) ⊗ₖ 1`, fold the sum back, pull `M *` out, use `hK`.
H3. `simp_rw [Matrix.mul_assoc, traceLeft_cyc, Matrix.mul_assoc, conjTranspose_kronecker,
       conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]`, then `rw [← traceLeft_sum, ← Matrix.mul_sum]`.
    Last step: `have hk : ∑ i, ((K i)ᴴ * K i) ⊗ₖ (1 : Matrix d₂ d₂ ℂ) = 1 := by
       rw [← one_kronecker_one, ← hK]; ext ⟨a, b⟩ ⟨c, e⟩; simp [Matrix.sum_apply, Finset.sum_mul]`
    and finish with `rw [hk, Matrix.mul_one]`.
-/
