/- M133 | Unitaries preserve Born probabilities | 15-20 min | Ket, unitaryGroup, star_mulVec, dotProduct, physlib
GOAL
  For a unitary `U` and a normalised ket `ψ`, the Born probabilities `|(Uψ)ᵢ|²` of measuring `Uψ`
  in the computational basis still sum to 1.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import QuantumInfo.Operators.Unitary

open scoped Matrix

namespace M133

/- SKELETON · unitary_born
  Two milestones first, then a chain. The sum is real; the algebra that moves `U` is complex.
  1. MILESTONE (a), a `have` (TACTIC_STATES, "Adding facts"):
       key : star (U.val *ᵥ ψ.vec) ⬝ᵥ (U.val *ᵥ ψ.vec) = star ψ.vec ⬝ᵥ ψ.vec
     proof: one `rw` chain                                       R1 → R2 → R3 → R4 → R5 → R6
  2. MILESTONE (b), a `have` for every vector (used twice in step 3):
       toC : ∀ v : d → ℂ, ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v
     proof: R7, then one `simp` naming R8 and R11 (it applies R9, R10, R12, R13 itself)
  3. Chain toC (for `U ψ`), key, toC (for `ψ`) reversed into
       h : ↑(∑ i, ‖(↑U *ᵥ ψ.vec) i‖ ^ 2) = ↑(∑ i, ‖ψ.vec i‖ ^ 2)              R14
  4. Replace the right-hand sum by 1 inside `h`:                            R15
  5. Leave `ℂ`: the goal is the real version of `h`:                        R16
-/
-- BEGIN SPEC
theorem unitary_born {d : Type} [Fintype d] [DecidableEq d] (U : 𝐔[d]) (ψ : Ket d) :
    ∑ i, ‖(U.val *ᵥ ψ.vec) i‖ ^ 2 = 1 :=
-- END SPEC
  sorry

end M133

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The sum `∑ ‖vᵢ‖²` is the real number behind the complex `star v ⬝ᵥ v` (= `v†v`). Show that `U`
    does not change `star v ⬝ᵥ v` (it is `ψ† U† U ψ`), then come back to `ℝ` and use `ψ.normalized'`.
H2. Two `have`s, as in the SKELETON: (a) `key` by a `rw` chain R1–R6 that moves `U` from the right
    factor to the left one and cancels `star U * U`; (b) `toC : ∀ v : d → ℂ,
    ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v` by `intro v` and one `simp`. Then glue with `Eq.trans`.
H3. (a): `rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]`;
    (b): `intro v; simp [dotProduct, Complex.conj_mul']`. Then
    `have h := (toC _).trans (key.trans (toC _).symm)`, `rw [ψ.normalized'] at h`, `exact_mod_cast h`.
-/
