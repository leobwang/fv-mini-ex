/- M140 | Linear no-cloning | 15-20 min | no-cloning, linearity, superposition, Pi.single, mulVec, mathlib
GOAL
  No matrix `C` on `ℂ^d ⊗ ℂ^d` (with `d ≥ 2` basis states) copies every nonzero vector into a blank register `e`,
  even up to a nonzero factor: it is impossible that `C (v ⊗ e) = c • (v ⊗ v)` with `c ≠ 0` for all `v ≠ 0`.
  (With `d = 1` such a `C` exists.) Linearity breaks on a superposition.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix

namespace M140

/- SKELETON · no_linear_cloner
  Notation: |k⟩ is `(Pi.single k 1 : d → ℂ)`, v ⊗ w is `fun p => v p.1 * w p.2`.
  1. Assume a cloner `h` exists; the goal becomes `False`:                     R1
  2. Two different indices `i j : d`, `hij : i ≠ j`:                            R2
  3. Prove first: every basis vector is nonzero
       ne : ∀ k : d, (Pi.single k 1 : d → ℂ) ≠ 0                               R3 → R4 at k → simp (R5, R6, R7)
  4. Use `h` on |i⟩ and on |j⟩; keep only the equations `hi`, `hj`:            R8
  5. Prove: the superposition is nonzero
       hs0 : (Pi.single i 1 + Pi.single j 1 : d → ℂ) ≠ 0                       R3 → R4 at i → simp with R11 (R9, R5, R10, R7)
  6. Use `h` on |i⟩ + |j⟩; keep `c`, `hc : c ≠ 0` and the equation `hs`:       R8
  7. Prove: the input splits, (|i⟩ + |j⟩) ⊗ e = |i⟩ ⊗ e + |j⟩ ⊗ e
       lin : (fun p : d × d => (Pi.single i 1 + Pi.single j 1 : d → ℂ) p.1 * e p.2) =
               (fun p => (Pi.single i 1 : d → ℂ) p.1 * e p.2) + (fun p => (Pi.single j 1 : d → ℂ) p.1 * e p.2)
                                                                               R12 → simp with R13 (R9)
  8. Rewrite `hs` with `lin`, linearity of `C`, then `hi`, `hj`:               R14 with R15
  9. Evaluate `hs` at the index pair `(i, j)`:                                  R4
 10. Simplify that number equation to `0 = c` (give `simp` both hij, hij.symm):  R9, R16, R17, R18, R11
 11. Contradiction with `hc`:                                                   R19
-/
-- BEGIN SPEC
theorem no_linear_cloner {d : Type} [Fintype d] [DecidableEq d] [Nontrivial d]
    (C : Matrix (d × d) (d × d) ℂ) (e : d → ℂ) :
    ¬ ∀ v : d → ℂ, v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧
      C *ᵥ (fun p => v p.1 * e p.2) = c • fun p => v p.1 * v p.2 :=
-- END SPEC
  sorry

end M140

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Assume a cloner `h` exists (`intro h`), pick two different indices `i ≠ j` (`exists_pair_ne d`), and feed `h`
    the vectors `|i⟩ = Pi.single i 1`, `|j⟩` and `|i⟩ + |j⟩`. Each use first needs `v ≠ 0`: assume `hk : v = 0`
    and evaluate it at one index with `congrFun` (cheatsheet R3, R4, R7).
H2. The input `(|i⟩ + |j⟩) ⊗ e` splits as `|i⟩ ⊗ e + |j⟩ ⊗ e` (prove it as a `have lin` with `funext p` and
    `simp [add_mul]`), so `Matrix.mulVec_add` and the two basis cases turn the output into
    `cᵢ |i⟩⊗|i⟩ + cⱼ |j⟩⊗|j⟩`, which is `0` at the index pair `(i, j)`. A real clone
    `c (|i⟩+|j⟩) ⊗ (|i⟩+|j⟩)` is `c` there, and `c ≠ 0`.
H3. `obtain ⟨c, hc, hs⟩ := h _ hs0; rw [lin, Matrix.mulVec_add, hi, hj] at hs; have := congrFun hs (i, j)`,
    then `simp [Pi.single_apply, hij, hij.symm] at this` leaves `this : 0 = c`; finish with `exact hc this.symm`.
-/
