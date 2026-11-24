/- M140 | Linear no-cloning | 15-20 min | no-cloning, linearity, superposition, Pi.single, mulVec, mathlib
GOAL
  No matrix `C` on `ℂ^d ⊗ ℂ^d` (with `d ≥ 2` basis states) copies every nonzero vector into a blank register `e`,
  even up to a nonzero factor: it is impossible that `C (v ⊗ e) = c • (v ⊗ v)` with `c ≠ 0` for all `v ≠ 0`.
  (With `d = 1` such a `C` exists.) Linearity breaks on a superposition.

REFERENCE
  -- A vector on `d × d` is a function of index pairs: `v ⊗ e` is `fun p => v p.1 * e p.2`.  `M *ᵥ v` is matrix·vector.
  #check exists_pair_ne       -- (α : Type) [Nontrivial α] : ∃ x y, x ≠ y
  #check @Pi.single_apply     -- Pi.single i x i' = if i' = i then x else 0   (`Pi.single i 1` is the basis vector |i⟩)
  example (i : Fin 3) : (Pi.single i (1 : ℂ) : Fin 3 → ℂ) i = 1 := by simp
  #check @Matrix.mulVec_add   -- A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y
  #check @Pi.smul_apply       -- (c • f) x = c • f x   (`•` scales a function pointwise; `simp` knows it)
  example (h : ∃ c : ℂ, c ≠ 0 ∧ c * 2 = 2) : True := by obtain ⟨c, hc, h2⟩ := h; trivial   -- unpack ∃ and ∧
  example (f g : ℕ → ℕ) (h : f = g) (x : ℕ) : f x = g x := congrFun h x   -- evaluate a function equation
-/
import Mathlib

open Matrix

namespace M140

-- BEGIN SPEC
theorem no_linear_cloner {d : Type} [Fintype d] [DecidableEq d] [Nontrivial d]
    (C : Matrix (d × d) (d × d) ℂ) (e : d → ℂ) :
    ¬ ∀ v : d → ℂ, v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧
      C *ᵥ (fun p => v p.1 * e p.2) = c • fun p => v p.1 * v p.2 :=
-- END SPEC
  sorry

end M140

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Assume a cloner `h` exists, pick two different indices `i ≠ j`, and feed it `|i⟩`, `|j⟩` and `|i⟩ + |j⟩`
    (each time you must first show the input is `≠ 0`: evaluate `hk : v = 0` at a well-chosen index).
H2. The input `(|i⟩ + |j⟩) ⊗ e` splits as `|i⟩ ⊗ e + |j⟩ ⊗ e` (prove it with `funext p; simp [add_mul]`), so
    `mulVec_add` and the two basis cases give `cᵢ |i⟩⊗|i⟩ + cⱼ |j⟩⊗|j⟩`, which is `0` at the index `(i, j)`.
    A real clone `c (|i⟩+|j⟩) ⊗ (|i⟩+|j⟩)` is `c` there, and `c ≠ 0`.
H3. `obtain ⟨c, hc, hs⟩ := h _ hs0; rw [lin, Matrix.mulVec_add, hi, hj] at hs; have := congrFun hs (i, j)`,
    then `simp [Pi.single_apply, hij, hij.symm] at this` leaves `0 = c` (or similar); finish with `hc`.
-/
