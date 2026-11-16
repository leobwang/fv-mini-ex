/- M136 | The Bloch ball | 15-20 min | MState, 2×2 Hermitian, PosSemidef.det_nonneg, nlinarith, physlib
GOAL
  Every qubit state can be written `ρ = ½(I + xX + yY + zZ)` with real Bloch coordinates
  `x = 2 Re ρ₀₁`, `y = −2 Im ρ₀₁`, `z = ρ₀₀ − ρ₁₁` (`X, Y, Z` the Pauli matrices). Prove `x² + y² + z² ≤ 1`.

REFERENCE
  -- context: `open scoped ComplexOrder` (the order `≤` on ℂ), `variable (ρ : MState (Fin 2))`
  example : ρ.m.PosSemidef := ρ.psd             -- also `ρ.Hermitian : ρ.m.IsHermitian`
  example : ρ.m.trace = 1 := ρ.tr'                 -- `ρ.m : Matrix (Fin 2) (Fin 2) ℂ`
  example (h : ρ.m.PosSemidef) : 0 ≤ ρ.m.det := h.det_nonneg   -- `≤` on ℂ: see `Complex.nonneg_iff`
  example (i j : Fin 2) : star (ρ.m j i) = ρ.m i j := ρ.Hermitian.apply i j
  #check Matrix.det_fin_two     -- A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0
  #check Matrix.trace_fin_two   -- A.trace = A 0 0 + A 1 1
  #check Complex.nonneg_iff     -- 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im
  #check Complex.mul_re         -- (z * w).re = z.re * w.re - z.im * w.im
  example (z : ℂ) (h : z = 1) : z.re = 1 := by simpa using congrArg Complex.re h   -- take real parts
  example (a b : ℝ) (h : 0 ≤ a * b) : (a - b) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [h]
-/
import QuantumInfo.States.Mixed.MState

open scoped ComplexOrder

namespace M136

-- BEGIN SPEC
/-- Bloch coordinates of a qubit state. -/
def blochX (ρ : MState (Fin 2)) : ℝ := 2 * (ρ.m 0 1).re
def blochY (ρ : MState (Fin 2)) : ℝ := -2 * (ρ.m 0 1).im
def blochZ (ρ : MState (Fin 2)) : ℝ := (ρ.m 0 0).re - (ρ.m 1 1).re
-- END SPEC

-- BEGIN SPEC
theorem bloch_ball (ρ : MState (Fin 2)) : blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 ≤ 1 :=
-- END SPEC
  by
    have hdet := ρ.psd.det_nonneg
    have htr := ρ.tr'
    have h10 : ρ.m 1 0 = star (ρ.m 0 1) := (ρ.Hermitian.apply 1 0).symm
    -- WHY: the diagonal of a Hermitian matrix is real; `nlinarith` needs these imaginary parts.
    have h00 : (ρ.m 0 0).im = 0 := by
      have := congrArg Complex.im (ρ.Hermitian.apply 0 0); simp at this; linarith
    have h11 : (ρ.m 1 1).im = 0 := by
      have := congrArg Complex.im (ρ.Hermitian.apply 1 1); simp at this; linarith
    rw [Matrix.det_fin_two, h10, Complex.nonneg_iff] at hdet
    rw [Matrix.trace_fin_two] at htr
    have htr' := congrArg Complex.re htr
    simp [Complex.mul_re, h00, h11] at hdet htr'
    simp only [blochX, blochY, blochZ]
    nlinarith [hdet.1]

end M136

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `a = ρ₀₀`, `b = ρ₁₁` (real), `w = ρ₀₁`, so `ρ₁₀ = conj w`. Positivity gives `det ρ ≥ 0`,
    i.e. `ab ≥ |w|²`; the trace gives `a + b = 1`. The claim is `(a − b)² + 4|w|² ≤ (a + b)²`.
H2. Collect `hdet := ρ.psd.det_nonneg`, `htr := ρ.tr'`, `h10 : ρ.m 1 0 = star (ρ.m 0 1)`, and
    `(ρ.m 0 0).im = 0`, `(ρ.m 1 1).im = 0` (imaginary part of the Hermitian condition at `(0,0)`, `(1,1)`).
    Expand `det`/`trace` for `Fin 2`, take real parts, and hand everything to `nlinarith`.
H3. `rw [Matrix.det_fin_two, h10, Complex.nonneg_iff] at hdet; rw [Matrix.trace_fin_two] at htr`;
    `have htr' := congrArg Complex.re htr`; `simp [blochX, blochY, blochZ, Complex.mul_re, h00, h11] at *`;
    `nlinarith [hdet.1]`.
-/
