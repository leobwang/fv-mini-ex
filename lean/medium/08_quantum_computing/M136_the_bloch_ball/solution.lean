/- M136 | The Bloch ball | 15-20 min | MState, 2×2 Hermitian, PosSemidef.det_nonneg, nlinarith, physlib
GOAL
  Every qubit state can be written `ρ = ½(I + xX + yY + zZ)` with real Bloch coordinates
  `x = 2 Re ρ₀₁`, `y = −2 Im ρ₀₁`, `z = ρ₀₀ − ρ₁₁` (`X, Y, Z` the Pauli matrices). Prove `x² + y² + z² ≤ 1`.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · bloch_ball
  Notation: a = ρ₀₀, b = ρ₁₁, w = ρ₀₁. Goal: (2 Re w)² + (−2 Im w)² + (Re a − Re b)² ≤ 1.
  1. Collect the facts of the state, one `have` each:
       hdet : 0 ≤ ρ.m.det                                                  R1 → R2
       htr  : ρ.m.trace = 1                                                R3
       h10  : ρ.m 1 0 = star (ρ.m 0 1)                                     R4 → R5 → R6
  2. The diagonal is real, one `have` each, each proved by                 R4 → R5 → R7 → R8 → R9
       h00 : (ρ.m 0 0).im = 0          h11 : (ρ.m 1 1).im = 0
  3. Expand hdet: 2×2 determinant, substitute h10, split the `≤` on ℂ:     R10 → R11 → R12
  4. Expand htr, then take its real part as a new fact htr':               R13 → R7
  5. Real parts of hdet and htr' in one `simp`, with Complex.mul_re, h00, h11:
                                                                           R17 (does R14, R15, R16)
     hdet (now last in the context) has hdet.1 : Re w * Re w + Im w * Im w ≤ Re a * Re b,
     i.e. |w|² ≤ ab; htr' is Re a + Re b = 1.
  6. Unfold blochX, blochY, blochZ in the goal:                            R18
  7. Close with the real half of hdet:                                     R19
-/
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
H2. Collect `hdet := ρ.psd.det_nonneg` (R1, R2), `htr := ρ.tr'` (R3), `h10 : ρ.m 1 0 = star (ρ.m 0 1)`
    (R4–R6), and `(ρ.m 0 0).im = 0`, `(ρ.m 1 1).im = 0` (imaginary part of the Hermitian condition at
    `(0,0)`, `(1,1)`: R7–R9). Expand `det`/`trace` for `Fin 2`, take real parts, hand it to `nlinarith`.
H3. `rw [Matrix.det_fin_two, h10, Complex.nonneg_iff] at hdet; rw [Matrix.trace_fin_two] at htr`;
    `have htr' := congrArg Complex.re htr`; `simp [Complex.mul_re, h00, h11] at hdet htr'`;
    `simp only [blochX, blochY, blochZ]`; `nlinarith [hdet.1]`.
-/
