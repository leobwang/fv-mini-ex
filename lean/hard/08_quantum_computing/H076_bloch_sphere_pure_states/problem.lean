/- H076 | The Bloch sphere: pure iff on the sphere | 1-2 h | MState, Ket construction, Bloch vector, 2×2 Hermitian, physlib
GOAL
  A qubit state `ρ` is pure (`ρ = |ψ⟩⟨ψ|` for some ket `ψ`) iff its Bloch vector
  `r = (blochX ρ, blochY ρ, blochZ ρ)` has length 1. For `←` you construct the ket yourself.

REFERENCE
  -- `ρ : MState (Fin 2)` is a qubit density matrix; `ρ.m : Matrix (Fin 2) (Fin 2) ℂ` is its raw matrix
  #check MState.pure_apply    -- (MState.pure ψ).m i j = ψ i * conj (ψ j)     (`starRingEnd ℂ` is conj)
  #check MState.Hermitian     -- ρ.m.IsHermitian;   `ρ.Hermitian.apply i j : star (ρ.m j i) = ρ.m i j`
  #check MState.tr'           -- ρ.m.trace = 1      (with `Matrix.trace_fin_two : A.trace = A 0 0 + A 1 1`)
  #check MState.ext_m         -- ρ₁.m = ρ₂.m → ρ₁ = ρ₂
  #check Ket.normalized       -- ∑ x, Complex.normSq (ψ x) = 1     (`ψ i` is the i-th amplitude)
  example : Ket (Fin 2) := ⟨![1, 0], by simp⟩   -- a ket = amplitude vector + proof `∑ ‖vᵢ‖ ^ 2 = 1`
  #check Complex.mul_conj     -- z * conj z = ↑(normSq z);   `Complex.normSq_apply`: = z.re*z.re + z.im*z.im
  #check Real.mul_self_sqrt   -- 0 ≤ x → √x * √x = x
  -- `simp only [Fin.forall_fin_two]` splits `∀ i j : Fin 2, P i j` into its four cases
BANNED: MState.pure_iff_purity_one, MState.pure_of_constant_spectrum, MState.pure_iff_constant_spectrum, MState.pure_iff_rank_eq_one
NOTE: `fin_cases` leaves indices as `⟨0, _⟩`, which `rw` with `ψ 0` lemmas cannot see; prefer `Fin.forall_fin_two`.
-/
import QuantumInfo.States.Mixed.MState

open scoped Matrix

namespace H076

-- BEGIN SPEC
/-- Bloch vector `r = (2 Re ρ₀₁, −2 Im ρ₀₁, ρ₀₀ − ρ₁₁)`, so that `ρ = (1 + r·σ)/2` -/
def blochX (ρ : MState (Fin 2)) : ℝ := 2 * (ρ.m 0 1).re
def blochY (ρ : MState (Fin 2)) : ℝ := -2 * (ρ.m 0 1).im
def blochZ (ρ : MState (Fin 2)) : ℝ := (ρ.m 0 0).re - (ρ.m 1 1).re
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem herm_facts (ρ : MState (Fin 2)) :
    ρ.m 1 0 = starRingEnd ℂ (ρ.m 0 1) ∧ (ρ.m 0 0).im = 0 ∧ (ρ.m 1 1).im = 0 ∧
      (ρ.m 0 0).re + (ρ.m 1 1).re = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- on the sphere ⇔ `det ρ = 0`, i.e. `|ρ₀₁|² = ρ₀₀ ρ₁₁` -/
theorem sphere_iff (ρ : MState (Fin 2)) :
    blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 = 1 ↔
      Complex.normSq (ρ.m 0 1) = (ρ.m 0 0).re * (ρ.m 1 1).re := by
  sorry

-- MILESTONE (optional: change or delete)
theorem pure_on_sphere (ψ : Ket (Fin 2)) :
    blochX (MState.pure ψ) ^ 2 + blochY (MState.pure ψ) ^ 2 + blochZ (MState.pure ψ) ^ 2 = 1 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- the key construction: a ket with prescribed `|ψ₀|² = a`, `ψ₀ conj ψ₁ = z`, `|ψ₁|² = b` -/
theorem exists_ket (a b : ℝ) (z : ℂ) (ha : 0 ≤ a) (hab : a + b = 1) (hz : Complex.normSq z = a * b) :
    ∃ ψ : Ket (Fin 2), ψ 0 * starRingEnd ℂ (ψ 0) = a ∧ ψ 0 * starRingEnd ℂ (ψ 1) = z ∧
      ψ 1 * starRingEnd ℂ (ψ 1) = b := by
  sorry

-- BEGIN SPEC
theorem bloch_sphere (ρ : MState (Fin 2)) :
    (∃ ψ : Ket (Fin 2), ρ = MState.pure ψ) ↔ blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 = 1 :=
-- END SPEC
  sorry

end H076

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `a = Re ρ₀₀`, `b = Re ρ₁₁`, `z = ρ₀₁`. Hermiticity and trace 1 give `ρ₁₀ = conj z`, real
    diagonal and `a + b = 1`; then `|r|² = 1` is the same as `|z|² = a b` (`sphere_iff`, by `nlinarith`).
H2. `→`: for `ρ = pure ψ`, `|z|² = |ψ₀|²|ψ₁|²` (`Complex.normSq_mul`, `Complex.normSq_conj`, `Complex.mul_conj`).
    `←`: `|z|² = a b ≥ 0` with `a + b = 1` forces `a ≥ 0`. Get a ket from `exists_ket` and compare all
    four entries (`MState.ext_m`, `ext i j`, then a `∀ i j` fact proved with `Fin.forall_fin_two`).
H3. `exists_ket`: split `ha.eq_or_lt`. If `a = 0` then `z = 0`, take `Ket.basis 1`. If `a > 0` take
    `⟨![(√a : ℂ), conj z / √a], _⟩`; normalization is `a + normSq z / a = a + b = 1`
    (`Complex.normSq_div`, `Complex.normSq_ofReal`, `Complex.normSq_conj`, `Real.mul_self_sqrt`, `field_simp`).
    `field_simp` needs the side conditions as hypotheses over ℂ; move them from ℝ with `exact_mod_cast`:
    `have : ((√a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'`, and likewise `√a * √a = a`.
-/
