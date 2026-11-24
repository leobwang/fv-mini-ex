/- H076 | The Bloch sphere: pure iff on the sphere | 1-2 h | MState, Ket construction, Bloch vector, 2×2 Hermitian, physlib
GOAL
  A qubit state `ρ` is pure (`ρ = |ψ⟩⟨ψ|` for some ket `ψ`) iff its Bloch vector
  `r = (blochX ρ, blochY ρ, blochZ ρ)` has length 1. For `←` you construct the ket yourself.
BANNED: MState.pure_iff_purity_one, MState.pure_of_constant_spectrum, MState.pure_iff_constant_spectrum, MState.pure_iff_rank_eq_one

GUIDE
  Entries R1–R47: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · herm_facts   (MILESTONE 1: used in `sphere_iff` and in `bloch_sphere`)
  1. Collect the two sources and expand the trace:                              R1, R2, R3 (`at htr`)
  2. Split the four conjuncts; the first is a Hermiticity equation, flipped:    R5 with R4 (`hH.apply 1 0`)
  3. Each diagonal entry is real: im of Hermiticity at `(i, i)`, simplify,
     solve `-x = x`:                                                            R4 → R6 → R7 → R8
  4. Real parts add to 1: re of `htr`, simplified into the goal:                R6 inside R9
-/
-- MILESTONE (optional: change or delete)
theorem herm_facts (ρ : MState (Fin 2)) :
    ρ.m 1 0 = starRingEnd ℂ (ρ.m 0 1) ∧ (ρ.m 0 0).im = 0 ∧ (ρ.m 1 1).im = 0 ∧
      (ρ.m 0 0).re + (ρ.m 1 1).re = 1 := by
  have hH := ρ.Hermitian
  have htr := ρ.tr'
  rw [Matrix.trace_fin_two] at htr
  refine ⟨(hH.apply 1 0).symm, ?_, ?_, ?_⟩
  · have := congrArg Complex.im (hH.apply 0 0)
    simp at this
    linarith
  · have := congrArg Complex.im (hH.apply 1 1)
    simp at this
    linarith
  · simpa using congrArg Complex.re htr

/- SKELETON · sphere_iff   (MILESTONE 2: used in `pure_on_sphere` and in `bloch_sphere`)
  1. From `herm_facts ρ` keep only `hs : Re ρ₀₀ + Re ρ₁₁ = 1`:                  R10
  2. `normSq` → real and imaginary parts:                                       R11
  3. Unfold `blochX`, `blochY`, `blochZ`:                                       R12
  4. Both directions, each closed by polynomial arithmetic with `hs`:           R13 (`<;> intro h`), R14
-/
-- MILESTONE (optional: change or delete)
/-- on the sphere ⇔ `det ρ = 0`, i.e. `|ρ₀₁|² = ρ₀₀ ρ₁₁` -/
theorem sphere_iff (ρ : MState (Fin 2)) :
    blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 = 1 ↔
      Complex.normSq (ρ.m 0 1) = (ρ.m 0 0).re * (ρ.m 1 1).re := by
  obtain ⟨-, -, -, hs⟩ := herm_facts ρ
  rw [Complex.normSq_apply]
  simp only [blochX, blochY, blochZ]
  constructor <;> intro h <;> nlinarith

/- SKELETON · pure_on_sphere   (MILESTONE 3: the `→` direction of `bloch_sphere`)
  1. Turn the sphere equation into the `normSq` equation with MILESTONE 2:      R15 (`rw [sphere_iff]`)
  2. One `simp only` with the entries of `pure ψ` and the `normSq` rules:       R16, R17, R18, R19, R20
-/
-- MILESTONE (optional: change or delete)
theorem pure_on_sphere (ψ : Ket (Fin 2)) :
    blochX (MState.pure ψ) ^ 2 + blochY (MState.pure ψ) ^ 2 + blochZ (MState.pure ψ) ^ 2 = 1 := by
  rw [sphere_iff]
  simp only [MState.pure_apply, Complex.normSq_mul, Complex.normSq_conj, Complex.mul_conj,
    Complex.ofReal_re]

/- SKELETON · exists_ket   (MILESTONE 4: the ket for the `←` direction of `bloch_sphere`)
  1. Split `0 ≤ a` into `a = 0` and `0 < a`:                                    R21
  2. Case `a = 0`: `hz0 : z = 0` and `hb : b = 1`, then the ket `|1⟩`:          R22, R8
       provide `Ket.basis 1` with `refine ⟨x, ?_, ?_, ?_⟩` (TACTIC_STATES), then   R23 with `hz0, hb`
  3. Case `0 < a`: facts over ℂ for `field_simp` and the products:
       ha' : (a : ℂ) ≠ 0,  hsa : ((√a : ℝ) : ℂ) ≠ 0,  hsq : ↑√a * ↑√a = ↑a     R24, R25, R26
  4. The ket `ψ = (√a, conj z / √a)`; its normalization proof:                  R28, R27
       one `simp only` (sum, entries, `‖·‖²` → `normSq`, `normSq` rules, `hz`,
       `√a * √a = a`) leaves `a + a * b / a = 1`:                               R29, R30, R31, R32, R33, R18, R26
       then cancel and finish:                                                  R34, R8
  5. `refine ⟨ψ, ?_, ?_, ?_⟩` (TACTIC_STATES); in each of the three amplitude
     goals unfold `ψ` and `Ket.apply`, then the conj rules:                     R28, R23, R30, R35, R36, R37
       `ψ₀ conj ψ₀ = a`:   `simp` with `hsq`
       `ψ₀ conj ψ₁ = z`:   R34
       `ψ₁ conj ψ₁ = b`:   R38, R39, R19, rw [hz, hsq], R40, R34
-/
-- MILESTONE (optional: change or delete)
/-- the key construction: a ket with prescribed `|ψ₀|² = a`, `ψ₀ conj ψ₁ = z`, `|ψ₁|² = b` -/
theorem exists_ket (a b : ℝ) (z : ℂ) (ha : 0 ≤ a) (hab : a + b = 1) (hz : Complex.normSq z = a * b) :
    ∃ ψ : Ket (Fin 2), ψ 0 * starRingEnd ℂ (ψ 0) = a ∧ ψ 0 * starRingEnd ℂ (ψ 1) = z ∧
      ψ 1 * starRingEnd ℂ (ψ 1) = b := by
  rcases ha.eq_or_lt with rfl | ha
  · have hz0 : z = 0 := by simpa using hz
    have hb : b = 1 := by linarith
    refine ⟨Ket.basis 1, ?_, ?_, ?_⟩ <;> simp [Ket.basis, Ket.apply, hz0, hb]
  · have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hsa : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
    have hsq : ((Real.sqrt a : ℝ) : ℂ) * (Real.sqrt a : ℝ) = a := by
      exact_mod_cast Real.mul_self_sqrt ha.le
    let ψ : Ket (Fin 2) :=
      ⟨![(Real.sqrt a : ℂ), starRingEnd ℂ z / (Real.sqrt a : ℂ)], by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          ← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_conj,
          hz, Real.mul_self_sqrt ha.le]
        field_simp
        linarith⟩
    refine ⟨ψ, ?_, ?_, ?_⟩
    · simp [ψ, Ket.apply, hsq]
    · simp only [ψ, Ket.apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀,
        Complex.conj_conj, Complex.conj_ofReal]
      field_simp
    · simp only [ψ, Ket.apply, Matrix.cons_val_one, Matrix.cons_val_zero, map_div₀,
        Complex.conj_conj, Complex.conj_ofReal]
      rw [div_mul_div_comm, mul_comm (starRingEnd ℂ z), Complex.mul_conj, hz, hsq]
      push_cast
      field_simp

/- SKELETON · bloch_sphere
  Prove the four MILESTONES above first: step 2 uses MILESTONE 3, steps 3–5 use 1, 2 and 4.
  1. Split the `↔`:                                                             R13
  2. `→`: introduce the ket and substitute `ρ`, then MILESTONE 3:               R41, exact pure_on_sphere ψ
  3. `←`: `intro h`; turn `h` into the `normSq` equation (MILESTONE 2) and
     take all four facts of MILESTONE 1:                                        R42, R10
  4. `ha : 0 ≤ Re ρ₀₀` (not given!) from `|z|² = a b ≥ 0` and `a + b = 1`:      R43
  5. Get `ψ` and `e00, e01, e11` from MILESTONE 4:                              R10 (`obtain`)
  6. `key : ∀ i j : Fin 2, ρ.m i j = ψ i * conj (ψ j)`:                         R44, then R5 (`e01.symm`)
       entry (0,0): rw [e00], then R45 as a term with `h0`;  entry (1,1) the same
       entry (1,0): rw [h10, ← e01], then `simp [mul_comm]`                     R46, R36, R39
  7. `ρ = pure ψ`: provide `ψ`, matrices, entries, then rw [MState.pure_apply, key]   R47, ext i j, R16
-/
-- BEGIN SPEC
theorem bloch_sphere (ρ : MState (Fin 2)) :
    (∃ ψ : Ket (Fin 2), ρ = MState.pure ψ) ↔ blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 = 1 :=
-- END SPEC
  by
    constructor
    · rintro ⟨ψ, rfl⟩
      exact pure_on_sphere ψ
    · intro h
      rw [sphere_iff] at h
      obtain ⟨h10, h0, h1, hs⟩ := herm_facts ρ
      -- WHY: `a ≥ 0` is not assumed; it follows from `|z|² = a b ≥ 0` and `a + b = 1`.
      have ha : 0 ≤ (ρ.m 0 0).re := by nlinarith [Complex.normSq_nonneg (ρ.m 0 1)]
      obtain ⟨ψ, e00, e01, e11⟩ := exists_ket _ _ _ ha hs h
      have key : ∀ i j : Fin 2, ρ.m i j = ψ i * starRingEnd ℂ (ψ j) := by
        simp only [Fin.forall_fin_two]
        refine ⟨⟨?_, e01.symm⟩, ?_, ?_⟩
        · rw [e00]; exact Complex.ext rfl h0
        · rw [h10, ← e01]; simp [mul_comm]
        · rw [e11]; exact Complex.ext rfl h1
      refine ⟨ψ, MState.ext_m ?_⟩
      ext i j
      rw [MState.pure_apply, key]

end H076

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Name `a = Re ρ₀₀`, `b = Re ρ₁₁`, `z = ρ₀₁`. Hermiticity and trace 1 give `ρ₁₀ = conj z`, a real
    diagonal and `a + b = 1`, so `|r|² = 4|z|² + (a − b)² = 1 + 4 (|z|² − a b)`: on the sphere iff
    `|z|² = a b` (`sphere_iff`). A pure state has `|z|² = |ψ₀|² |ψ₁|² = a b`; for `←` you build the ket.
H2. Prove the milestones in order (see the SKELETONs). `→`: `rw [sphere_iff]` and one `simp only` with
    `MState.pure_apply` and the `normSq` lemmas (R16–R20). `←`: `0 ≤ a` by `nlinarith` with
    `Complex.normSq_nonneg`; the ket from `exists_ket`; equality of states with `MState.ext_m` and `ext i j`,
    using a `∀ i j` fact proved with `Fin.forall_fin_two` (not `fin_cases`: cheatsheet, Traps).
H3. `exists_ket`: `rcases ha.eq_or_lt with rfl | ha`. If `a = 0`: `z = 0` (`simpa using hz`), take `Ket.basis 1`.
    If `0 < a`: `let ψ : Ket (Fin 2) := ⟨![(Real.sqrt a : ℂ), starRingEnd ℂ z / (Real.sqrt a : ℂ)], by …⟩`;
    the normalization `simp only` leaves `a + a * b / a = 1`, then `field_simp; linarith`. First put the
    side conditions in the context over ℂ:
    `have hsa : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'`, and likewise
    `hsq : ((Real.sqrt a : ℝ) : ℂ) * (Real.sqrt a : ℝ) = a` from `Real.mul_self_sqrt ha.le`.
-/
