/- H086 | Grover's amplitude formula | 1.5-2 h | Grover iteration, invariant subspace, induction, trigonometry, Real.arcsin, field_simp, linear_combination, mathlib
GOAL
  Search `N ≥ 2` items with one marked item `m`. Start from the uniform state `1/√N` and apply the Grover
  step `k` times (oracle: flip the sign of amplitude `m`; diffusion: `vᵢ ↦ 2·mean(v) − vᵢ`). Prove that
  the marked amplitude is `sin((2k+1)θ)` and every other one is `cos((2k+1)θ)/√(N−1)`, where `θ = arcsin(1/√N)`.

GUIDE
  Entries R1–R37: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H086

variable {N : ℕ}

-- BEGIN SPEC
/-- the oracle `O = I − 2|m⟩⟨m|`: flips the sign of the marked amplitude -/
def oracle (m : Fin N) (v : Fin N → ℝ) : Fin N → ℝ := fun i => if i = m then -v i else v i

/-- the diffusion `2|s⟩⟨s| − I` (inversion about the mean) -/
noncomputable def diffuse (v : Fin N → ℝ) : Fin N → ℝ := fun i => 2 * (∑ j, v j) / N - v i

/-- the state after `k` Grover iterations, starting from the uniform superposition -/
noncomputable def grover (m : Fin N) : ℕ → (Fin N → ℝ)
  | 0 => fun _ => 1 / Real.sqrt N
  | k + 1 => diffuse (oracle m (grover m k))
-- END SPEC

/- SKELETON · step_form   (MILESTONE 1: used in the inductive step of `grover_amplitude`)
  1. Fact `hsum : ∑ j, oracle m (fun i => if i = m then a else b) j = -a + (N - 1) * b`:
       a. pointwise helper `∀ j, oracle m (…) j = b + (if j = m then -a - b else 0)`:
          `intro j`, then case on `j = m` and unfold `oracle`                     R2, R3
       b. `simp only [helper, …]`: split the sum, collapse the spike, count the
          constant part                                                          R4 → R5 → R6 → R7 → R8 → R9 → R10
       c. what is left is `↑N * b + (-a - b) = -a + (↑N - 1) * b`                 ring
  2. Functions are equal pointwise                                               R1
  3. Unfold `diffuse` and substitute the sum                                     simp only [diffuse, hsum]
  4. Fact `(N : ℝ) ≠ 0` (for `field_simp`)                                       R11, R12
  5. Case on `i = m`; in each case unfold `oracle`, clear `/ ↑N`, finish         R2, R3, R13, ring
-/
-- MILESTONE (optional: change or delete)
/-- the Grover step keeps the form "`a` at `m`, `b` elsewhere" and acts linearly on `(a, b)` -/
theorem step_form (m : Fin N) (a b : ℝ) :
    diffuse (oracle m (fun i => if i = m then a else b))
      = fun i => if i = m then a * (1 - 2 / N) + 2 * (N - 1) / N * b
          else -(2 / N) * a + (1 - 2 / N) * b := by
  have hsum : ∑ j, oracle m (fun i => if i = m then a else b) j = -a + (N - 1) * b := by
    have : ∀ j, oracle m (fun i => if i = m then a else b) j
        = b + (if j = m then -a - b else 0) := by
      intro j; by_cases h : j = m <;> simp [oracle, h]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  funext i
  simp only [diffuse, hsum]
  have hm : (N : ℝ) ≠ 0 := by
    have := m.pos; positivity
  by_cases h : i = m <;> simp [oracle, h] <;> field_simp <;> ring

/- SKELETON · sin_cos_theta   (MILESTONE 2: sin θ and cos θ; used in rot_sin, rot_cos and the base case)
  1. Facts `(2 : ℝ) ≤ N` and `1 ≤ Real.sqrt N`                                   R14; R15, R16
  2. Split the `∧`                                                               constructor
  3. sin: reduce to the two bounds on `1 / √N`                                   R17
       `-1 ≤ 1 / √N`: first `0 < 1 / √N`, then                                   R12, R16
       `1 / √N ≤ 1`:                                                             R18, then step 1
  4. cos: one `rw` chain; the last rewrite makes both sides equal               R19 → R20 → R21 → R22 → R23 → R24
       (R23 is `1 - 1 / N = (N - 1) / N`, proved by R13)
-/
-- MILESTONE (optional: change or delete)
theorem sin_cos_theta (hN : 2 ≤ N) :
    Real.sin (Real.arcsin (1 / Real.sqrt N)) = 1 / Real.sqrt N ∧
      Real.cos (Real.arcsin (1 / Real.sqrt N)) = Real.sqrt (N - 1) / Real.sqrt N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; linarith
  constructor
  · apply Real.sin_arcsin
    · have : 0 < 1 / Real.sqrt N := by positivity
      linarith
    · rw [div_le_one (by positivity)]; exact h1
  · rw [Real.cos_arcsin, div_pow, Real.sq_sqrt (by linarith), one_pow,
      show (1 : ℝ) - 1 / N = (N - 1) / N by field_simp, Real.sqrt_div (by linarith)]

/- SKELETON · rot_sin   (MILESTONE 3: uses MILESTONE 2; used in the inductive step)
  1. `hs`, `hc` from `sin_cos_theta hN`                                          R25
  2. Facts: `(2 : ℝ) ≤ N` (R14); `h1 : √(N - 1) ^ 2 = N - 1`, `h2 : √N ^ 2 = N`  R21
     `0 < √(N - 1)`, `0 < √N` (so that `field_simp` may divide)                  R26
  3. Expand the right side, substitute sin θ and cos θ                           R27 → R29 → R30, rw [hs, hc]
  4. Clear denominators, then remove `√N ^ 2`                                    R13, rw [h2]
  5. Close against `h1`: read the goal, find the multiplier of `h1`              R31
-/
-- MILESTONE (optional: change or delete)
/-- in the coordinates `(sin φ, cos φ / √(N−1))` the step is a rotation by `2θ` (marked part) -/
theorem rot_sin (hN : 2 ≤ N) (φ : ℝ) :
    Real.sin φ * (1 - 2 / N) + 2 * (N - 1) / N * (Real.cos φ / Real.sqrt (N - 1))
      = Real.sin (φ + 2 * Real.arcsin (1 / Real.sqrt N)) := by
  obtain ⟨hs, hc⟩ := sin_cos_theta hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : Real.sqrt (N - 1) ^ 2 = N - 1 := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have h3 : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  have h4 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc]
  field_simp
  rw [h2]
  linear_combination (-(N : ℝ) * (2 * Real.sin φ * Real.sqrt (N - 1) + 2 * Real.cos φ)) * h1

/- SKELETON · rot_cos   (MILESTONE 4: as rot_sin; used in the inductive step)
  1–2. As in `rot_sin`                                                           R25, R14, R21, R26
  3. Expand with the cosine addition formula instead                             R28 → R29 → R30, rw [hs, hc]
  4. Clear denominators, then remove `√N ^ 2`                                    R13, rw [h2]
  5. Close against `h1` (a different multiplier)                                 R31
-/
-- MILESTONE (optional: change or delete)
/-- ... and the unmarked part -/
theorem rot_cos (hN : 2 ≤ N) (φ : ℝ) :
    -(2 / N) * Real.sin φ + (1 - 2 / N) * (Real.cos φ / Real.sqrt (N - 1))
      = Real.cos (φ + 2 * Real.arcsin (1 / Real.sqrt N)) / Real.sqrt (N - 1) := by
  obtain ⟨hs, hc⟩ := sin_cos_theta hN
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : Real.sqrt (N - 1) ^ 2 = N - 1 := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have h3 : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  have h4 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  rw [Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc]
  field_simp
  rw [h2]
  linear_combination (-2 * (N : ℝ) * Real.cos φ) * h1

/- SKELETON · grover_amplitude
  Prove the four MILESTONES above first: step 2 uses sin_cos_theta, step 3 uses step_form, rot_sin, rot_cos.
  1. Induct on `k`                                                               R32
  2. zero: `hs`, `hc` (R25), `(2 : ℝ) ≤ N` (R14), `0 < √(N - 1)` (R26)
       pointwise                                                                 R1
       unfold `grover m 0`, clean `(2 * ↑0 + 1) * θ`, substitute hs, hc          R33 + R34 in one `simp only`
       split the `if`: the `then` goal is `rfl`, the `else` goal                 R35, R13
  3. succ: unfold one step, use `ih`, apply MILESTONE 1                          rw [grover, ih, step_form] (R33, R37)
       pointwise                                                                 R1
       fact `e : (2 * ↑(k + 1) + 1) * θ = (2 * ↑k + 1) * θ + 2 * θ`             R36, ring
       rewrite with `e`, then MILESTONES 3 and 4 backwards                       R37
-/
-- BEGIN SPEC
theorem grover_amplitude (hN : 2 ≤ N) (m : Fin N) (k : ℕ) :
    grover m k = fun i => if i = m then Real.sin ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N))
      else Real.cos ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N)) / Real.sqrt (N - 1) :=
-- END SPEC
  by
    induction k with
    | zero =>
      obtain ⟨hs, hc⟩ := sin_cos_theta hN
      have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have h3 : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
      funext i
      simp only [grover, Nat.cast_zero, mul_zero, zero_add, one_mul, hs, hc]
      split_ifs
      · rfl
      · field_simp
    | succ k ih =>
      rw [grover, ih, step_form]
      funext i
      have e : (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.arcsin (1 / Real.sqrt N)
          = (2 * k + 1) * Real.arcsin (1 / Real.sqrt N) + 2 * Real.arcsin (1 / Real.sqrt N) := by
        push_cast; ring
      rw [e, ← rot_sin hN, ← rot_cos hN]

end H086

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct on `k`. The state always has the form "`a` at `m`, `b` elsewhere" (`step_form`), and in the
    coordinates `a = sin φ`, `b = cos φ / √(N−1)` one Grover step adds `2θ` to `φ` (`rot_sin`, `rot_cos`).
    The start `1/√N` is `φ = θ` (`sin_cos_theta`), so after `k` steps `φ = (2k+1)θ`.
H2. `step_form`: the sum after the oracle is `−a + (N−1)b`; write each summand as
    `b + (if j = m then −a − b else 0)` and collapse it with R4–R10, then `funext i`, case on `i = m`,
    `field_simp; ring`. `sin_cos_theta`: `Real.sin_arcsin` with the bounds `0 < 1/√N ≤ 1`; the cosine is
    `Real.cos_arcsin` and `1 − 1/N = (N−1)/N` with `Real.sqrt_div`. `rot_sin`/`rot_cos`: expand with
    `sin_add`/`cos_add`, `sin_two_mul`, `cos_two_mul`, substitute, `field_simp`, `rw [h2]`, and finish with
    `linear_combination` against `h1 : √(N−1)^2 = N−1`.
H3. Inductive step: `rw [grover, ih, step_form]; funext i`, then
    `rw [e, ← rot_sin hN, ← rot_cos hN]` with `e` proved by `push_cast; ring`.
    `rot_sin` ends with `linear_combination (-(N:ℝ) * (2 * Real.sin φ * Real.sqrt (N - 1) + 2 * Real.cos φ)) * h1`;
    `rot_cos` with `linear_combination (-2 * (N:ℝ) * Real.cos φ) * h1`.
-/
