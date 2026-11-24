/- H086 | Grover's amplitude formula | 1.5-2 h | Grover iteration, invariant subspace, induction, trigonometry, Real.arcsin, field_simp, linear_combination, mathlib
GOAL
  Search `N ≥ 2` items with one marked item `m`. Start from the uniform state `1/√N` and apply the Grover
  step `k` times (oracle: flip the sign of amplitude `m`; diffusion: `vᵢ ↦ 2·mean(v) − vᵢ`). Prove that
  the marked amplitude is `sin((2k+1)θ)` and every other one is `cos((2k+1)θ)/√(N−1)`, where `θ = arcsin(1/√N)`.

REFERENCE
  -- amplitudes are real vectors `Fin N → ℝ`; in `Real.sqrt (N - 1)` the `N` is cast to `ℝ`, so `N - 1` is real subtraction
  -- `√x` is notation for `Real.sqrt x` (the glosses below use `√`, the spec writes `Real.sqrt`)
  #check Real.sin_arcsin    -- -1 ≤ x → x ≤ 1 → sin (arcsin x) = x
  #check Real.cos_arcsin    -- (x) : cos (arcsin x) = √(1 - x ^ 2)
  #check Real.sqrt_div      -- 0 ≤ x → ∀ y, √(x / y) = √x / √y          (and `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`)
  #check Real.sin_add       -- sin (x + y) = sin x * cos y + cos x * sin y     (and `Real.cos_add`)
  #check Real.sin_two_mul   -- sin (2 * x) = 2 * sin x * cos x     (and `Real.cos_two_mul : cos (2x) = 2 cos x ^ 2 - 1`)
  #check Finset.sum_ite_eq' -- ∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0
  example (x y : ℝ) (h : x ^ 2 = 2) : x ^ 2 * y = 2 * y := by linear_combination y * h   -- goal = linear combo of hyps
  example (x : ℝ) (hx : x ≠ 0) : 1 / x * x = 1 := by field_simp    -- clears denominators it knows are ≠ 0
  example (n : ℕ) : (2 * ((n + 1 : ℕ) : ℝ) + 1) = (2 * n + 1) + 2 := by push_cast; ring
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

-- MILESTONE (optional: change or delete)
/-- the Grover step keeps the form "`a` at `m`, `b` elsewhere" and acts linearly on `(a, b)` -/
theorem step_form (m : Fin N) (a b : ℝ) :
    diffuse (oracle m (fun i => if i = m then a else b))
      = fun i => if i = m then a * (1 - 2 / N) + 2 * (N - 1) / N * b
          else -(2 / N) * a + (1 - 2 / N) * b := by
  sorry

-- MILESTONE (optional: change or delete)
theorem sin_cos_theta (hN : 2 ≤ N) :
    Real.sin (Real.arcsin (1 / Real.sqrt N)) = 1 / Real.sqrt N ∧
      Real.cos (Real.arcsin (1 / Real.sqrt N)) = Real.sqrt (N - 1) / Real.sqrt N := by
  sorry

-- MILESTONE (optional: change or delete)
/-- in the coordinates `(sin φ, cos φ / √(N−1))` the step is a rotation by `2θ` (marked part) -/
theorem rot_sin (hN : 2 ≤ N) (φ : ℝ) :
    Real.sin φ * (1 - 2 / N) + 2 * (N - 1) / N * (Real.cos φ / Real.sqrt (N - 1))
      = Real.sin (φ + 2 * Real.arcsin (1 / Real.sqrt N)) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- ... and the unmarked part -/
theorem rot_cos (hN : 2 ≤ N) (φ : ℝ) :
    -(2 / N) * Real.sin φ + (1 - 2 / N) * (Real.cos φ / Real.sqrt (N - 1))
      = Real.cos (φ + 2 * Real.arcsin (1 / Real.sqrt N)) / Real.sqrt (N - 1) := by
  sorry

-- BEGIN SPEC
theorem grover_amplitude (hN : 2 ≤ N) (m : Fin N) (k : ℕ) :
    grover m k = fun i => if i = m then Real.sin ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N))
      else Real.cos ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N)) / Real.sqrt (N - 1) :=
-- END SPEC
  sorry

end H086

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct on `k`. The state always has the form "`a` at `m`, `b` elsewhere" (milestone 1), and in the coordinates `a = sin φ`, `b = cos φ / √(N−1)` one Grover step adds `2θ` to `φ` (milestones 3 and 4).
H2. Milestone 1: after the oracle the sum is `−a + (N−1)b`; write each summand as `b + (if j = m then −a − b else 0)` and use `Finset.sum_ite_eq'` (the constant part `∑ j : Fin N, b = N * b` is `Finset.sum_const` + `Finset.card_univ` + `Fintype.card_fin` + `nsmul_eq_mul`, or `simp`), then case on `i = m` and `field_simp; ring`. Milestone 2: `sin_arcsin` needs `0 ≤ 1/√N ≤ 1`; for the cosine, `1 − 1/N = (N−1)/N` and `Real.sqrt_div`. Milestones 3–4: expand with `sin_add`/`cos_add`, `sin_two_mul`, `cos_two_mul`, substitute milestone 2, `field_simp`, and finish with `linear_combination` against `h1 : √(N−1)^2 = N−1` (and `√N^2 = N`).
H3. Inductive step: `rw [grover, ih, step_form]; funext i`, rewrite `(2(k+1)+1)θ = (2k+1)θ + 2θ` (`push_cast; ring`), then `rw [← rot_sin hN, ← rot_cos hN]`. Milestone 3 ends with `linear_combination (-(N:ℝ) * (2 * sin φ * √(N-1) + 2 * cos φ)) * h1` after `rw [h2]`; milestone 4 with `linear_combination (-2 * (N:ℝ) * cos φ) * h1`.
-/
