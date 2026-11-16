/- H102 | Thermodynamic limit of the Ising ring | 1-1.5 h | Tendsto, log, dominant eigenvalue, transfer matrix, Filter.Tendsto.congr', mathlib
GOAL
  The zero-field Ising ring of `N` spins (`K = βJ`) has partition function `Z_N = tr (T0 K ^ N)`.
  Prove the free energy per spin converges: `(log Z_N) / N → log (2 cosh K)` as `N → ∞`, so
  `f = -kB T log (2 cosh βJ)`. The eigenvalue `2 cosh K` of `T0` dominates the other, `2 sinh K`.

REFERENCE
  #check tendsto_pow_atTop_nhds_zero_of_abs_lt_one  -- |r| < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)
  #check Filter.Tendsto.log         -- Tendsto f l (𝓝 x) → x ≠ 0 → Tendsto (fun y => log (f y)) l (𝓝 (log x))
  #check Filter.Tendsto.div_atTop   -- Tendsto f l (𝓝 a) → Tendsto g l atTop → Tendsto (fun y => f y / g y) l (𝓝 0)
  #check tendsto_natCast_atTop_atTop  -- Tendsto (Nat.cast : ℕ → ℝ) atTop atTop
  #check Filter.Tendsto.const_add   -- `hf.const_add b : Tendsto (fun y => b + f y) l (𝓝 (b + a))`
  example (f g : ℕ → ℝ) (a : ℝ) (h : Tendsto f atTop (𝓝 a)) (e : f =ᶠ[atTop] g) : Tendsto g atTop (𝓝 a) := h.congr' e
  example (f g : ℕ → ℝ) (e : ∀ N, 1 ≤ N → f N = g N) : f =ᶠ[atTop] g := by filter_upwards [eventually_ge_atTop 1] with N hN; exact e N hN
  #check Real.log_mul               -- x ≠ 0 → y ≠ 0 → log (x * y) = log x + log y    (and `Real.log_pow`)
  #check Real.cosh_sq               -- cosh x ^ 2 = sinh x ^ 2 + 1
  #check pow_lt_one₀                -- 0 ≤ a → a < 1 → n ≠ 0 → a ^ n < 1
  -- Milestone 1 is M166: `Matrix.mul_apply`, `Fin.sum_univ_two`, `Real.cosh_eq`, `Real.sinh_eq`, `fin_cases`
NOTE: `𝓝 a` = neighbourhoods of `a` ("→ a"), `atTop` = "N → ∞", `f =ᶠ[atTop] g` = "f N = g N for all large N". At `N = 0` the quotient is junk (`x / 0 = 0` in Lean).
-/
import Mathlib

open Real Filter Topology

namespace H102

-- BEGIN SPEC
/-- Zero-field transfer matrix of the Ising chain, `K = β J` (same as M166). By H097 the ring
partition function of `N` spins at `h = 0` is `Matrix.trace (T0 K ^ N)`. -/
noncomputable def T0 (K : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp K, Real.exp (-K); Real.exp (-K), Real.exp K]
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem trace_pow (K : ℝ) (n : ℕ) :
    Matrix.trace (T0 K ^ n) = (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n := by
  -- WHY: the trace of `T^(n+1)` is not a function of the trace of `T^n`; induct on the whole matrix.
  have key : T0 K ^ n =
      !![((2 * cosh K) ^ n + (2 * sinh K) ^ n) / 2, ((2 * cosh K) ^ n - (2 * sinh K) ^ n) / 2;
        ((2 * cosh K) ^ n - (2 * sinh K) ^ n) / 2, ((2 * cosh K) ^ n + (2 * sinh K) ^ n) / 2] := by
    induction n with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [T0, Matrix.mul_apply, Fin.sum_univ_two, cosh_eq, sinh_eq, pow_succ] <;> ring
  rw [key]
  simp [Matrix.trace, Fin.sum_univ_two]

-- MILESTONE (optional: change or delete)
theorem abs_lam_minus_lt (K : ℝ) : |2 * Real.sinh K| < 2 * Real.cosh K := by
  rw [abs_mul, abs_two]
  have h := Real.cosh_sq K
  have hc := Real.cosh_pos K
  nlinarith [abs_nonneg (Real.sinh K), sq_abs (Real.sinh K)]

-- MILESTONE (optional: change or delete)
theorem limit_lemma (lp lm : ℝ) (h0 : 0 < lp) (h1 : |lm| < lp) :
    Tendsto (fun N : ℕ => Real.log (lp ^ N + lm ^ N) / N) atTop (𝓝 (Real.log lp)) := by
  set r := lm / lp with hr
  have hr1 : |r| < 1 := by rw [hr, abs_div, abs_of_pos h0, div_lt_one h0]; exact h1
  have hpos : ∀ N : ℕ, 0 < 1 + r ^ N := by
    intro N
    rcases N with _ | N
    · norm_num
    · have h1 : |r| ^ (N + 1) < 1 := pow_lt_one₀ (abs_nonneg r) hr1 (by omega)
      have h2 := neg_abs_le (r ^ (N + 1))
      rw [abs_pow] at h2
      linarith
  have heq : ∀ N : ℕ, lp ^ N + lm ^ N = lp ^ N * (1 + r ^ N) := by
    intro N
    rw [hr, div_pow]
    field_simp
  have hlim : Tendsto (fun N : ℕ => Real.log (1 + r ^ N)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr1).const_add 1
    simpa using this.log (by norm_num)
  have h2 : Tendsto (fun N : ℕ => Real.log lp + Real.log (1 + r ^ N) / N) atTop
      (𝓝 (Real.log lp)) := by
    simpa using (hlim.div_atTop tendsto_natCast_atTop_atTop).const_add (Real.log lp)
  -- WHY: at `N = 0` the two sequences differ (`log lp` vs `x / 0 = 0`); they agree only for `N ≥ 1`.
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [heq, Real.log_mul (by positivity) (hpos N).ne', Real.log_pow]
  field_simp

-- BEGIN SPEC
theorem free_energy_per_spin (K : ℝ) :
    Tendsto (fun N : ℕ => Real.log (Matrix.trace (T0 K ^ N)) / N) atTop
      (𝓝 (Real.log (2 * Real.cosh K))) :=
-- END SPEC
  by
    simp_rw [trace_pow]
    exact limit_lemma _ _ (by positivity) (abs_lam_minus_lt K)

end H102

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Z_N = λ₊ᴺ + λ₋ᴺ` with `λ₊ = 2 cosh K > |λ₋|`, `λ₋ = 2 sinh K` (milestone 1 is M166). Factor out
    the big one: `λ₊ᴺ + λ₋ᴺ = λ₊ᴺ (1 + rᴺ)` with `r = λ₋/λ₊`, `|r| < 1`. Then
    `log Z_N / N = log λ₊ + log (1 + rᴺ) / N`, and the second term → 0.
H2. `limit_lemma`: show `0 < 1 + r ^ N` for every `N` (`N = 0` by `norm_num`; else `|r| ^ N < 1` and
    `neg_abs_le`), `log (1 + rᴺ) → log 1 = 0` (`Tendsto.const_add`, `Tendsto.log`), divide by `N → ∞`
    (`div_atTop`), add `log lp`, and transfer to the original sequence with `congr'` on `N ≥ 1`.
    `abs_lam_minus_lt`: `have := Real.cosh_sq K; have := Real.cosh_pos K`, then
    `nlinarith [abs_nonneg (2 * Real.sinh K), sq_abs (2 * Real.sinh K)]`.
H3. `refine h2.congr' ?_; filter_upwards [eventually_ge_atTop 1] with N hN`, then
    `rw [heq, Real.log_mul (by positivity) (hpos N).ne', Real.log_pow]; field_simp`, where
    `heq : lp ^ N + lm ^ N = lp ^ N * (1 + (lm / lp) ^ N)`. Main: `simp_rw [trace_pow]; apply limit_lemma`.
-/
