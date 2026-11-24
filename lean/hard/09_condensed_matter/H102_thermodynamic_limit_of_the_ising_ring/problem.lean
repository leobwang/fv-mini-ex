/- H102 | Thermodynamic limit of the Ising ring | 1-1.5 h | Tendsto, log, dominant eigenvalue, transfer matrix, Filter.Tendsto.congr', mathlib
GOAL
  The zero-field Ising ring of `N` spins (`K = βJ`) has partition function `Z_N = tr (T0 K ^ N)`.
  Prove the free energy per spin converges: `(log Z_N) / N → log (2 cosh K)` as `N → ∞`, so
  `f = -kB T log (2 cosh βJ)`. The eigenvalue `2 cosh K` of `T0` dominates the other, `2 sinh K`.

GUIDE
  Entries R1–R40: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · trace_pow   (milestone 1: prove it first; free_energy_per_spin uses it)
  1. The trace of `T0 K ^ (n + 1)` is not a function of the trace of `T0 K ^ n`: prove the closed form
     of the whole matrix first, with `c := (2 * cosh K) ^ n`, `s := (2 * sinh K) ^ n` written out,
       key : T0 K ^ n = !![(c + s) / 2, (c - s) / 2; (c - s) / 2, (c + s) / 2]
     proof: induction on `n`:                                                                 R1
       zero: matrix equation → four entries, then `simp`:                ext, fin_cases, R2, R3, R4
       succ: `T0 K ^ (n + 1)` → (closed form for `n`) * `T0 K`:                         R5, rw [ih]
             four entries; `simp` with `T0`, the product, `cosh`/`sinh` → `exp` and `pow_succ`;
             `ring` closes what is left:                      ext, fin_cases, R6, R7, R8, R5, ring
  2. rw [key], then the trace of a literal 2×2 matrix:                                        R9, R7
-/
-- MILESTONE (optional: change or delete)
theorem trace_pow (K : ℝ) (n : ℕ) :
    Matrix.trace (T0 K ^ n) = (2 * Real.cosh K) ^ n + (2 * Real.sinh K) ^ n := by
  sorry

/- SKELETON · abs_lam_minus_lt   (milestone 2: free_energy_per_spin uses it)
  1. `|2 * sinh K|` → `2 * |sinh K|`:                                                       R10, R11
  2. add `cosh K ^ 2 = sinh K ^ 2 + 1` and `0 < cosh K` to the context:                     R12, R13
  3. close with `nlinarith`, told how `|sinh K|` relates to `sinh K`:                       R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem abs_lam_minus_lt (K : ℝ) : |2 * Real.sinh K| < 2 * Real.cosh K := by
  sorry

/- SKELETON · limit_lemma   (milestone 3: free_energy_per_spin uses it)
  1. name the ratio `r := lm / lp`:                                                             R16
  2. hr1 : |r| < 1                                         proof: rw [hr], R17, R18, R19, then `h1`
  3. hpos : ∀ N : ℕ, 0 < 1 + r ^ N                 proof: `intro N`, R20; case 0: `norm_num`;
       case N + 1: `|r| ^ (N + 1) < 1` (R21, first argument R14, side goal R22),
       `-|r ^ (N + 1)| ≤ r ^ (N + 1)` (R23), R24 on the latter, then R25
  4. heq : ∀ N : ℕ, lp ^ N + lm ^ N = lp ^ N * (1 + r ^ N)   proof: `intro N`, rw [hr], R26, R27
  5. hlim : Tendsto (fun N : ℕ => Real.log (1 + r ^ N)) atTop (𝓝 0)
       proof: R28 on hr1 → R29 (add 1) → R30 (side goal `norm_num`) → R31
  6. h2 : Tendsto (fun N : ℕ => Real.log lp + Real.log (1 + r ^ N) / N) atTop (𝓝 (Real.log lp))
       proof: R33 on hlim with R32 → R29 (add `log lp`) → R31
  7. h2 matches the goal only for N ≥ 1 (at N = 0, `x / 0 = 0`): move it over:            R34, R35
       `(N : ℝ) ≠ 0` (R36); rw [heq], R37 (side goals: R36, and R38 on `hpos N`), R39; then R27
-/
-- MILESTONE (optional: change or delete)
theorem limit_lemma (lp lm : ℝ) (h0 : 0 < lp) (h1 : |lm| < lp) :
    Tendsto (fun N : ℕ => Real.log (lp ^ N + lm ^ N) / N) atTop (𝓝 (Real.log lp)) := by
  sorry

/- SKELETON · free_energy_per_spin
  0. Prove the milestones first: trace_pow (milestone 1), abs_lam_minus_lt (milestone 2) and
     limit_lemma (milestone 3). This proof only combines them.
  1. rewrite the trace with trace_pow under `fun N =>`:                                         R40
  2. the goal is now limit_lemma at `lp = 2 * cosh K`, `lm = 2 * sinh K`; its hypotheses are
     R36 and abs_lam_minus_lt
-/
-- BEGIN SPEC
theorem free_energy_per_spin (K : ℝ) :
    Tendsto (fun N : ℕ => Real.log (Matrix.trace (T0 K ^ N)) / N) atTop
      (𝓝 (Real.log (2 * Real.cosh K))) :=
-- END SPEC
  sorry

end H102

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Z_N = λ₊ᴺ + λ₋ᴺ` with `λ₊ = 2 cosh K > |λ₋|`, `λ₋ = 2 sinh K`. Factor out the big one:
    `λ₊ᴺ + λ₋ᴺ = λ₊ᴺ (1 + rᴺ)` with `r = λ₋/λ₊`, `|r| < 1`. Then `log Z_N / N = log λ₊ + log (1 + rᴺ) / N`
    for `N ≥ 1`, and the second term → 0. For `Z_N` itself, induct on the whole matrix `T0 K ^ n`.
H2. `trace_pow`: `have key` (skeleton) by `induction n with`; zero: `ext i j; fin_cases i <;> fin_cases j
    <;> simp`; succ: `rw [pow_succ, ih]`, the four entries by `simp [T0, Matrix.mul_apply, Fin.sum_univ_two,
    cosh_eq, sinh_eq, pow_succ] <;> ring`; then `rw [key]; simp [Matrix.trace, Fin.sum_univ_two]`.
    `abs_lam_minus_lt`: `rw [abs_mul, abs_two]`, `have := Real.cosh_sq K`, `have := Real.cosh_pos K`,
    `nlinarith [abs_nonneg (Real.sinh K), sq_abs (Real.sinh K)]`.
    `limit_lemma`: the facts `hr1`, `hpos`, `heq`, the limits `hlim`, `h2` (skeleton), then `congr'` on `N ≥ 1`.
H3. `hpos`, case `N + 1`: `pow_lt_one₀ (abs_nonneg r) hr1 (by omega)`, `neg_abs_le (r ^ (N + 1))`,
    `rw [abs_pow] at h2`, `linarith`. `hlim`: `simpa using this.log (by norm_num)` with
    `this := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr1).const_add 1`. `h2`:
    `simpa using (hlim.div_atTop tendsto_natCast_atTop_atTop).const_add (Real.log lp)`. Transfer:
    `refine h2.congr' ?_; filter_upwards [eventually_ge_atTop 1] with N hN`, `have : (N : ℝ) ≠ 0 := by
    positivity`, `rw [heq, Real.log_mul (by positivity) (hpos N).ne', Real.log_pow]; field_simp`.
    Main: `simp_rw [trace_pow]`, then `limit_lemma _ _ (by positivity) (abs_lam_minus_lt K)`.
-/
