/- H030 | √2 is irrational | 1-1.5 h | infinite descent, parity, casts, Irrational, mathlib
GOAL
  Prove `p² ≠ 2q²` for natural `q > 0` by infinite descent, then transfer it to the reals:
  `√2` is irrational.

BANNED: irrational_sqrt_two, Nat.Prime.irrational_sqrt, irrational_sqrt_natCast_iff, irrational_nrt_of_notint_nrt, irrational_sqrt_of_multiplicity_odd, irrational_sqrt_ratCast_iff, Irrational.of_pow, irrational_sqrt_intCast_iff

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H030

/- SKELETON · sq_ne_two_mul_sq   (MILESTONE: prove it first; sqrt_two_irrational uses it in its last step)
  1. Strong induction on `q`, keeping `p` general (`hq` moves into `ih` as `0 < m →`):   R1
  2. Assume the equation; the goal becomes `False`:                                      R2
       h : p ^ 2 = 2 * q ^ 2
  3. `p` is even: `2 ∣ p ^ 2` from `h`, then `2 ∣ p`, then substitute `p = 2 * k`:      R3 → R4 → R5
  4. Halve the equation:  hq2 : q ^ 2 = 2 * k ^ 2                                         have, R6
  5. `q` is even: the same three moves on `hq2`, substituting `q = 2 * m`:               R3 → R4 → R5
  6. Descend: apply `ih` at `m` with `p := k`; its side goals are
       `m < 2 * m` and `0 < m` (from `hq : 0 < 2 * m`), and `k ^ 2 = 2 * m ^ 2`:         R7, R8, R8, R6
-/
-- BEGIN SPEC
theorem sq_ne_two_mul_sq (p q : ℕ) (hq : 0 < q) : p ^ 2 ≠ 2 * q ^ 2 :=
-- END SPEC
  by
    induction q using Nat.strong_induction_on generalizing p with
    | _ q ih =>
      intro h
      obtain ⟨k, rfl⟩ : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ p ^ 2 from ⟨q ^ 2, h⟩)
      have hq2 : q ^ 2 = 2 * k ^ 2 := by linarith
      obtain ⟨m, rfl⟩ : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ q ^ 2 from ⟨k ^ 2, hq2⟩)
      exact ih m (by omega) k (by omega) (by linarith)

/- SKELETON · sqrt_two_irrational
  Uses the MILESTONE `sq_ne_two_mul_sq` (above) in step 6: prove that one first.
  1. Irrational → "no fraction of integers equals √2":                                   R9
  2. Introduce `a b : ℤ`, `hb0 : b ≠ 0`, `h : √2 = ↑a / ↑b`; the goal is `False`:        R10
  3. The real version of `hb0` (`field_simp` needs it):  hb : (b : ℝ) ≠ 0                have, R11
  4. Square and clear the denominator:
       h2 : (a : ℝ) ^ 2 = 2 * (b : ℝ) ^ 2
     proof: the fact `√2 ^ 2 = 2` (R12), rewrite it with `h` and `div_pow` (R13, R14),
     clear `↑b ^ 2` (R15), reorder (R6)
  5. Down to ℤ, then to ℕ:
       h3 : a ^ 2 = 2 * b ^ 2                                                             R11
       h4 : a.natAbs ^ 2 = 2 * b.natAbs ^ 2                                               R16 → R19 (with R17, R18)
  6. Close with the milestone at `a.natAbs`, `b.natAbs`; its `0 < q` from `hb0`:        R7, R20
-/
-- BEGIN SPEC
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
-- END SPEC
  by
    rw [irrational_iff_ne_rational]
    intro a b hb0 h
    have hb : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
    have h2 : (a : ℝ) ^ 2 = 2 * (b : ℝ) ^ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      rw [h, div_pow] at this
      field_simp at this
      linarith
    have h3 : a ^ 2 = 2 * b ^ 2 := by exact_mod_cast h2
    have h4 : a.natAbs ^ 2 = 2 * b.natAbs ^ 2 := by
      have := congrArg Int.natAbs h3
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    exact sq_ne_two_mul_sq _ _ (Int.natAbs_pos.mpr hb0) h4

end H030

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Part 1: if `p² = 2q²` then `p` is even, `p = 2k`, so `q² = 2k²`, so `q = 2m` is even and
    `k² = 2m²` with `0 < m < q`: a smaller solution, which strong induction on `q` rules out.
    Part 2: `√2 = a / b` gives `a² = 2b²` in ℝ, then in ℤ, then (absolute values) in ℕ: Part 1.
H2. Part 1: `induction q using Nat.strong_induction_on generalizing p with | _ q ih => ?_`, `intro h`,
    then evenness twice with `Nat.prime_two.dvd_of_dvd_pow` and `obtain ⟨k, rfl⟩`; `linarith` halves
    the equations, `omega` gives the bounds. Part 2: `rw [irrational_iff_ne_rational]`, `intro a b hb0 h`;
    from `Real.sq_sqrt` get `↑a ^ 2 = 2 * ↑b ^ 2` with `rw [h, div_pow] at this` and `field_simp at this`;
    `exact_mod_cast` to ℤ; `congrArg Int.natAbs` + `simpa [Int.natAbs_mul, Int.natAbs_pow]` to ℕ.
H3. Descent step: `obtain ⟨k, rfl⟩ : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ p ^ 2 from ⟨q ^ 2, h⟩)`,
    the same for `q` from `hq2 : q ^ 2 = 2 * k ^ 2`, then `exact ih m (by omega) k (by omega) (by linarith)`.
    Last line of Part 2: `exact sq_ne_two_mul_sq _ _ (Int.natAbs_pos.mpr hb0) h4`.
-/
