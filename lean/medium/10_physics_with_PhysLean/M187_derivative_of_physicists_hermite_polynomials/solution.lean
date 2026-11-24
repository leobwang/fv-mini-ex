/- M187 | Derivative of physicists' Hermite polynomials | 15 min | Polynomial.derivative, induction, nsmul, ring, physlib
GOAL
  The physicists' Hermite polynomials are `H₀ = 1`, `H_{n+1} = 2X·Hₙ − Hₙ'` (`'` = formal derivative).
  Prove the ladder relation `H'_{n+1} = 2(n+1)·Hₙ` for every `n` (the QHO lowering, i.e. annihilation, operator acts by it).

REFERENCE
  `physHermite n : ℤ[X]` is `Hₙ` (a polynomial with integer coefficients); `derivative p` is `p'`.
  #check physHermite_succ  -- physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)
  #check physHermite_one   -- physHermite 1 = 2 * X
  #check derivative_mul    -- derivative (f * g) = derivative f * g + f * derivative g
  #check derivative_sub    -- derivative (f - g) = derivative f - derivative g
  #check derivative_X      -- derivative X = 1
  #check nsmul_eq_mul      -- n • a = ↑n * a   (`k • p` with `k : ℕ` is `p + ... + p`, k times)
  `induction n with | zero => ... | succ n ih => ...`; `rw [physHermite_succ n]` unfolds only `H_{n+1}`.
  `simp` knows the derivative of numerals and casts is `0`; `push_cast; ring` finishes polynomial identities.
BANNED: derivative_physHermite_succ, derivative_physHermite, physHermite_succ', deriv_physHermite, physHermite_succ_coe', physHermite_succ_apply'
-/
import Physlib.Mathematics.SpecialFunctions.PhysHermite

open Polynomial

namespace M187

-- BEGIN SPEC
theorem hermite_derivative (n : ℕ) :
    derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n :=
-- END SPEC
  by
    induction n with
    | zero => simp [physHermite_one]
    | succ n ih =>
      rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih, physHermite_succ n]
      simp
      ring

end M187

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct on `n`. In the step, unfold the recursion once on the left (`H_{n+2}`), differentiate, and use
    the induction hypothesis for `H'_{n+1}`.
H2. After `rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih]` the goal still mentions
    `H_{n+1}` and `H_{n+1}'` in other places: unfold `H_{n+1}` once more with `physHermite_succ n`, so
    everything is in terms of `Hₙ` and `Hₙ'`.
H3. Step: `rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih, physHermite_succ n]`; what is left
    is a polynomial identity once the derivatives of `2 • X`, numerals and casts are simplified away.
-/
