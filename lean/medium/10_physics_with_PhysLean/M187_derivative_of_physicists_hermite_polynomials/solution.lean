/- M187 | Derivative of physicists' Hermite polynomials | 15 min | Polynomial.derivative, induction, nsmul, ring, physlib
GOAL
  The physicists' Hermite polynomials are `H₀ = 1`, `H_{n+1} = 2X·Hₙ − Hₙ'` (`'` = formal derivative).
  Prove the ladder relation `H'_{n+1} = 2(n+1)·Hₙ` for every `n` (the QHO lowering, i.e. annihilation, operator acts by it).

BANNED: derivative_physHermite_succ, derivative_physHermite, physHermite_succ', deriv_physHermite, physHermite_succ_coe', physHermite_succ_apply'

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Mathematics.SpecialFunctions.PhysHermite

open Polynomial

namespace M187

/- SKELETON · hermite_derivative
  1. Induct on `n`, naming the step's variable and hypothesis `n`, `ih`:         R1
  2. zero (`H₁' = 2·H₀`): one `simp` call (`physHermite_one` is a simp lemma;
     naming it is optional); it also applies R3, R5, R7, R8 and
     `0 + 1 = 1`, `1 • p = p` by itself:                                         R2
  3. succ, in this order:
       a. unfold the LEFT side once, `H_{n+2}` (argument `n + 1`):               R4
       b. differentiate the difference, then the product:                       R6, R5
       c. use `ih` (it rewrites `H'_{n+1}` AND the copy inside `H''_{n+1}`):      rw [ih]   (W1)
       d. only now unfold the remaining `H_{n+1}` (argument `n`):                R4
       e. evaluate the derivatives of `2 • X`, numerals and casts, and turn
          every ℕ-scalar `k • p` into `↑k * p`: one `simp`                       R11, R12, R13, R5, R10, R7, R8, R9
       f. close the identity in `ℤ[X]`:                                          R14
-/
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
H1. Induct on `n`. The zero case is a computation once `physHermite_one` is available. In the step,
    unfold the recursion once on the left (`H_{n+2}`), differentiate, and use `ih` for `H'_{n+1}`.
H2. Step: `physHermite_succ (n + 1)`, then `derivative_sub`, `derivative_mul`, then `ih`, and only then
    `physHermite_succ n`, so that everything is in `Hₙ` and `Hₙ'` (unfolding `H_{n+1}` before `ih` destroys the
    left side of `ih`). What remains are derivatives of `2 • X`, numerals and casts, which `simp` removes.
H3. Step: `rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih, physHermite_succ n]`; after `simp`
    the goal is an identity of commutative rings in `ℤ[X]` (`ring`). Zero case: `simp [physHermite_one]`.
-/
