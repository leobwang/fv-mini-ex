/- M127 | Z-rotations and the 2π sign | 10-15 min | Complex.exp, exp_add, push_cast, unitary group, mathlib
GOAL
  The rotation `Rz θ = diag(e^{-iθ/2}, e^{iθ/2})` composes additively (`Rz a · Rz b = Rz (a + b)`),
  a full turn gives the spinor sign `Rz (2π) = -1`, and every `Rz θ` is unitary.

REFERENCE
  #check Matrix.mul_fin_two   -- !![a, b; c, d] * !![a', b'; c', d'] = !![a*a' + b*c', …]
  #check Matrix.one_fin_two   -- (1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]
  example (a b : ℂ) : Complex.exp a * Complex.exp b = Complex.exp (a + b) := (Complex.exp_add a b).symm
  #check Complex.exp_pi_mul_I -- cexp (↑π * I) = -1
  #check Complex.exp_neg      -- cexp (-x) = (cexp x)⁻¹
  #check Complex.exp_conj     -- cexp (conj x) = conj (cexp x)
  example (θ : ℝ) : (starRingEnd ℂ) (Complex.exp (θ * I)) = Complex.exp (-(θ * I)) := by
    rw [← Complex.exp_conj]; simp   -- `starRingEnd ℂ` is complex conjugation
  -- `push_cast` rewrites `((a + b : ℝ) : ℂ)` to `↑a + ↑b`; `ring_nf` then normalises exponents on both sides.
  #check Matrix.mem_unitaryGroup_iff  -- A ∈ unitaryGroup n α ↔ A * star A = 1
  #check Matrix.star_eq_conjTranspose -- star M = Mᴴ   (conjugate transpose)
NOTE: `cexp` is notation for `Complex.exp`; `(θ / 2 : ℂ)` means the real `θ` cast to ℂ, then halved.
-/
import Mathlib

open Matrix Complex

namespace M127

-- BEGIN SPEC
noncomputable def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(θ / 2 : ℂ) * I), 0; 0, Complex.exp ((θ / 2 : ℂ) * I)]
-- END SPEC

-- BEGIN SPEC
theorem Rz_add (a b : ℝ) : Rz a * Rz b = Rz (a + b) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Rz_two_pi : Rz (2 * Real.pi) = -1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Rz_unitary (θ : ℝ) : Rz θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
-- END SPEC
  sorry

end M127

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Diagonal matrices multiply entrywise, so every goal reduces to identities between exponentials.
    Combine products of exponentials into one exponential, then compare exponents with `ring`.
H2. `Rz_add`: multiply the diagonals, merge each product into one exponential with `← Complex.exp_add`,
    then make the exponents agree (the real sum `↑(a + b)` must be split into `↑a + ↑b` first).
    `Rz_two_pi`: prove the two diagonal entries are `-1` separately (rewrite the exponent to `π * I`
    or `-(π * I)` with `show … by ring`), then compare with `Matrix.one_fin_two`.
    `Rz_unitary`: `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` and go entry by entry.
H3. `Rz_two_pi`: `have h2 : Complex.exp ((2 * ↑Real.pi / 2) * I) = -1 := by rw [show (2 * (Real.pi : ℂ) / 2) * I = Real.pi * I by ring, Complex.exp_pi_mul_I]`.
    `Rz_unitary`: the key fact is that `conj` goes inside `cexp` via `← Complex.exp_conj`; then `map_ofNat`
    turns the stray `conj 2` into `2`, products merge with `← Complex.exp_add`, and the exponents cancel.
-/
