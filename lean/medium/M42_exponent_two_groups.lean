/- M42 | Exponent-2 groups are abelian | 10 min | Group, inverses, calc, mathlib
GOAL
  In a group where every element squares to the identity, every element is its own inverse and
  multiplication commutes.

REFERENCE
  -- In `[Group G]`: `*`, `1`, `⁻¹` with the group axioms; `ring`/`simp` assume nothing commutes.
  #check inv_eq_of_mul_eq_one_right   -- a * b = 1 → a⁻¹ = b
  #check mul_inv_rev                  -- (a * b)⁻¹ = b⁻¹ * a⁻¹
  #check mul_assoc                    -- a * b * c = a * (b * c)
  example {G : Type} [Group G] (a : G) : a * a⁻¹ = 1 := mul_inv_cancel a
  `group` is a Mathlib tactic that normalises words in a group (useful to check steps).
BANNED: mul_comm, mul_comm_of_mul_self_eq_one, CommGroup
-/
import Mathlib

namespace M42

-- BEGIN SPEC
theorem inv_eq_self {G : Type} [Group G] (h : ∀ g : G, g * g = 1) (a : G) : a⁻¹ = a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem comm_of_sq_one {G : Type} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) :
    a * b = b * a :=
-- END SPEC
  sorry

end M42

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `g * g = 1` says `g` is the inverse of `g`.
H2. Apply that to `a * b`: `a * b = (a * b)⁻¹`, and inverses reverse products.
H3. `calc a * b = (a * b)⁻¹ := (inv_eq_self h (a * b)).symm; _ = b⁻¹ * a⁻¹ := mul_inv_rev a b; _ = b * a := by rw [inv_eq_self h, inv_eq_self h]`.
-/
