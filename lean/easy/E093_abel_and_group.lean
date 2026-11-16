/- E093 | abel and group | 2 min | abel, group, AddCommGroup, Group, nsmul, mathlib
GOAL
  Normalise expressions in an additive commutative group (`abel`) and in an arbitrary, possibly
  noncommutative, group (`group`). `ring` needs a ring (a multiplication), so it does not apply.

REFERENCE
  example {G : Type} [AddCommGroup G] (a b : G) : a + b - a = b := by abel
  example {G : Type} [AddCommGroup G] (a : G) : a + a = 2 • a := by abel  -- `n • a` = a + … + a
  example {G : Type} [Group G] (a b : G) : a * b * b⁻¹ = a := by group   -- `⁻¹` is typed `\inv`
  -- `group`/`abel` ignore hypotheses: rewrite with `h` yourself, or set up a `calc` first
BANNED: simp, simp_all, simpa, grind, mul_inv_rev, eq_inv_of_mul_eq_one_right, eq_inv_of_mul_eq_one_left, inv_eq_of_mul, inv_eq_of_mul_eq_one_right, inv_eq_of_mul_eq_one_left, eq_inv_iff_mul_eq_one, inv_eq_iff_mul_eq_one, mul_eq_one_iff_eq_inv, mul_eq_one_iff_inv_eq, exact?, try?
NOTE: `abel` handles numeral multiples `3 • a`; it gets stuck on `n • (a + b)` with a variable `n`.
-/
import Mathlib

namespace E093

-- BEGIN SPEC
theorem abel1 {G : Type} [AddCommGroup G] (a b c : G) : a + b - c - (b - c) = a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem abel2 {G : Type} [AddCommGroup G] (a b : G) : (a + b) + (a - b) = 2 • a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem abel3 {G : Type} [AddCommGroup G] (a b : G) : 3 • (a + b) - 3 • b = 3 • a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem group1 {G : Type} [Group G] (a b : G) : (a * b)⁻¹ * a * b = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem group2 {G : Type} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem group3 {G : Type} [Group G] (a b : G) (h : a * b = 1) : b = a⁻¹ :=
-- END SPEC
  sorry

end E093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first five are pure identities: one tactic each. `group3` depends on `h`.
H2. `abel` for the additive ones, `group` for the multiplicative ones. For `group3`, write `b`
    as `a⁻¹ * (a * b)` (a group identity), then use `h`.
H3. `calc b = a⁻¹ * (a * b) := by group
       _ = a⁻¹ := by rw [h]; group`.
-/
