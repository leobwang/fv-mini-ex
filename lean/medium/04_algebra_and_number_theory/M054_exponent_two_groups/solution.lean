/- M054 | Exponent-2 groups are abelian | 10 min | Group, inverses, calc, mathlib
GOAL
  In a group where every element squares to the identity, every element is its own inverse and
  multiplication commutes.
BANNED: mul_comm, mul_comm_of_mul_self_eq_one, CommGroup

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M054

/- SKELETON · inv_eq_self
  1. Goal `a⁻¹ = a`: reduce it to "`a` is a right inverse of `a`",
     goal `a * a = 1`:                                                        R1
  2. That is the hypothesis `h` at the element `a`:                           R2
  (Both steps fit in one term: the lemma of R1 applied to a proof of its premise.)
-/
-- BEGIN SPEC
theorem inv_eq_self {G : Type} [Group G] (h : ∀ g : G, g * g = 1) (a : G) : a⁻¹ = a :=
-- END SPEC
  inv_eq_of_mul_eq_one_right (h a)

/- SKELETON · comm_of_sq_one
  1. A chain `a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a`:                          R3
  2. Step `a * b = (a * b)⁻¹`: Part 1's theorem `inv_eq_self`, applied to
     `h` and to the element `a * b`, then flipped:                            R2 → R4
  3. Step `(a * b)⁻¹ = b⁻¹ * a⁻¹`: inverses reverse products:                 R5
  4. Step `b⁻¹ * a⁻¹ = b * a`: remove both inverses with Part 1's theorem,
     one `rw` per inverse:                                                    R6, R6
-/
-- BEGIN SPEC
theorem comm_of_sq_one {G : Type} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) :
    a * b = b * a :=
-- END SPEC
  calc a * b = (a * b)⁻¹ := (inv_eq_self h (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_self h, inv_eq_self h]

end M054

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `g * g = 1` says `g` is a right inverse of `g`, and in a group a right inverse is the inverse (R1).
H2. For commutativity apply Part 1 to `a * b`: `a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹`, and Part 1 again turns
    `b⁻¹ * a⁻¹` into `b * a`. Write it as a `calc` chain (R3).
H3. Part 1: `inv_eq_of_mul_eq_one_right` needs `a * a = 1`, which is `h a`. Part 2: the first calc
    step is `(inv_eq_self h (a * b)).symm`, the second `mul_inv_rev a b`, and the last rewrites with
    `inv_eq_self h` twice (R6).
-/
