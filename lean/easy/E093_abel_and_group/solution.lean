/- E093 | abel and group | 2 min | abel, group, AddCommGroup, Group, nsmul, mathlib
GOAL
  Normalise expressions in an additive commutative group (`abel`) and in an arbitrary, possibly
  noncommutative, group (`group`). `ring` needs a ring (a multiplication), so it does not apply.
BANNED: simp, simp_all, simpa, grind, mul_inv_rev, eq_inv_of_mul_eq_one_right, eq_inv_of_mul_eq_one_left, inv_eq_of_mul, inv_eq_of_mul_eq_one_right, inv_eq_of_mul_eq_one_left, eq_inv_iff_mul_eq_one, inv_eq_iff_mul_eq_one, mul_eq_one_iff_eq_inv, mul_eq_one_iff_inv_eq, exact?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E093

/- SKELETON · abel1
  1. Only `+` and `-` in an `AddCommGroup`: one normalising tactic closes it:              R1
-/
-- BEGIN SPEC
theorem abel1 {G : Type} [AddCommGroup G] (a b c : G) : a + b - c - (b - c) = a :=
-- END SPEC
  by abel

/- SKELETON · abel2
  1. Numeral multiple `2 • a`: the same tactic, which treats `2` as a known coefficient:   R2
     (if it fails, look at what is left with R3)
-/
-- BEGIN SPEC
theorem abel2 {G : Type} [AddCommGroup G] (a b : G) : (a + b) + (a - b) = 2 • a :=
-- END SPEC
  by abel

/- SKELETON · abel3
  1. Numeral multiples of a sum, `3 • (a + b)`: expanded and collected in one step:        R2
-/
-- BEGIN SPEC
theorem abel3 {G : Type} [AddCommGroup G] (a b : G) : 3 • (a + b) - 3 • b = 3 • a :=
-- END SPEC
  by abel

/- SKELETON · group1
  1. Only `*`, `⁻¹`, `1` in a `Group`: one normalising tactic closes it,
     the inverse of the product included:                                                  R4, R5
-/
-- BEGIN SPEC
theorem group1 {G : Type} [Group G] (a b : G) : (a * b)⁻¹ * a * b = 1 :=
-- END SPEC
  by group

/- SKELETON · group2
  1. The inverse of a product, as an identity: one step:                                  R5
-/
-- BEGIN SPEC
theorem group2 {G : Type} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
-- END SPEC
  by group

/- SKELETON · group3
  `group` alone fails here: it ignores `h` (leftover `⊢ b = a ^ (-1)`).
  1. Split the goal `b = a⁻¹` into two `calc` steps through the middle term
     `a⁻¹ * (a * b)` (brackets as written, so that `a * b` is a subterm):                R6
  2. Step `b = a⁻¹ * (a * b)`: a pure group identity:                                     R4
  3. Step `_ = a⁻¹`: rewrite `a * b` to `1`, then the identity `a⁻¹ * 1 = a⁻¹`:            R7, R4
-/
-- BEGIN SPEC
theorem group3 {G : Type} [Group G] (a b : G) (h : a * b = 1) : b = a⁻¹ :=
-- END SPEC
  by
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ := by rw [h]; group

end E093

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first five are pure identities: one tactic each (`+`/`-`/`•` → R1, R2; `*`/`⁻¹` → R4, R5).
    `group3` depends on `h`, and neither `abel` nor `group` reads hypotheses.
H2. `abel` for the additive ones, `group` for the multiplicative ones. For `group3`, use a `calc`
    (R6) whose middle term contains `a * b` literally, rewrite there with `h` (R7), and let `group`
    close both steps (R4). The shape is W3 of the guide.
H3. The middle term is `a⁻¹ * (a * b)`: `b = a⁻¹ * (a * b)` is a group identity, and
    `rw [h]` turns it into `a⁻¹ * 1`.
-/
