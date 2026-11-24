/- E053 | Structures with extends | 2-3 min | structure, extends, toParent, functional update
GOAL
  Implement `Point3.lift`, which adds a `z` coordinate to a 2D `Point`, and prove it keeps the
  original point and sets `z`.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E053

-- BEGIN SPEC
structure Point where
  x : Int
  y : Int

structure Point3 extends Point where
  z : Int

def Point3.normSq (p : Point3) : Int := p.x * p.x + p.y * p.y + p.z * p.z
-- END SPEC

/- SKELETON · Point3.lift (definition body)
  1. The parent part must be `p` (lift_toPoint), the new field `z` (lift_z).
     Copy `p`'s fields and add `z` with a functional update:                         R1
     (or the anonymous constructor, parent part first:                               R2)
-/
-- BEGIN SPEC
def Point3.lift (p : Point) (z : Int) : Point3 :=
-- END SPEC
  sorry

/- SKELETON · lift_toPoint
  1. Unfold `Point3.lift`: the left side is a constructor value's `.toPoint`:         R3
  2. Reduce that projection; both sides are then `p`:                                R4
     Steps 1–2 in one go:                                                            R6
-/
-- BEGIN SPEC
theorem lift_toPoint (p : Point) (z : Int) : (Point3.lift p z).toPoint = p :=
-- END SPEC
  sorry

/- SKELETON · lift_z
  1. As in lift_toPoint, with the new field `.z` instead of the parent part:         R3 → R4
     or in one go:                                                                   R6
-/
-- BEGIN SPEC
theorem lift_z (p : Point) (z : Int) : (Point3.lift p z).z = z :=
-- END SPEC
  sorry

/- SKELETON · normSq_lift_zero
  1. Unfold BOTH `Point3.normSq` and `Point3.lift`:                                  R3
  2. Reduce the inherited fields `.x`, `.y` and the new field `.z`:                  R5, R4
     The goal is now `p.x * p.x + p.y * p.y + 0 * 0 = p.x * p.x + p.y * p.y`.
  3. Clean up `0 * 0`, then `… + 0`:                                                 R7, R8
     Steps 1–3 in one go: `simp` with both names                                     R9
-/
-- BEGIN SPEC
theorem normSq_lift_zero (p : Point) :
    (Point3.lift p 0).normSq = p.x * p.x + p.y * p.y :=
-- END SPEC
  sorry

end E053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `lift_toPoint` and `lift_z` say exactly what the parent part and the new field must be. A `Point3`
    is a `Point` plus `z`, and its constructor takes the parent part as ONE argument.
H2. Build the `Point3` from `p` by functional update (R1) or the anonymous constructor (R2). Then
    `lift_toPoint` and `lift_z` hold by unfolding and reducing projections, i.e. by `rfl` (R6). For
    `normSq_lift_zero`, unfold both definitions, reduce the fields, and clean up `0 * 0` (R3–R5, R7, R8).
H3. `{ p with z := z }`; `rfl`; `rfl`; `simp [Point3.normSq, Point3.lift]` (R9).
-/
