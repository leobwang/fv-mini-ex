/- E053 | Structures with extends | 2-3 min | structure, extends, toParent, functional update
GOAL
  Implement `Point3.lift`, which adds a `z` coordinate to a 2D `Point`, and prove it keeps the
  original point and sets `z`.

REFERENCE
  structure A where
    a : Nat
  structure B extends A where
    b : Nat                            -- B has fields `a` and `b`, plus `B.toA : B → A`
  example : B := { a := 1, b := 2 }    -- flat field syntax works through `extends`
  example (q : B) : Nat := q.a + q.b   -- parent fields project directly
  example (q : B) : A := q.toA         -- the parent part as an `A`
  example (x : A) : B := { x with b := 0 }   -- copy x's fields (x may be the parent type), add b
  example (x : A) : B := ⟨x, 0⟩         -- anonymous constructor: parent first, then new fields
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

-- BEGIN SPEC
def Point3.lift (p : Point) (z : Int) : Point3 :=
-- END SPEC
  { p with z := z }

-- BEGIN SPEC
theorem lift_toPoint (p : Point) (z : Int) : (Point3.lift p z).toPoint = p :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem lift_z (p : Point) (z : Int) : (Point3.lift p z).z = z :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem normSq_lift_zero (p : Point) :
    (Point3.lift p 0).normSq = p.x * p.x + p.y * p.y :=
-- END SPEC
  by simp [Point3.normSq, Point3.lift]

end E053

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `lift_toPoint` and `lift_z` say exactly what the parent part and the new field must be.
H2. Build the `Point3` from `p` by functional update or the anonymous constructor; the first two
    theorems then hold by `rfl`.
H3. `{ p with z := z }`. For `normSq_lift_zero`, unfold both definitions: `simp [Point3.normSq, Point3.lift]`.
-/
