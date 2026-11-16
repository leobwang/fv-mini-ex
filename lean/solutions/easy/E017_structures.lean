/- E017 | Structures | 2-3 min | structure, fields, projections
GOAL
  Define `origin` and `Point.swap` for a 2D point structure, and prove they behave.

REFERENCE
  structure Pair where
    a : Nat
    b : Nat
  example : Pair := { a := 1, b := 2 }       -- structure-instance notation
  example : Pair := ⟨1, 2⟩                   -- anonymous constructor (fields in order)
  example (p : Pair) : Pair := { p with a := 0 }   -- functional update
  example (p : Pair) : (Pair.mk p.a p.b) = p := rfl   -- eta: rebuilding p is definitionally p
  `p.a` projects; `Pair.foo p` can be written `p.foo` (dot notation on the type's namespace).
-/

-- BEGIN SPEC
structure Point where
  x : Nat
  y : Nat
-- END SPEC

-- BEGIN SPEC
def origin : Point :=
-- END SPEC
  { x := 0, y := 0 }

-- BEGIN SPEC
def Point.swap (p : Point) : Point :=
-- END SPEC
  ⟨p.y, p.x⟩

-- BEGIN SPEC
theorem origin_spec : origin.x = 0 ∧ origin.y = 0 :=
-- END SPEC
  ⟨rfl, rfl⟩

-- BEGIN SPEC
theorem swap_fields (p : Point) : p.swap.x = p.y ∧ p.swap.y = p.x :=
-- END SPEC
  ⟨rfl, rfl⟩

-- BEGIN SPEC
theorem swap_swap (p : Point) : p.swap.swap = p :=
-- END SPEC
  rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `swap_fields` says which field goes where.
H2. Build the result with `⟨_, _⟩` or `{ x := _, y := _ }`; all three theorems then hold by computation.
H3. `def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩`; proofs `⟨rfl, rfl⟩`, `⟨rfl, rfl⟩`, `rfl`.
-/
