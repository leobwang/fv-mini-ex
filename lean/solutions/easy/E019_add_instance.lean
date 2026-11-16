/- E019 | Add instance | 3 min | instance, Add, type classes, ext
GOAL
  Give 2D integer vectors an `Add` instance so `p + q` works, then prove `+` is commutative.

REFERENCE
  structure P2 where
    a : Nat
    b : Nat
  instance instMulP2 : Mul P2 where mul p q := ⟨p.a * q.a, p.b * q.b⟩   -- now `p * q` works
  example (p q : P2) : (p * q).a = p.a * q.a := rfl
  #check Int.add_comm   -- (a b : Int) : a + b = b + a
  `@[ext]` on a structure generates `V2.ext : p.x = q.x → p.y = q.y → p = q`; use `apply V2.ext`.
-/

-- BEGIN SPEC
@[ext] structure V2 where
  x : Int
  y : Int
-- END SPEC

-- BEGIN SPEC
instance instAddV2 : Add V2 :=
-- END SPEC
  ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩

-- BEGIN SPEC
theorem add_fields (p q : V2) : (p + q).x = p.x + q.x ∧ (p + q).y = p.y + q.y :=
-- END SPEC
  ⟨rfl, rfl⟩

-- BEGIN SPEC
theorem add_comm_v2 (p q : V2) : p + q = q + p :=
-- END SPEC
  by
    apply V2.ext
    · exact Int.add_comm p.x q.x
    · exact Int.add_comm p.y q.y

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `add_fields` says the sum is computed coordinate-wise.
H2. `instance instAddV2 : Add V2 := ⟨fun p q => ...⟩`. For commutativity compare the fields.
H3. `apply V2.ext` then `exact Int.add_comm p.x q.x` and `exact Int.add_comm p.y q.y`.
-/
