/- E055 | Coercions | 2-3 min | Coe, @[coe], ↑, coercion unfolding
GOAL
  `Pos` is a natural number packed with a proof that it is positive. Its coercion to `Nat` (given) lets a
  `Pos` stand wherever a `Nat` is expected. Write the function behind it, define addition, and prove
  the coercion respects both.

REFERENCE
  structure Even2 where (val : Nat) (even : val % 2 = 0)   -- data + proof, like `Pos` below
  instance : Coe Even2 Nat := ⟨Even2.val⟩     -- `Coe α β` has one field, `coe : α → β`
  example (e : Even2) : Nat := e + 1          -- Lean inserts the coercion: `↑e + 1`
  example (e : Even2) : Nat := ↑e             -- `↑x` asks for a coercion explicitly
  example (e : Even2) : (e : Nat) = e.val := rfl   -- `(e : Nat)` is a type ascription that coerces
  -- `↑a` elaborates to the function inside the instance (`Pos.toNat a`); `@[coe]` only makes it print as `↑a`
  #check Nat.add_pos_left   -- (h : 0 < m) (n : Nat) : 0 < m + n
  #check Nat.pos_iff_ne_zero   -- 0 < n ↔ n ≠ 0
-/

namespace E055

-- BEGIN SPEC
structure Pos where
  val : Nat
  pos : 0 < val

def one : Pos := ⟨1, Nat.one_pos⟩
-- END SPEC

-- BEGIN SPEC
@[coe] def Pos.toNat (p : Pos) : Nat :=
-- END SPEC
  p.val

-- BEGIN SPEC
instance instCoePosNat : Coe Pos Nat := ⟨Pos.toNat⟩
-- END SPEC

-- BEGIN SPEC
def Pos.add (a b : Pos) : Pos :=
-- END SPEC
  ⟨a.val + b.val, Nat.add_pos_left a.pos b.val⟩

-- BEGIN SPEC
theorem coe_mk (n : Nat) (h : 0 < n) : ((⟨n, h⟩ : Pos) : Nat) = n :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem coe_one : ((one : Pos) : Nat) = 1 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem coe_add (a b : Pos) : ((a.add b : Pos) : Nat) = (a : Nat) + (b : Nat) :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem coe_ne_zero (a : Pos) : (a : Nat) ≠ 0 :=
-- END SPEC
  Nat.pos_iff_ne_zero.mp a.pos

end E055

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `coe_mk` tells you what `Pos.toNat` must return. `Pos.add` must build a value *and* a proof that it is positive.
H2. With `toNat p := p.val`, `coe_mk`, `coe_one` and `coe_add` hold by definition (`rfl`). For `coe_ne_zero`, the
    field `a.pos : 0 < a.val` is the fact you need, in a different shape.
H3. `Pos.add a b := ⟨a.val + b.val, Nat.add_pos_left a.pos b.val⟩`; `coe_ne_zero` is `Nat.pos_iff_ne_zero.mp a.pos`.
-/
