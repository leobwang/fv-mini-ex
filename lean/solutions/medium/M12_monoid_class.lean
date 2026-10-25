/- M12 | A monoid class with laws | 10-15 min | class, instance, proof fields, type classes
GOAL
  A `class` can carry proofs. Give `Nat` a `MyMonoid` instance with `max` and `0`, and prove a
  generic theorem that holds in every `MyMonoid`.

REFERENCE
  class Pointed (α : Type) where
    pt : α
    pt_eq : pt = pt          -- a field can be a proof
  instance instPointedNat : Pointed Nat := { pt := 0, pt_eq := rfl }  -- or `where` syntax
  example : (Pointed.pt : Nat) = 0 := rfl
  example (a b c : Nat) : max (max a b) c = max a (max b c) := by omega   -- omega knows max/min
  Inside a generic proof `[MyMonoid α]`, use the laws by name: `MyMonoid.op_assoc a b c`.
-/

namespace M12

-- BEGIN SPEC
class MyMonoid (α : Type) where
  op : α → α → α
  unit : α
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)
  unit_op : ∀ a : α, op unit a = a
  op_unit : ∀ a : α, op a unit = a

def mconcat {α : Type} [MyMonoid α] : List α → α
  | [] => MyMonoid.unit
  | x :: xs => MyMonoid.op x (mconcat xs)
-- END SPEC

-- BEGIN SPEC
instance instMaxMonoid : MyMonoid Nat :=
-- END SPEC
  { op := max
    unit := 0
    op_assoc := by intro a b c; omega
    unit_op := by intro a; omega
    op_unit := by intro a; omega }

-- BEGIN SPEC
theorem op_is_max (a b : Nat) : MyMonoid.op a b = max a b :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem mconcat_example : mconcat [3, 1, 4, 1, 5] = 5 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem mconcat_append {α : Type} [MyMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = MyMonoid.op (mconcat xs) (mconcat ys) :=
-- END SPEC
  by
    induction xs with
    | nil => simp [mconcat, MyMonoid.unit_op]
    | cons x xs ih => simp [mconcat, ih, MyMonoid.op_assoc]

end M12

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The instance needs five fields: two data fields and three proofs about `max` and `0`.
H2. Each law is a goal about `max` that `omega` proves after `intro`. The generic theorem is induction on `xs`.
H3. `{ op := max, unit := 0, op_assoc := by intro a b c; omega, ... }`; `mconcat_append` cons case: `simp [mconcat, ih, MyMonoid.op_assoc]`.
-/
