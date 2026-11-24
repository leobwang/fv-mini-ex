/- M008 | Length-indexed vectors | 10-15 min | indexed inductive, dependent pattern matching
GOAL
  `Vec α n` is a list whose length `n` is part of its type. Implement `head` (total on
  non-empty vectors), `map` and `append`, and relate them to lists.

REFERENCE
  -- Pattern matching refines the index: matching `.cons x xs` on `Vec α (n + 1)` is complete.
  def Vec.tail' {α : Type} {n : Nat} : M008.Vec α (n + 1) → M008.Vec α n | .cons _ xs => xs
  def Vec.len {α : Type} {n : Nat} (_ : M008.Vec α n) : Nat := n   -- the index is available
  example (n m : Nat) : m + (n + 1) = (m + n) + 1 := rfl   -- holds by computation (recursion on 2nd arg)
NOTE: `append` returns `Vec α (m + n)` (not `n + m`) so that the `cons` case type-checks by `rfl`.
-/

namespace M008

-- BEGIN SPEC
inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (x : α) (xs : Vec α n) : Vec α (n + 1)

def Vec.toList {α : Type} {n : Nat} : Vec α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
-- END SPEC

-- BEGIN SPEC
def Vec.head {α : Type} {n : Nat} (v : Vec α (n + 1)) : α :=
-- END SPEC
  match v with
  | .cons x _ => x

-- BEGIN SPEC
def Vec.map {α β : Type} {n : Nat} (f : α → β) (v : Vec α n) : Vec β n :=
-- END SPEC
  match v with
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

-- BEGIN SPEC
def Vec.append {α : Type} {n m : Nat} (v : Vec α n) (w : Vec α m) : Vec α (m + n) :=
-- END SPEC
  match v with
  | .nil => w
  | .cons x xs => .cons x (xs.append w)

-- BEGIN SPEC
theorem head_cons {α : Type} {n : Nat} (x : α) (v : Vec α n) : (Vec.cons x v).head = x :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem toList_length {α : Type} {n : Nat} (v : Vec α n) : v.toList.length = n :=
-- END SPEC
  by
    induction v with
    | nil => rfl
    | cons x xs ih => simp [Vec.toList, ih]

-- BEGIN SPEC
theorem toList_map {α β : Type} {n : Nat} (f : α → β) (v : Vec α n) :
    (v.map f).toList = v.toList.map f :=
-- END SPEC
  by
    induction v with
    | nil => rfl
    | cons x xs ih => simp [Vec.map, Vec.toList, ih]

-- BEGIN SPEC
theorem toList_append {α : Type} {n m : Nat} (v : Vec α n) (w : Vec α m) :
    (v.append w).toList = v.toList ++ w.toList :=
-- END SPEC
  by
    induction v with
    | nil => rfl
    | cons x xs ih => simp [Vec.append, Vec.toList, ih]

end M008

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `head` only needs the `cons` case: Lean knows `nil` cannot have type `Vec α (n + 1)`.
H2. `map` and `append` recurse on `v`; the theorems follow by `induction v`.
H3. `match v with | .cons x xs => .cons x (xs.append w) | .nil => w`; proofs: `induction v with | nil => rfl | cons x xs ih => simp [Vec.append, Vec.toList, ih]`.
-/
