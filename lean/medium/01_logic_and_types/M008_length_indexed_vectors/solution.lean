/- M008 | Length-indexed vectors | 10-15 min | indexed inductive, dependent pattern matching
GOAL
  `Vec α n` is a list whose length `n` is part of its type. Implement `head` (total on
  non-empty vectors), `map` and `append`, and relate them to lists.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · Vec.head
  1. The body is a `match v with` that has ONE branch, for `.cons`: a `Vec α (n + 1)`
     cannot be `nil` (index 0), so no `nil` branch is needed (or allowed):    R1
  2. Return the head field of that branch.
-/
-- BEGIN SPEC
def Vec.head {α : Type} {n : Nat} (v : Vec α (n + 1)) : α :=
-- END SPEC
  match v with
  | .cons x _ => x

/- SKELETON · Vec.map
  1. `match v with`, one branch per constructor; the result index is refined
     to `0` and `n✝ + 1`:                                                     R2
  2. `nil` branch: build the empty vector:                                    R3
  3. `cons x xs` branch: a `.cons` of `f x` and the recursive call on `xs`:   R3, R4
-/
-- BEGIN SPEC
def Vec.map {α β : Type} {n : Nat} (f : α → β) (v : Vec α n) : Vec β n :=
-- END SPEC
  match v with
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

/- SKELETON · Vec.append
  1. Recurse on `v` (not `w`): `match v with`, two branches:                 R2
  2. `nil` branch must be a `Vec α (m + 0)`; `w` is one by computation:      R5
  3. `cons x xs` branch must be a `Vec α (m + (n✝ + 1))`: a `.cons` of `x`
     and the recursive call on `xs`, of type `Vec α (m + n✝ + 1)`:            R3, R4, R5
-/
-- BEGIN SPEC
def Vec.append {α : Type} {n m : Nat} (v : Vec α n) (w : Vec α m) : Vec α (m + n) :=
-- END SPEC
  match v with
  | .nil => w
  | .cons x xs => .cons x (xs.append w)

/- SKELETON · head_cons
  1. `head` applied to a `cons` reduces by its only branch: close by computation.   R6
-/
-- BEGIN SPEC
theorem head_cons {α : Type} {n : Nat} (x : α) (v : Vec α n) : (Vec.cons x v).head = x :=
-- END SPEC
  rfl

/- SKELETON · toList_length
  1. Induction on `v`, naming the `cons` fields and the IH:                 R7
  2. `nil`: true by computation (`[].length` is `0`):                       R6
  3. `cons x xs ih`: unfold `Vec.toList`, apply `List.length_cons`,
     rewrite with `ih` (one `simp` call does all three):                    R8 → R9 → R12
-/
-- BEGIN SPEC
theorem toList_length {α : Type} {n : Nat} (v : Vec α n) : v.toList.length = n :=
-- END SPEC
  by
    induction v with
    | nil => rfl
    | cons x xs ih => simp [Vec.toList, ih]

/- SKELETON · toList_map
  1. Induction on `v`:                                                      R7
  2. `nil`: by computation:                                                 R6
  3. `cons x xs ih`: unfold `Vec.map` and `Vec.toList`, apply
     `List.map_cons`, rewrite with `ih` (one `simp` call):                  R8 → R10 → R12
-/
-- BEGIN SPEC
theorem toList_map {α β : Type} {n : Nat} (f : α → β) (v : Vec α n) :
    (v.map f).toList = v.toList.map f :=
-- END SPEC
  by
    induction v with
    | nil => rfl
    | cons x xs ih => simp [Vec.map, Vec.toList, ih]

/- SKELETON · toList_append
  1. Induction on `v` only; `w` stays fixed:                                R7
  2. `nil`: by computation (`[] ++ l` is `l`):                              R6
  3. `cons x xs ih`: unfold `Vec.append` and `Vec.toList`, apply
     `List.cons_append`, rewrite with `ih` (one `simp` call):               R8 → R11 → R12
-/
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
H1. Every definition is a `match v with` whose branches see the index refined (R1, R2): `head` needs
    only the `cons` branch, and `append`'s type `Vec α (m + n)` is chosen so its branches fit by
    computation (`m + (n + 1)` is `(m + n) + 1`, R5).
H2. `map` and `append` recurse structurally on `v` (the call goes on the field `xs`). `head_cons` is
    `rfl`. Each list theorem is `induction v`: `rfl` for `nil`, and for `cons` unfold the
    definitions and use the IH with one `simp` call.
H3. `append`: `match v with | .nil => w | .cons x xs => .cons x (xs.append w)`. Proofs:
    `induction v with | nil => rfl | cons x xs ih => simp [Vec.append, Vec.toList, ih]`
    (use `Vec.map` instead of `Vec.append` for `toList_map`, and only `Vec.toList` for `toList_length`).
-/
