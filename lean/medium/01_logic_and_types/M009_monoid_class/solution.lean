/- M009 | A monoid class with laws | 10-15 min | class, instance, proof fields, type classes
GOAL
  A `class` can carry proofs. Give `Nat` a `MyMonoid` instance with `max` and `0`, and prove a
  generic theorem that holds in every `MyMonoid`.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M009

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

/- SKELETON · instMaxMonoid
  1. After `:=`, a structure instance in braces: the data fields
     `op := max`, `unit := 0`, then one field per law:                        R4
       (R1 shows the three obligations, with `max` and `0` substituted)
  2. Each law field `:= by …`: name the `∀` variables, then arithmetic:     R2 → R3
-/
-- BEGIN SPEC
instance instMaxMonoid : MyMonoid Nat :=
-- END SPEC
  { op := max
    unit := 0
    op_assoc := by intro a b c; omega
    unit_op := by intro a; omega
    op_unit := by intro a; omega }

/- SKELETON · op_is_max
  1. On `Nat`, `MyMonoid.op` is your instance's `op := max`: both sides
     are the same term once the projection unfolds:                          R5
-/
-- BEGIN SPEC
theorem op_is_max (a b : Nat) : MyMonoid.op a b = max a b :=
-- END SPEC
  rfl

/- SKELETON · mconcat_example
  1. A closed term: evaluate `mconcat` through the instance:                  R6
-/
-- BEGIN SPEC
theorem mconcat_example : mconcat [3, 1, 4, 1, 5] = 5 :=
-- END SPEC
  rfl

/- SKELETON · mconcat_append
  1. Induction on `xs`; `ys` stays fixed:                                     R7
  2. Case `nil`: `[] ++ ys` → `ys`, unfold `mconcat []`, then the law
     `MyMonoid.unit_op` on the right side:                                    R8 → R10 → R12
  3. Case `cons`: move `x` out of the append, unfold `mconcat` on both
     sides, rewrite with `ih`, then the law `MyMonoid.op_assoc`:              R9 → R10 → R11 → R12
-/
-- BEGIN SPEC
theorem mconcat_append {α : Type} [MyMonoid α] (xs ys : List α) :
    mconcat (xs ++ ys) = MyMonoid.op (mconcat xs) (mconcat ys) :=
-- END SPEC
  by
    induction xs with
    | nil => simp [mconcat, MyMonoid.unit_op]
    | cons x xs ih => simp [mconcat, ih, MyMonoid.op_assoc]

end M009

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The instance needs five fields: two data fields (`op`, `unit`) and three proofs about `max` and `0`.
    `op_is_max` and `mconcat_example` hold by computation. In `mconcat_append`, `op` is unknown: only the
    three laws are available, and the proof is an induction on `xs`.
H2. Each law field: `by intro …; omega` (R2, R3). `op_is_max` and `mconcat_example`: `rfl` (R5, R6).
    `mconcat_append`: `induction xs with | nil => … | cons x xs ih => …`; in each case simplify the append,
    unfold `mconcat`, use `ih` (cons only), and finish with one law (R7–R12).
H3. `{ op := max, unit := 0, op_assoc := by intro a b c; omega, … }`; `mconcat_append`:
    nil: `simp [mconcat, MyMonoid.unit_op]`; cons: `simp [mconcat, ih, MyMonoid.op_assoc]`.
-/
