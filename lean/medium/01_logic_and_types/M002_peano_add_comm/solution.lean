/- M002 | Peano addition is commutative | 10-15 min | inductive, helper lemmas, induction
GOAL
  On your own unary naturals, prove that addition is associative and commutative.
  You will need helper lemmas; the induction hypothesis alone is not enough.

REFERENCE
  -- `add n m` recurses on m:  add n zero = n,  add n (succ m) = succ (add n m)
  example (n : M002.N) : M002.add n .zero = n := rfl          -- true by definition
  example (n m : M002.N) : M002.add n (.succ m) = .succ (M002.add n m) := rfl
  -- `add .zero n = n` is NOT definitional: it needs induction on n.
  example (a b : M002.N) (h : a = b) : M002.N.succ a = .succ b := by rw [h]
  Typical helpers: `zero_add`, `succ_add : add (succ a) b = succ (add a b)`.
-/

namespace M002

-- BEGIN SPEC
inductive N where
  | zero : N
  | succ (n : N) : N

def add : N → N → N
  | n, .zero => n
  | n, .succ m => .succ (add n m)
-- END SPEC

theorem zero_add (n : N) : add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem succ_add (a b : N) : add (.succ a) b = .succ (add a b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp [add, ih]

-- BEGIN SPEC
theorem add_assoc (a b c : N) : add (add a b) c = add a (add b c) :=
-- END SPEC
  by
    induction c with
    | zero => rfl
    | succ c ih => simp [add, ih]

-- BEGIN SPEC
theorem add_comm (a b : N) : add a b = add b a :=
-- END SPEC
  by
    induction b with
    | zero => simp [add, zero_add]
    | succ b ih => simp [add, succ_add, ih]

end M002

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Associativity goes through directly by induction on `c`. Commutativity gets stuck at `add zero a = a`.
H2. Induct on the second argument (the one `add` recurses on); prove `zero_add` and `succ_add` first.
H3. `theorem succ_add (a b : N) : add (.succ a) b = .succ (add a b)` by induction on `b`; then `add_comm` by induction on `b` using `zero_add`, `succ_add`.
-/
