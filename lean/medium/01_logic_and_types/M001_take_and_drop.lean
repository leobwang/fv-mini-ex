/- M001 | take and drop | 10-15 min | induction generalizing, List, cases
GOAL
  Prove four laws about your own `take` and `drop`. The induction hypothesis must work for
  every list, not just the one in the goal.

REFERENCE
  example (n : Nat) (xs : List Nat) : xs.length + n ≥ n := by
    induction n generalizing xs with     -- ih : ∀ xs, ... (xs is re-quantified)
    | zero => omega
    | succ k ih => have := ih xs; omega
  example (xs : List Nat) : xs = xs := by cases xs with | nil => rfl | cons y ys => rfl
  example (n m : Nat) : n + 1 + m = (n + m) + 1 := by omega   -- then `rw [this]` to expose `+ 1`
  `omega` understands `min a b` and `max a b`.
-/

example (n : Nat) (xs : List Nat) : xs.length + n ≥ n := by
  induction n with     -- ih : ∀ xs, ... (xs is re-quantified)
  | zero => omega
  | succ k ih => omega

example (xs : List Nat) : xs = xs := by cases xs with | nil => rfl | cons y ys => rfl

example (n m : Nat) : n + 1 + m = (n + m) + 1 := by omega   -- then `rw [this]` to expose `+ 1`

namespace M001

-- BEGIN SPEC
def take {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => x :: take n xs

def drop {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | n + 1, _ :: xs => drop n xs
-- END SPEC

-- BEGIN SPEC
theorem take_append_drop {α : Type} (n : Nat) (xs : List α) : take n xs ++ drop n xs = xs := by
-- END SPEC
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
  cases xs with
    | nil => rfl
    | cons y ys => simp [take, drop, ih]

-- BEGIN SPEC
theorem length_drop {α : Type} (n : Nat) (xs : List α) : (drop n xs).length = xs.length - n := by
-- END SPEC
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
  cases xs with
    | nil => simp [drop]
    | cons y ys => simp [drop, ih]

-- BEGIN SPEC
theorem length_take {α : Type} (n : Nat) (xs : List α) : (take n xs).length = min n xs.length := by
-- END SPEC
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => simp [take]
    | cons y ys => simp [take, ih]

-- BEGIN SPEC
theorem drop_drop {α : Type} (m n : Nat) (xs : List α) : drop m (drop n xs) = drop (n + m) xs := by
-- END SPEC
  induction n generalizing xs with
  | zero => simp [drop]
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by omega]
    cases xs with
      | nil => cases m <;> rfl
      | cons y ys => simp [drop, ih]

end M001

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both functions recurse on the number and the list at once: induct on `n`, then split `xs`.
H2. `induction n generalizing xs`, then in the `succ` case `cases xs`; finish with `simp [take, drop, ih]` (+ `omega`).
H3. For `drop_drop` you need `drop m [] = []` (by `cases m <;> rfl`) and `rw [show n + 1 + m = (n + m) + 1 by omega]`.
-/
