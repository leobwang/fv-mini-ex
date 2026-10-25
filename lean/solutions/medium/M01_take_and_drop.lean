/- M01 | take and drop | 10-15 min | induction generalizing, List, cases
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

namespace M01

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
theorem take_append_drop {α : Type} (n : Nat) (xs : List α) : take n xs ++ drop n xs = xs :=
-- END SPEC
  by
    induction n generalizing xs with
    | zero => simp [take, drop]
    | succ n ih =>
      cases xs with
      | nil => simp [take, drop]
      | cons x xs => simp [take, drop, ih]

-- BEGIN SPEC
theorem length_drop {α : Type} (n : Nat) (xs : List α) : (drop n xs).length = xs.length - n :=
-- END SPEC
  by
    induction n generalizing xs with
    | zero => simp [drop]
    | succ n ih =>
      cases xs with
      | nil => simp [drop]
      | cons x xs => simp [drop, ih]

-- BEGIN SPEC
theorem length_take {α : Type} (n : Nat) (xs : List α) : (take n xs).length = min n xs.length :=
-- END SPEC
  by
    induction n generalizing xs with
    | zero => simp [take]
    | succ n ih =>
      cases xs with
      | nil => simp [take]
      | cons x xs => simp [take, ih]

theorem drop_nil {α : Type} (m : Nat) : drop m ([] : List α) = [] := by
  cases m <;> rfl

-- BEGIN SPEC
theorem drop_drop {α : Type} (m n : Nat) (xs : List α) : drop m (drop n xs) = drop (n + m) xs :=
-- END SPEC
  by
    induction n generalizing xs with
    | zero => simp [drop]
    | succ n ih =>
      cases xs with
      | nil => simp [drop, drop_nil]
      | cons x xs =>
        -- WHY: `drop` only unfolds on a literal `_ + 1`, so reshape `n + 1 + m` first.
        rw [show n + 1 + m = (n + m) + 1 by omega]
        simp [drop, ih]

end M01

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both functions recurse on the number and the list at once: induct on `n`, then split `xs`.
H2. `induction n generalizing xs`, then in the `succ` case `cases xs`; finish with `simp [take, drop, ih]` (+ `omega`).
H3. For `drop_drop` you need `drop m [] = []` (by `cases m <;> rfl`) and `rw [show n + 1 + m = (n + m) + 1 by omega]`.
-/
