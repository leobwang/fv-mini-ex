/- M001 | take and drop | 10-15 min | induction generalizing, List, cases
GOAL
  Prove four laws about your own `take` and `drop`. The induction hypothesis must work for
  every list, not just the one in the goal.

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

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

/- SKELETON · take_append_drop
  1. Induct on the number with the list free, so `ih : ∀ xs, …`:            R1
  2. `zero`: unfold `take`/`drop` at `0`, then `[] ++ xs = xs`:              R3 → R4
  3. `succ n ih`: split the list:                                           R2
       `nil`:       unfold at `[]`, then `[] ++ [] = []`:                   R3 → R4/R5
       `cons x xs`: unfold one step, pull `x` out of `++`, use `ih` at the
                    tail (one `simp` call does all three):                  R3 → R6 → R7
-/
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

/- SKELETON · length_drop
  1. Same induction and split as `take_append_drop`:                        R1, R2
  2. `zero`:       unfold `drop`, then `n - 0 = n`:                         R3 → R9
  3. `succ.nil`:   unfold, `[].length = 0`, `0 - (n + 1) = 0`:              R3 → R8 → R10
  4. `succ.cons`:  unfold, `(x :: xs).length = xs.length + 1`, cancel the
                   `+ 1` in the subtraction, use `ih`:                       R3 → R8 → R11 → R7
     (`simp` applies R8–R11 by itself: name only `drop` and `ih`.)
-/
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

/- SKELETON · length_take
  1. Same induction and split:                                              R1, R2
  2. `zero`:       unfold `take`, `[].length = 0`, `min 0 _ = 0`:          R3 → R8 → R12
  3. `succ.nil`:   unfold, `[].length = 0`, `min _ 0 = 0`:                  R3 → R8 → R12
  4. `succ.cons`:  unfold, length of a cons, `min (a + 1) (b + 1)`
                   = `min a b + 1`, use `ih`:                                R3 → R8 → R13 → R7
     (If `simp` leaves arithmetic, finish with `omega`:                     R17)
-/
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

/- SKELETON · drop_drop
  0. MILESTONE first, as its own theorem above this one (outside the spec):
       drop_nil : drop m ([] : List α) = []            proof: R15
     It is used in step 3.
  1. Induct on `n` with the list free, then split the list:                 R1, R2
  2. `zero`:       unfold `drop 0`, then `0 + m = m`:                       R3 → R14
  3. `succ.nil`:   unfold `drop (n + 1) []`; both sides are then `drop _ []`,
                   closed by giving the milestone to `simp`:                R3 → R7
  4. `succ.cons`:  `n + 1 + m` is not of the form `_ + 1`: rewrite it to
                   `n + m + 1` FIRST, then unfold and use `ih`:             R16 → R3 → R7
                   (unfolding first leaves `drop (n + m) xs = drop (n + 1 + m) (x :: xs)` stuck)
-/
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

end M001

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both functions recurse on the number and the list at once: induct on `n` with the list
    generalized (R1), then split `xs` (R2). Every case is then closed by unfolding the definitions.
H2. `induction n generalizing xs with | zero => … | succ n ih => cases xs with | nil => … | cons x xs => …`;
    each case is `simp [take, drop]` or `simp [take, drop, ih]` (simp applies the list and `Nat`
    lemmas R4–R14 by itself; `omega` for leftover arithmetic). `drop_drop` needs the milestone
    `drop m [] = []` and a reshaped number in `succ.cons`.
H3. `theorem drop_nil {α : Type} (m : Nat) : drop m ([] : List α) = [] := by cases m <;> rfl`.
    In `drop_drop`: `succ.nil` is `simp [drop, drop_nil]`; `succ.cons` is
    `rw [show n + 1 + m = (n + m) + 1 by omega]` then `simp [drop, ih]`.
-/
