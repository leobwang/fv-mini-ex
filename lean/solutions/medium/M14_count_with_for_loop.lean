/- M14 | Count with a for loop | 10-15 min | Id.run, do, for, let mut, foldl [R06]
GOAL
  `countLoop` counts occurrences of `k` with an imperative `for` loop. Prove it agrees with the
  recursive specification `count`.

REFERENCE
  def sumLoop (xs : List Nat) : Nat := Id.run do
    let mut s := 0
    for x in xs do
      s := s + x
    return s
  example (xs : List Nat) : sumLoop xs = xs.foldl (fun b a => b + a) 0 := by simp [sumLoop]
    -- `simp [f]` turns a pure `for` loop over a list into `List.foldl`
  #check List.foldl_cons   -- List.foldl f b (a :: l) = List.foldl f (f b a) l
  The loop variable is a `foldl` accumulator: generalise it (as in M02).
-/

namespace M14

-- BEGIN SPEC
def count (k : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x = k then 1 else 0) + count k xs

def countLoop (k : Nat) (xs : List Nat) : Nat := Id.run do
  let mut c := 0
  for x in xs do
    c := c + (if x = k then 1 else 0)
  return c
-- END SPEC

theorem foldl_count (k : Nat) (xs : List Nat) (c : Nat) :
    xs.foldl (fun b a => b + if a = k then 1 else 0) c = c + count k xs := by
  induction xs generalizing c with
  | nil => simp [count]
  | cons x xs ih => simp only [List.foldl_cons, ih, count]; omega

-- BEGIN SPEC
theorem countLoop_spec (k : Nat) (xs : List Nat) : countLoop k xs = count k xs :=
-- END SPEC
  by simp [countLoop, foldl_count]

end M14

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Run `simp [countLoop]` and look at the goal: it is a `List.foldl` starting from `0`.
H2. Prove what the fold computes from an arbitrary start value `c`, by induction generalising `c`.
H3. `theorem foldl_count (k : Nat) (xs : List Nat) (c : Nat) : xs.foldl (fun b a => b + if a = k then 1 else 0) c = c + count k xs`.
-/
