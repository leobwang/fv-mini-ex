/- M033 | Prefix sums | 10-15 min | List.map, List.take, getElem?, induction generalizing [R18]
GOAL
  Implement `prefixSums xs`, whose entry `i` is the sum of the first `i` elements of `xs`
  (so it has one more entry than `xs`, starting with 0).

REFERENCE
  example : [1, 2, 3].take 2 = [1, 2] := rfl
  #check List.getElem?_map     -- (List.map f l)[i]? = Option.map f l[i]?
  #check List.take_succ_cons   -- List.take (i + 1) (a :: as) = a :: List.take i as
  #check List.sum_cons         -- (a :: l).sum = a + l.sum
  example (xs : List Int) (x : Int) : (x :: xs)[0]? = some x := rfl
  -- Idea: prefixSums (x :: xs) = 0 :: (add x to every entry of prefixSums xs).
-/

namespace M033

-- BEGIN SPEC
def prefixSums (xs : List Int) : List Int :=
-- END SPEC
  match xs with
  | [] => [0]
  | x :: xs => 0 :: (prefixSums xs).map (x + ·)

-- BEGIN SPEC
theorem prefixSums_length (xs : List Int) : (prefixSums xs).length = xs.length + 1 :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [prefixSums, ih]

-- BEGIN SPEC
theorem prefixSums_get (xs : List Int) (i : Nat) (h : i ≤ xs.length) :
    (prefixSums xs)[i]? = some (xs.take i).sum :=
-- END SPEC
  by
    induction xs generalizing i with
    | nil => simp at h; subst h; rfl
    | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
        simp at h
        simp [prefixSums, List.getElem?_map, ih i (by omega)]

end M033

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Build the list recursively: the head entry is 0, the rest are shifted by `x`.
H2. `prefixSums_get`: induction on `xs` generalising `i`, then `cases i`.
H3. Implementation `| [] => [0] | x :: xs => 0 :: (prefixSums xs).map (x + ·)`; succ case: `simp [prefixSums, List.getElem?_map, ih i (by omega)]`.
-/
