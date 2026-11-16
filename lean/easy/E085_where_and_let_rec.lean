/- E085 | where and let rec | 2-3 min | where, let rec, auxiliary definitions, induction generalizing
GOAL
  `countdown` and `sumList` hide an accumulator helper (`countdown.go` via `where`, `sumList.loop` via
  `let rec`). Prove each helper's invariant for every accumulator, then the main fact.
  `countdown n` counts `k` down from `n` while consing `k` onto `acc`, so it builds the ascending list
  `[0, 1, …, n-1]` (`xs.sum` is the sum of the list's elements).

REFERENCE
  def len (xs : List Nat) : Nat := go xs 0 where go : List Nat → Nat → Nat | [], a => a | _ :: t, a => go t (a + 1)
  def len' (xs : List Nat) : Nat := let rec go : List Nat → Nat → Nat | [], a => a | _ :: t, a => go t (a + 1); go xs 0
  #check @len.go           -- both forms define a separate top-level function: `len.go`, `len'.go`
  example (xs : List Nat) : len xs = len.go xs 0 := rfl   -- `simp [len]` exposes the helper call
  example : len.go [1, 2] 5 = 7 := by simp [len.go]        -- the helper has its own equations
  `induction xs generalizing a with …`: the IH then holds for every accumulator `a` (the step needs `a + 1`)
  #check @List.range_succ  -- List.range (n + 1) = List.range n ++ [n]   (List.range n = [0, …, n-1])
BANNED: grind, try?, exact?
NOTE: without `generalizing acc` the IH only speaks about the original `acc` and the step gets stuck.
-/

namespace E085

-- BEGIN SPEC
def countdown (n : Nat) : List Nat := go n []
where
  go : Nat → List Nat → List Nat
    | 0, acc => acc
    | k + 1, acc => go k (k :: acc)

def sumList (xs : List Nat) : Nat :=
  let rec loop : List Nat → Nat → Nat
    | [], acc => acc
    | x :: xs, acc => loop xs (acc + x)
  loop xs 0
-- END SPEC

-- BEGIN SPEC
theorem go_spec (n : Nat) (acc : List Nat) : countdown.go n acc = List.range n ++ acc :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem countdown_eq (n : Nat) : countdown n = List.range n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem loop_spec (xs : List Nat) (acc : Nat) : sumList.loop xs acc = acc + xs.sum :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sumList_eq (xs : List Nat) : sumList xs = xs.sum :=
-- END SPEC
  sorry

end E085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The main facts follow from the helper invariants with `acc := []` and `acc := 0`.
H2. Prove the invariants by induction on `n` (resp. `xs`), generalizing the accumulator. In the step
    for `go`, `List.range (k + 1)` splits as `List.range k ++ [k]`.
H3. `induction n generalizing acc with | zero => rfl | succ k ih => simp [countdown.go, ih, List.range_succ]`;
    then `simp [countdown, go_spec]`. `loop_spec` has the same shape (finish its step with `omega`).
-/
