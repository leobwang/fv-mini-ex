/- E085 | where and let rec | 2-3 min | where, let rec, auxiliary definitions, induction generalizing
GOAL
  `countdown` and `sumList` hide an accumulator helper (`countdown.go` via `where`, `sumList.loop` via
  `let rec`). Prove each helper's invariant for every accumulator, then the main fact.
  `countdown n` counts `k` down from `n` while consing `k` onto `acc`, so it builds the ascending list
  `[0, 1, …, n-1]` (`xs.sum` is the sum of the list's elements).

BANNED: grind, try?, exact?

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · go_spec
  1. Induction on `n`, generalizing the accumulator: the step calls `go k (k :: acc)`,
     so the IH is needed at `k :: acc`, not at `acc`:                       R1
  2. `zero`: both sides compute to `acc`:                                    R2
  3. `succ k ih`:
       unfold one step of `countdown.go`                                     R3
       rewrite the call `countdown.go k (k :: acc)` with `ih`                R4
       split `List.range (k + 1)`                                            R5
       regroup `List.range k ++ [k] ++ acc` into `List.range k ++ k :: acc`  R6 → R7
-/
-- BEGIN SPEC
theorem go_spec (n : Nat) (acc : List Nat) : countdown.go n acc = List.range n ++ acc :=
-- END SPEC
  by
  induction n generalizing acc with  -- WHY: the step calls `go k (k :: acc)`, a different accumulator
  | zero => rfl
  | succ k ih => simp [countdown.go, ih, List.range_succ]

/- SKELETON · countdown_eq
  1. Unfold `countdown` to its helper call `countdown.go n []`:               R8
  2. Rewrite with `go_spec` (Part 1, at `acc := []`):                         R4
  3. Drop `++ []`:                                                            R9
-/
-- BEGIN SPEC
theorem countdown_eq (n : Nat) : countdown n = List.range n :=
-- END SPEC
  by simp [countdown, go_spec]

/- SKELETON · loop_spec
  1. Induction on `xs`, generalizing `acc` (the step calls `loop xs (acc + x)`):  R10
  2. `nil`: unfold `sumList.loop`, then `[].sum` → `0`; `acc = acc + 0` computes:  R11, R12, R2
  3. `cons x xs ih`:
       unfold one step of `sumList.loop`                                      R11
       rewrite `sumList.loop xs (acc + x)` with `ih`                          R4
       expand `(x :: xs).sum`                                                 R13
       regroup `acc + x + xs.sum = acc + (x + xs.sum)`                        R14
-/
-- BEGIN SPEC
theorem loop_spec (xs : List Nat) (acc : Nat) : sumList.loop xs acc = acc + xs.sum :=
-- END SPEC
  by
  induction xs generalizing acc with
  | nil => simp [sumList.loop]
  | cons x xs ih => simp [sumList.loop, ih]; omega

/- SKELETON · sumList_eq
  1. Unfold `sumList` to its helper call `sumList.loop xs 0`:                 R15
  2. Rewrite with `loop_spec` (Part 3, at `acc := 0`):                        R4
  3. `0 + xs.sum` → `xs.sum`:                                                 R16
-/
-- BEGIN SPEC
theorem sumList_eq (xs : List Nat) : sumList xs = xs.sum :=
-- END SPEC
  by simp [sumList, loop_spec]

end E085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each main function is its helper started at a fixed accumulator (`countdown.go n []`,
    `sumList.loop xs 0`). Prove the helper invariants `go_spec`, `loop_spec` first, for every
    accumulator, and then use them at `[]` and `0`.
H2. The invariants: induction on `n` (resp. `xs`) with `generalizing acc`, since the recursive call
    changes the accumulator. In the step, unfold one helper equation, rewrite with `ih` at the new
    accumulator, then tidy up: `List.range_succ`, `List.append_assoc`, `List.singleton_append` for `go`;
    `List.sum_cons` and `omega` for `loop`. The main facts: unfold, rewrite with the invariant,
    `List.append_nil` / `Nat.zero_add`.
H3. `induction n generalizing acc with | zero => rfl | succ k ih => simp [countdown.go, ih, List.range_succ]`;
    then `simp [countdown, go_spec]`. `loop_spec` has the same shape: `simp [sumList.loop, ih]` in the
    step, finished with `omega`.
-/
