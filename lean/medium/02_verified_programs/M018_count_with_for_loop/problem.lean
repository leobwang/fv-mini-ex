/- M018 | Count with a for loop | 10-15 min | Id.run, do, for, let mut, foldl [R06]
GOAL
  `countLoop` counts occurrences of `k` with an imperative `for` loop. Prove it agrees with the
  recursive specification `count`.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M018

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

/- SKELETON · countLoop_spec
  1. MILESTONE first (a helper theorem above this one): what the fold computes from an
     ARBITRARY start value `c`. Its left side is the fold R1 prints for `countLoop`, with `c`
     in place of `0`; its right side is `c + count k xs`.
       induction on `xs`, generalising `c`:                                R4
       `nil`:  fold over `[]`, then `count []`, then `c + 0`:              R2, R5, R8
       `cons`: one fold step, the induction hypothesis at the new start
               value, one equation of `count`, then arithmetic:            R3, R6, R5 → R7
  2. Main theorem: loop → fold from `0`, rewrite with the milestone at
     `c := 0`, then `0 + n`:                                                R1, R6, R8
     (one `simp [...]` call can do all three when given the milestone)
-/
-- BEGIN SPEC
theorem countLoop_spec (k : Nat) (xs : List Nat) : countLoop k xs = count k xs :=
-- END SPEC
  sorry

end M018

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Run `simp [countLoop]` and look at the goal: it is a `List.foldl` starting from `0` (R1). Induction
    on that goal gets stuck, because `List.foldl_cons` changes the start value (R3).
H2. Prove a milestone about the fold from an arbitrary start value `c`, by
    `induction xs generalizing c` (R4); then `countLoop_spec` is R1 plus the milestone at `c := 0`.
H3. `theorem foldl_count (k : Nat) (xs : List Nat) (c : Nat) : xs.foldl (fun b a => b + if a = k then 1 else 0) c = c + count k xs`.
    Its `cons` case: `simp only [List.foldl_cons, ih, count]` then `omega`.
-/
