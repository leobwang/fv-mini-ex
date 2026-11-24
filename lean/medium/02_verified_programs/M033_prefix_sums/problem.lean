/- M033 | Prefix sums | 10-15 min | List.map, List.take, getElem?, induction generalizing [R18]
GOAL
  Implement `prefixSums xs`, whose entry `i` is the sum of the first `i` elements of `xs`
  (so it has one more entry than `xs`, starting with 0).

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M033

/- SKELETON · prefixSums
  1. Match on the list, two arms: `[]` · `x :: xs`                                         R1
  2. `[]`: the only prefix of the empty list is empty, sum 0: one entry.
  3. `x :: xs`: the entry `0` first, then every prefix sum of `xs` plus `x`
     (recursive call on `xs`, shifted with `List.map (x + ·)`)                             R1, R2
  4. Test it: `example : prefixSums [1, 2, 3] = [0, 1, 3, 6] := by rfl`                     R1
-/
-- BEGIN SPEC
def prefixSums (xs : List Int) : List Int :=
-- END SPEC
  sorry

/- SKELETON · prefixSums_length
  1. Induction on `xs`                                                                       R3
  2. nil: both sides compute                                                                 rfl
  3. cons: unfold one step, lengths of `::` and `map`, then the IH:
       `simp` with `prefixSums` and `ih`                                                     R4, R5, R6
-/
-- BEGIN SPEC
theorem prefixSums_length (xs : List Int) : (prefixSums xs).length = xs.length + 1 :=
-- END SPEC
  sorry

/- SKELETON · prefixSums_get
  1. Induction on `xs`, generalizing `i` (the step lowers the index by one)                  R7
  2. nil: `h : i ≤ [].length` → `h : i = 0`, substitute, then both sides compute             R8 → R9 → rfl
  3. cons: split the index                                                                   R10
       zero: both sides compute                                                              R11
       succ i: first `h : i ≤ xs.length`                                                     R12
               then one `simp` with `prefixSums`, the IH at `i` and these lemmas:
               left side   R4 → R13 → R14 → IH via R15 → R16
               right side  R17 → R18
-/
-- BEGIN SPEC
theorem prefixSums_get (xs : List Int) (i : Nat) (h : i ≤ xs.length) :
    (prefixSums xs)[i]? = some (xs.take i).sum :=
-- END SPEC
  sorry

end M033

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Build the list recursively (R1): the head entry is 0, the rest are the prefix sums of the tail,
    each shifted by the head `x` with `List.map` (R2). Test it with `rfl` before proving anything.
H2. Length: `induction xs` (R3), `rfl` and `simp [prefixSums, ih]`. Index: the IH is needed at a
    different index, so `induction xs generalizing i` (R7), then `cases i` (R10) in the `cons` case.
    nil: `simp at h; subst h; rfl` (R8, R9). zero: `rfl` (R11). succ: `simp at h` (R12) first, so that
    `omega` can prove the IH's bound.
H3. Implementation `| [] => [0] | x :: xs => 0 :: (prefixSums xs).map (x + ·)`; succ case:
    `simp [prefixSums, List.getElem?_map, ih i (by omega)]`.
-/
