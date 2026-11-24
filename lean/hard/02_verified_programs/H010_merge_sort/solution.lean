/- H010 | Merge sort | 1-1.5 h | well-founded recursion, fun_induction, List.Perm, List.Pairwise [R20]
GOAL
  Prove merge sort returns a sorted permutation of its input. `msort` splits the list in half
  with `take`/`drop` and recurses by well-founded recursion on the length.

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H010

-- BEGIN SPEC
abbrev Sorted (xs : List Nat) : Prop := xs.Pairwise (· ≤ ·)

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

def msort (xs : List Nat) : List Nat :=
  if h : xs.length < 2 then xs
  else
    let half := xs.length / 2
    merge (msort (xs.take half)) (msort (xs.drop half))
termination_by xs.length
-- END SPEC

/- SKELETON · merge_perm  (MILESTONE: prove it FIRST; used in merge_sorted and msort_perm)
  Both milestones follow merge's recursion. merge_perm is used in merge_sorted (to locate an
  element of `merge xs ys`) and in msort_perm; merge_sorted is used in msort_sorted.
  1. `fun_induction merge xs ys`: four cases (clauses 1, 2, and clause 3 split by its `if`)     R1
  2. case1 `ys.Perm ([] ++ ys)`: reflexivity, `[] ++ ys` computes to `ys`                       R2
  3. case2 `(x :: xs).Perm (x :: xs ++ [])`: `++ []` does not compute; simplify                 R3
  4. case3 (`x ≤ y`): both sides start with `x` (`x :: xs ++ l` is `x :: (xs ++ l)`)
     drop the head, then `ih`                                                                  R4, R5
  5. case4 (`¬x ≤ y`): `y` sits in the middle of the right side; a two-step chain
     `y :: merge … ~ y :: (x :: xs ++ ys) ~ x :: xs ++ y :: ys`                                 R6, R5 (ih), R7, R8
-/
-- MILESTONE (optional: change or delete)
theorem merge_perm (xs ys : List Nat) : (merge xs ys).Perm (xs ++ ys) := by
  fun_induction merge xs ys with
  | case1 ys => exact .refl _
  | case2 x xs => simp
  | case3 x xs y ys h ih => exact ih.cons x
  | case4 x xs y ys h ih => exact (ih.cons y).trans List.perm_middle.symm

/- SKELETON · merge_sorted  (MILESTONE: prove it SECOND; uses merge_perm, used in msort_sorted)
  1. `fun_induction merge xs ys` with `hx hy` in context: each `ih` asks for the
     sortedness of the recursive call's arguments                                              R9
  2. case1, case2: `hy`, `hx`
  3. case3 (`x ≤ y`): split `Sorted (x :: merge …)` into head bound and tail                   R10
     tail: `ih` fed with the tail of `hx`, and `hy`                                            R11
     head bound: name the element, move `hz` to `xs ++ y :: ys` (merge_perm), split it        R12, R13, R14, R15
     three cases `z ∈ xs | z = y | z ∈ ys`                                                      R16
       z ∈ xs: R17 on hx      z = y: hxy      z ∈ ys: R18 with hxy and R17 on hy               R17, R18
  4. case4 (`¬x ≤ y`): the same with the roles of the two lists swapped:
     tail: `ih` fed with `hx` and the tail of `hy`                                             R10, R11
     head bound: as in case3, now `hz : (z = x ∨ z ∈ xs) ∨ z ∈ ys`                              R12–R16
       z = x: arithmetic from hxy      z ∈ xs: R17 on hx, then arithmetic      z ∈ ys: R17 on hy   R19, R17
-/
-- MILESTONE (optional: change or delete)
theorem merge_sorted (xs ys : List Nat) (hx : Sorted xs) (hy : Sorted ys) : Sorted (merge xs ys) := by
  fun_induction merge xs ys with
  | case1 ys => exact hy
  | case2 x xs => exact hx
  | case3 x xs y ys hxy ih =>
    refine List.Pairwise.cons ?_ (ih hx.of_cons hy)
    intro z hz
    rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact List.rel_of_pairwise_cons hx hz
    · exact hxy
    · exact Nat.le_trans hxy (List.rel_of_pairwise_cons hy hz)
  | case4 x xs y ys hxy ih =>
    refine List.Pairwise.cons ?_ (ih hx hy.of_cons)
    intro z hz
    rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz
    rcases hz with (rfl | hz) | hz
    · omega
    · have := List.rel_of_pairwise_cons hx hz
      omega
    · exact List.rel_of_pairwise_cons hy hz

/- SKELETON · msort_perm  (uses merge_perm)
  1. `fun_induction msort xs`: base case `h : xs.length < 2`; recursive case with
     `half : Nat := xs.length / 2` and one IH per half                                         R20
  2. base: reflexivity                                                                         R2
  3. recursive: the chain  merge (msort take) (msort drop) ~ msort take ++ msort drop ~ xs
       first step: merge_perm                                                                  R6
       combine `ih1`, `ih2` into one fact about `++`                                           R21
       in that fact, `take ++ drop` is `xs`; it is now the goal                                R22
-/
-- BEGIN SPEC
theorem msort_perm (xs : List Nat) : (msort xs).Perm xs :=
-- END SPEC
  by
    fun_induction msort xs with
    | case1 xs h => exact .refl _
    | case2 xs h half ih1 ih2 =>
      refine (merge_perm _ _).trans ?_
      have := (ih1.append ih2)
      rw [List.take_append_drop] at this
      exact this

/- SKELETON · msort_sorted  (uses merge_sorted)
  1. `fun_induction msort xs`                                                                  R20
  2. base: `xs.length < 2`, so `xs` is `[]` or `[x]`; match on `xs` and `h` together            R23
       `[]`: R24      `[x]`: R25   (`Sorted l` is `List.Pairwise (· ≤ ·) l`)
  3. recursive: merge_sorted applied to `ih1` and `ih2`
-/
-- BEGIN SPEC
theorem msort_sorted (xs : List Nat) : Sorted (msort xs) :=
-- END SPEC
  by
    fun_induction msort xs with
    | case1 xs h =>
      match xs, h with
      | [], _ => exact .nil
      | [x], _ => exact List.pairwise_singleton _ x
    | case2 xs h half ih1 ih2 => exact merge_sorted _ _ ih1 ih2

end H010

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the MILESTONES first, each by `fun_induction merge xs ys`; then each `msort` theorem is
    `fun_induction msort xs` plus one milestone. `Sorted l` is `List.Pairwise (· ≤ ·) l`: use the
    `List.Pairwise` lemmas (R10, R11, R17, R24, R25) and the `List.Perm` lemmas (R2–R8, R21).
H2. merge_perm: each case is a permutation chain; only case4 needs `List.perm_middle`.
    merge_sorted: split the head off with `List.Pairwise.cons`; for the head bound, an element of
    `merge xs ys` is an element of `xs ++ ys` (merge_perm), so it lies in `xs`, is the other head,
    or lies in `ys`. msort_perm: `merge … ~ msort take ++ msort drop ~ take ++ drop = xs`.
    msort_sorted: a list of length < 2 is `[]` or `[x]`.
H3. merge_perm case4: `(ih.cons y).trans List.perm_middle.symm`. merge_sorted case3:
    `refine List.Pairwise.cons ?_ (ih hx.of_cons hy)`, `intro z hz`,
    `rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz`, `rcases hz with hz | rfl | hz`.
    msort_perm: `refine (merge_perm _ _).trans ?_; have := ih1.append ih2; rw [List.take_append_drop] at this`.
    msort_sorted base: `match xs, h with | [], _ => exact .nil | [x], _ => exact List.pairwise_singleton _ x`.
-/
