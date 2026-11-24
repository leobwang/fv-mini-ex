/- M030 | Merge sorted lists | 20 min | lexicographic termination, List.Perm, List.Pairwise [R15]
GOAL
  Implement `merge` of two sorted lists. Prove the result is a permutation of `xs ++ ys` and is
  sorted whenever both inputs are.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M030

/- SKELETON · merge
  1. Match on both lists at once, three arms: `[], ys` · `x :: xs, []` · `x :: xs, y :: ys`     R1
  2. Empty list: return the other one.
  3. Two heads: `if x ≤ y` put `x` first and merge `xs` with the whole `y :: ys`; else put `y`
     first and merge the whole `x :: xs` with `ys`. Each call shrinks one list and keeps the
     other: Lean finds the termination order itself (no `termination_by`)                    R1
  4. Test it: `example : merge [1, 4] [2, 3] = [1, 2, 3, 4] := by simp [merge]` (`rfl` fails)  R1
-/
-- BEGIN SPEC
def merge (xs ys : List Nat) : List Nat :=
-- END SPEC
  match xs, ys with
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

/- SKELETON · merge_perm  (prove it first: merge_sorted uses it)
  1. `fun_induction merge xs ys`: four cases (arms 1, 2, and arm 3 split by its `if`)           R2
  2. case1 `ys.Perm ([] ++ ys)`: reflexivity, `[] ++ ys` computes to `ys`                       R3
  3. case2 `(x :: xs).Perm (x :: xs ++ [])`: `++ []` does not compute; simplify                 R4
  4. case3 (`x ≤ y`): both sides start with `x`; drop the head, then `ih`                       R5
  5. case4 (`¬x ≤ y`): `y` sits in the middle of the right side; a two-step chain
       `y :: merge … ~ y :: (x :: xs ++ ys) ~ x :: xs ++ y :: ys`                               R6 → R5 (ih) → R7 → R8
-/
-- BEGIN SPEC
theorem merge_perm (xs ys : List Nat) : (merge xs ys).Perm (xs ++ ys) :=
-- END SPEC
  by
    fun_induction merge xs ys with
    | case1 ys => exact .refl _
    | case2 x xs => simp
    | case3 x xs y ys h ih => exact ih.cons x
    | case4 x xs y ys h ih => exact (ih.cons y).trans List.perm_middle.symm

/- SKELETON · merge_sorted  (uses merge_perm)
  1. `fun_induction merge xs ys` with `hx hy` left in context: each `ih` asks for the
     sortedness of the recursive call's arguments                                            R9
  2. case1, case2: `hy`, `hx`
  3. case3 (`x ≤ y`): split off the head                                                     R10
       tail: `ih` fed with the tails' sortedness                                             R11
       head bound: name the element, move `hz` to `xs ++ y :: ys` (merge_perm), split it    R12 → R13 → R14 → R15
       three cases `z ∈ xs | z = y | z ∈ ys`                                                  R16
         z ∈ xs: R17 on hx      z = y: hxy      z ∈ ys: R18 with hxy and R17 on hy           R17, R18
  4. case4 (`¬x ≤ y`): the same with the roles swapped (R11 on hy this time); the same
     rewrite now gives `hz : (z = x ∨ z ∈ xs) ∨ z ∈ ys`          R10 → R11, R12 → R13 → R14 → R15 → R16
       z = x: `x` became `z`, so `hxy : ¬z ≤ y`; `y ≤ z` is arithmetic                       R19
       z ∈ xs: R17 on hx gives `x ≤ z`; with `hxy : ¬x ≤ y` that is arithmetic               R17, R19
       z ∈ ys: R17 on hy                                                                      R17
-/
-- BEGIN SPEC
theorem merge_sorted (xs ys : List Nat) (hx : xs.Pairwise (· ≤ ·)) (hy : ys.Pairwise (· ≤ ·)) :
    (merge xs ys).Pairwise (· ≤ ·) :=
-- END SPEC
  by
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

end M030

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `merge` by `match xs, ys with` (R1) and test it with `simp [merge]`. Prove `merge_perm`
    first, then `merge_sorted`; both by `fun_induction merge xs ys` (R2, R9), four cases each.
    Sortedness needs `merge_perm` to know which elements end up behind the head.
H2. merge_perm: each case is a permutation chain; only case4 (`y` first) needs `List.perm_middle`.
    merge_sorted: split the head off with `List.Pairwise.cons`; for the head bound, an element of
    `merge xs ys` is an element of `xs ++ ys` (merge_perm), so it lies in one input or is the other
    head; finish with `List.rel_of_pairwise_cons`, `Nat.le_trans` or `omega`.
H3. merge_perm case4: `(ih.cons y).trans List.perm_middle.symm`. merge_sorted case3:
    `refine List.Pairwise.cons ?_ (ih hx.of_cons hy)`, `intro z hz`,
    `rw [(merge_perm _ _).mem_iff, List.mem_append, List.mem_cons] at hz`, `rcases hz with hz | rfl | hz`;
    in case4 the pattern is `rcases hz with (rfl | hz) | hz`.
-/
