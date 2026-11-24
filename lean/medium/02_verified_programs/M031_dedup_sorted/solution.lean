/- M031 | Dedup a sorted list | 15 min | List.Pairwise, strict order, fun_induction [R16]
GOAL
  Implement `dedup`, which removes adjacent duplicates. Prove it keeps the same elements, and that
  on a sorted input the output is strictly increasing.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M031

/- SKELETON · dedup
  1. Match on the list, three arms: `[]` · `[x]` · `x :: y :: rest`                           R1
  2. `[]` and `[x]` have no duplicates: return them unchanged.
  3. `x :: y :: rest`: `if x = y` drop `x`, else keep it; in BOTH branches recurse on
     `y :: rest` (`y` must stay: it is compared with what follows)                           R1
  4. Test it: `example : dedup [1, 1, 2, 2, 2, 3] = [1, 2, 3] := by rfl`                     R1
-/
-- BEGIN SPEC
def dedup (xs : List Nat) : List Nat :=
-- END SPEC
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedup (y :: rest) else x :: dedup (y :: rest)

/- SKELETON · dedup_mem  (prove it first: dedup_strict uses it)
  1. `fun_induction dedup xs`, four cases: `case1`, `case2 x`, `case3 x rest ih` (the `then`
     branch, `y` already replaced by `x`), `case4 x y rest h ih`                             R2
  2. case1, case2: both sides are the same list                                              simp
  3. case3, case4: rewrite the goal with the `↔` IH, then unfold `∈ _ :: _`                    R4 (uses ih, R3)
-/
-- BEGIN SPEC
theorem dedup_mem (xs : List Nat) (z : Nat) : z ∈ dedup xs ↔ z ∈ xs :=
-- END SPEC
  by
    fun_induction dedup xs with
    | case1 => simp
    | case2 x => simp
    | case3 x rest ih => simp_all
    | case4 x y rest h ih => simp_all

/- SKELETON · dedup_strict  (uses dedup_mem)
  1. `fun_induction dedup xs` with `h` kept: each IH asks for the sortedness of the
     recursive call's argument                                                               R2, R5
  2. case1, case2: lists of length ≤ 1                                                       R6
  3. case3 (`x = y`, dropped): `h : Pairwise (x :: x :: rest)`, the IH wants `x :: rest`      R7
  4. case4 (`hxy : ¬x = y`, `x` kept): split off the head, the tail from the IH               R8, R7
       head bound: name the element, move `hz` into `y :: rest` (dedup_mem)                  R9 → R10
       fact `h1 : x ≤ y` from sortedness                                                      R11, R12
       split `hz : z = y ∨ z ∈ rest`                                                          R3 → R13
         z = y:      `x ≤ z` and `¬x = z`                                                    R14
         z ∈ rest:   `h2 : y ≤ z` from the tail's sortedness, then arithmetic                R11 with R7, R14
-/
-- BEGIN SPEC
theorem dedup_strict (xs : List Nat) (h : xs.Pairwise (· ≤ ·)) : (dedup xs).Pairwise (· < ·) :=
-- END SPEC
  by
    fun_induction dedup xs with
    | case1 => simp
    | case2 x => simp
    | case3 x rest ih => exact ih h.of_cons
    | case4 x y rest hxy ih =>
      refine List.Pairwise.cons ?_ (ih h.of_cons)
      intro z hz
      rw [dedup_mem] at hz
      have h1 : x ≤ y := List.rel_of_pairwise_cons h List.mem_cons_self
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · have h2 : y ≤ z := List.rel_of_pairwise_cons h.of_cons hz
        omega

end M031

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare the first two entries; drop the first if they are equal, and recurse on the list that
    starts with the second (R1). Prove `dedup_mem` first: `dedup_strict` needs it to know where the
    entries of the recursive result come from. Both proofs: `fun_induction dedup xs` (R2), four cases.
H2. dedup_mem: `simp` for the short lists, `simp_all` (R4) when the IH is an `↔`. dedup_strict: the
    IH is an implication `Pairwise (· ≤ ·) (…) → …` (R5), fed with `h.of_cons` (R7). Only case4 needs
    work: `List.Pairwise.cons` (R8), then for `z ∈ dedup (y :: rest)` get `z ∈ y :: rest`
    (`dedup_mem`), `x ≤ y` and `y ≤ z` from `List.rel_of_pairwise_cons`, and `x ≠ y` from the case.
H3. Case4: `refine List.Pairwise.cons ?_ (ih h.of_cons)`, `intro z hz`, `rw [dedup_mem] at hz`,
    `have h1 : x ≤ y := List.rel_of_pairwise_cons h List.mem_cons_self`,
    `rw [List.mem_cons] at hz`, `rcases hz with rfl | hz`; each goal by `omega` (the second after
    `have h2 : y ≤ z := List.rel_of_pairwise_cons h.of_cons hz`).
-/
