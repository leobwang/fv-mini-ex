/- M024 | Is sorted | 15 min | List.Pairwise, Bool vs Prop, fun_induction [R08]
GOAL
  Implement a Boolean check `isSorted` that compares adjacent elements, and prove it returns
  `true` exactly when every earlier element is ≤ every later one (`List.Pairwise`).

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M024

/- SKELETON · isSorted
  1. Match on the list, three arms: `[]` · `[_]` · `x :: y :: rest`                          R1
  2. `[]` and `[_]` are sorted: return `true`.
  3. `x :: y :: rest`: the Bool test of `x ≤ y` AND the recursive check of `y :: rest`
     (`y` must stay: it is compared with what follows)                                      R1
  4. Test it: `example : isSorted [1, 2, 2] = true ∧ isSorted [2, 1] = false := by decide`  R1
-/
-- BEGIN SPEC
def isSorted (xs : List Nat) : Bool :=
-- END SPEC
  sorry

/- SKELETON · isSorted_iff
  1. `fun_induction isSorted xs`, three cases: `case1`, `case2 x`, `case3 x y rest ih`;
     `ih` is the whole statement for `y :: rest`                                            R2
  2. case1, case2: lists with fewer than two entries                                        R3
  3. case3: Bool side → Props, and the IH, in one `simp only`                                R4, R5, R6
       goal: `x ≤ y ∧ Pairwise (y :: rest) ↔ Pairwise (x :: y :: rest)`
       (here `Pairwise` abbreviates `List.Pairwise (fun x1 x2 => x1 ≤ x2)`)
  4. Split the `↔`                                                                           R7
  5. → : take `hxy : x ≤ y`, `hp : Pairwise (y :: rest)` apart                               R8
       head bound + tail (the tail is `hp`)                                                  R9
       name the element `a ∈ y :: rest`, split it                                            R10 → R11 → R12
         a = y:       `hxy`
         a ∈ rest:    `x ≤ y` and `y ≤ a` (from `hp`)                                        R13 with R14
  6. ← : `h : Pairwise (x :: y :: rest)`; prove the `∧` with `⟨_, _⟩`
       `x ≤ y`: the head is related to the second entry                                     R14 with R15
       the tail is sorted                                                                    R16
-/
-- BEGIN SPEC
theorem isSorted_iff (xs : List Nat) : isSorted xs = true ↔ xs.Pairwise (· ≤ ·) :=
-- END SPEC
  sorry

end M024

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three arms: empty, singleton, and `x :: y :: rest`, which compares `x ≤ y` (with `decide`) and
    recurses on `y :: rest` (R1). Prove the theorem along the function: `fun_induction isSorted xs`
    (R2); the first two cases are `simp` (R3).
H2. In case3, `simp only [Bool.and_eq_true, decide_eq_true_eq, ih]` (R4–R6) leaves
    `x ≤ y ∧ Pairwise (y :: rest) ↔ Pairwise (x :: y :: rest)`. Split it with `constructor` (R7).
    → : `Pairwise (x :: …)` needs `x ≤ a` for EVERY later `a`; transitivity through `y` gives it.
    ← : the head is related to the second entry, and the tail is pairwise.
H3. → : after `rintro ⟨hxy, hp⟩`, `refine List.Pairwise.cons ?_ hp`; split `a ∈ y :: rest` with
    `List.mem_cons` and `rcases … with rfl | ha`; the second case chains `hxy` with
    `List.rel_of_pairwise_cons hp ha` by `Nat.le_trans`.
    ← : `⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩`.
-/
