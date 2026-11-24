/- M017 | Quicksort terminates | 15-20 min | decreasing_by, termination_by, fun_induction
GOAL
  Lean cannot see that quicksort's recursive calls are on shorter lists. Prove termination in
  `decreasing_by`, then prove `qsort` keeps exactly the same elements and the same length.

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def lows (p : Nat) (xs : List Nat) : List Nat := xs.filter (· < p)
def highs (p : Nat) (xs : List Nat) : List Nat := xs.filter (fun x => ¬ x < p)
-- END SPEC

theorem lows_le (p : Nat) (xs : List Nat) : (lows p xs).length ≤ xs.length :=
  List.length_filter_le _ _

theorem highs_le (p : Nat) (xs : List Nat) : (highs p xs).length ≤ xs.length :=
  List.length_filter_le _ _

/- SKELETON · qsort (the `decreasing_by` block)
  `decreasing_by` has two goals, one per recursive call:                      R1
     ⊢ (lows p xs).length < (p :: xs).length      (and the same with `highs`)
  For each goal, focused with `·`:
  1. Put the helper's bound in the context (`lows_le` / `highs_le`):          R2 (proved by R3)
  2. Rewrite the length of the cons `p :: xs`:                                R4
  3. Finish the arithmetic:                                                   R5
-/
-- BEGIN SPEC
def qsort : List Nat → List Nat
  | [] => []
  | p :: xs => qsort (lows p xs) ++ p :: qsort (highs p xs)
termination_by xs => xs.length
-- END SPEC
decreasing_by
  · have := lows_le p xs; simp only [List.length_cons]; omega
  · have := highs_le p xs; simp only [List.length_cons]; omega

/- SKELETON · mem_qsort
  1. Induction along qsort's equations, naming case2's pivot, tail and the
     two IHs (first one = the `lows` call):                                   R6
  2. case1: both sides are `x ∈ []`:                                          simp
  3. case2: split the left side's `++` and `::`, then use both IHs, all
     BEFORE unfolding anything:                                               R7, R8, R9
       goal: x ∈ lows p xs ∨ x = p ∨ x ∈ highs p xs ↔ x ∈ p :: xs
  4. Unfold lows/highs and turn filter membership into `x ∈ xs ∧ x < p`:      R10, R11, R12
  5. The rest is propositional logic plus `x ∈ p :: xs`:                      R13
-/
-- BEGIN SPEC
theorem mem_qsort (x : Nat) (xs : List Nat) : x ∈ qsort xs ↔ x ∈ xs :=
-- END SPEC
  by
    fun_induction qsort xs with
    | case1 => simp
    | case2 p xs ih1 ih2 =>
      rw [List.mem_append, List.mem_cons, ih1, ih2]
      simp only [lows, highs, List.mem_filter, decide_eq_true_eq]
      grind

/- SKELETON · qsort_length
  1. The same induction as mem_qsort:                                         R6
  2. case1: `[].length = [].length`:                                          rfl
  3. case2: lengths of `++` and `::`, the IHs (`rw [ih1, ih2]`), then the
     length of `p :: xs`:                                         R14, R4, rw [ih1, ih2], R4
       goal: (lows p xs).length + ((highs p xs).length + 1) = xs.length + 1
  4. The fact that ties the two filters to xs, from a permutation:           R15 → R16
     then split its `++` length inside the hypothesis:                        R17 with R14
  5. Make the goal read like that fact: unfold lows highs, then turn
     `decide ¬x < p` into `!decide (x < p)`:                                  R10, R18
  6. Linear arithmetic:                                                       R5
-/
-- BEGIN SPEC
theorem qsort_length (xs : List Nat) : (qsort xs).length = xs.length :=
-- END SPEC
  by
    fun_induction qsort xs with
    | case1 => rfl
    | case2 p xs ih1 ih2 =>
      rw [List.length_append, List.length_cons, ih1, ih2, List.length_cons]
      have := (List.filter_append_perm (fun x => decide (x < p)) xs).length_eq
      rw [List.length_append] at this
      unfold lows highs
      simp only [decide_not]
      omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each recursive call is on a filter of `xs`, so its length is ≤ `xs.length` < `(p :: xs).length`;
    `lows_le` / `highs_le` give the `≤`. For the theorems, induct along `qsort`'s own recursion
    (`fun_induction qsort xs`), not on the list: `induction xs` gives an IH about the tail, which
    `qsort` never calls.
H2. `decreasing_by`: one `·` per goal: `have` the helper, rewrite `List.length_cons`, `omega`.
    `mem_qsort`, case2: `rw` with `List.mem_append`, `List.mem_cons` and the two IHs first, then
    `simp only [lows, highs, List.mem_filter, decide_eq_true_eq]` and `grind`.
    `qsort_length`, case2: `rw` the lengths and IHs, then get "lows length + highs length = xs.length"
    from `List.filter_append_perm` and `List.Perm.length_eq`, and finish with `omega`.
H3. `· have := lows_le p xs; simp only [List.length_cons]; omega` (the same for `highs`).
    `fun_induction qsort xs with | case1 => … | case2 p xs ih1 ih2 => rw [List.mem_append, List.mem_cons, ih1, ih2]; …`.
    Length fact: `have := (List.filter_append_perm (fun x => decide (x < p)) xs).length_eq`, then
    `rw [List.length_append] at this`; `omega` needs the goal in the same form, so
    `unfold lows highs` and `simp only [decide_not]` first.
-/
