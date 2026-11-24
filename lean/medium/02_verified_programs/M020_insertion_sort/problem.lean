/- M020 | Insertion sort | 20 min | inductive Sorted, List.Perm, induction on derivations [R14]
GOAL
  Prove insertion sort returns a sorted permutation of its input.

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M020

-- BEGIN SPEC
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons {x y : Nat} {rest : List Nat} : x ≤ y → Sorted (y :: rest) → Sorted (x :: y :: rest)

def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (isort xs)
-- END SPEC

/- SKELETON · isort_sorted
  0. MILESTONE first, as your own theorem above this one (outside the spec):
       theorem ins_sorted (x : Nat) {l : List Nat} (h : Sorted l) : Sorted (ins x l)
     a. Induction on the derivation `h`, naming `@cons y z rest hyz hs ih`:  R1
     b. nil:  the goal `Sorted (ins x [])` computes to `Sorted [x]`:           R2
     c. single y:  split on `x ≤ y`; unfold `ins`, pick the branch (goals
        `Sorted [x, y]` / `Sorted [y, x]`); build them with `.cons` from `.single`:
                                                                              R4, R5 → R6 / R7, R3, R2, R9
     d. cons y z rest:  split on `x ≤ y`.
          x ≤ y:   unfold, pick the branch, `.cons` from `hxy` and `.cons hyz hs`: R5 → R6, R3
          ¬x ≤ y:  `ih : Sorted (ins x (z :: rest))` and the goal's inner `ins x (z :: rest)`
                   evaluate only after a second split on `x ≤ z`. In each branch rewrite
                   `ih` with `hxz`, and the goal with BOTH `hxy` and `hxz` (with `hxz`
                   alone the outer `if x ≤ y` stays); then `.cons` with `ih` as its
                   second premise:                                            R4, R8, R5 → R6 / R7, R3, R9
  1. `isort_sorted`: induction on `xs`:                                         R10
  2. nil:  the goal `Sorted (isort [])` computes to `Sorted []`:               R2
  3. cons x xs ih:  the goal `Sorted (isort (x :: xs))` computes to
     `Sorted (ins x (isort xs))`; `exact` the milestone applied to `x` and `ih`: R15
-/
-- BEGIN SPEC
theorem isort_sorted (xs : List Nat) : Sorted (isort xs) :=
-- END SPEC
  sorry

/- SKELETON · isort_perm
  0. MILESTONE first, as your own theorem above this one (outside the spec):
       theorem ins_perm (x : Nat) (l : List Nat) : (ins x l).Perm (x :: l)
     a. Induction on `l`:                                                      R10
     b. nil:  both sides compute to `[x]`:                                     R11
     c. cons y ys ih:  split on `x ≤ y`:                                       R4
          x ≤ y:   unfold, pick the branch, then both sides are equal:         R5 → R6, R11
          ¬x ≤ y:  unfold, pick the branch; the goal is
                   `(y :: ins x ys).Perm (x :: y :: ys)`: chain (`a ~ b` is `a.Perm b`)
                   `y :: ins x ys ~ y :: x :: ys ~ x :: y :: ys`:              R5 → R7, R12 (on ih) → R13 → R14
  1. `isort_perm`: induction on `xs`:                                           R10
  2. nil:  the goal `(isort []).Perm []` computes to `[].Perm []`:              R11
  3. cons x xs ih:  the goal `(isort (x :: xs)).Perm (x :: xs)` computes to
     `(ins x (isort xs)).Perm (x :: xs)`; chain `ins x (isort xs) ~ x :: isort xs ~ x :: xs`:
       the milestone `ins_perm x (isort xs)`, then `ih` under the head `x`:      R15 → R13 → R12
-/
-- BEGIN SPEC
theorem isort_perm (xs : List Nat) : (isort xs).Perm xs :=
-- END SPEC
  sorry

end M020

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems reduce to facts about one `ins` step: it keeps a sorted list sorted, and it adds
    exactly `x`. State these two milestones as your own theorems before `isort_sorted`.
H2. `ins_sorted : Sorted l → Sorted (ins x l)` by induction on the `Sorted` derivation (not on `l`);
    in the `cons` case split on `x ≤ y`, and in its `¬x ≤ y` branch split on `x ≤ z` too.
    `ins_perm : (ins x l).Perm (x :: l)` by induction on `l` with a split on `x ≤ y`. The two `isort`
    theorems are then inductions on `xs` that apply the milestones in the `cons` case.
H3. In the cons case with `¬x ≤ y`, the IH is `Sorted (ins x (z :: rest))`; unfold it with
    `simp only [ins, hxz, if_true] at ih` (or `if_false`) and finish with `.cons (by omega) ih` or
    `.cons hyz ih`. Perm step: `(ih.cons y).trans (List.Perm.swap x y ys)`; for `isort_perm`:
    `(ins_perm x (isort xs)).trans (ih.cons x)`.
-/
