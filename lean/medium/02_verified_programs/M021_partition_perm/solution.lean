/- M021 | Partition is a permutation | 10-15 min | List.Perm, List.filter, pairs
GOAL
  `partition p xs` splits a list in one pass. Show it equals the two filters, and that
  gluing the parts back together is a permutation of the input.

BANNED: List.filter_append_perm

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M021

-- BEGIN SPEC
def partition (p : Nat → Bool) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let r := partition p xs
    if p x then (x :: r.1, r.2) else (r.1, x :: r.2)
-- END SPEC

/- SKELETON · partition_eq
  1. Induction on `xs`:                                                      R1
  2. nil:  both sides compute to `([], [])`:                                  R2
  3. cons x xs ih:  split on the Boolean `p x`, naming the fact `h`:          R3
  4. In both cases, one `simp` with these rewrite rules:
       unfold `partition` one step (the `let` is substituted)                R4
       `ih` for `partition p xs`, then the pair projections                  rw/simp [ih], R10
       each `filter` on `x :: xs`                                            R5
       `h` decides every `if`; simp's clean-up does the rest                 R6 → R9 → R7 → R8
     Both sides are then the same pair, which `simp` closes itself.
-/
-- BEGIN SPEC
theorem partition_eq (p : Nat → Bool) (xs : List Nat) :
    partition p xs = (xs.filter p, xs.filter (fun x => !p x)) :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases h : p x <;> simp [partition, ih, List.filter_cons, h]

/- SKELETON · partition_perm
  1. Use Part 1 BEFORE the induction, so the goal (and later `ih`) is about filters:  R11
  2. Induction on `xs`:                                                      R1
  3. nil:  everything computes to `[]`:                                       R12
  4. cons x xs ih:  split on `p x`, naming `h`; in each case
       rewrite `ih` and the goal with `List.filter_cons` and `h`:            R3, R13 (R5, R6, R10)
       clean the `if`s and `!`:                                              R9, R7, R8
  5. p x = false:  the goal is `(filter p xs ++ x :: filter (!p ·) xs).Perm (x :: xs)`;
       `x` is in the middle: move it to the front, then `ih` under the head:  R16 → R15 → R17
  6. p x = true:  pull `x` out of the append, then `ih` under the head:       R14, R17
-/
-- BEGIN SPEC
theorem partition_perm (p : Nat → Bool) (xs : List Nat) :
    ((partition p xs).1 ++ (partition p xs).2).Perm xs :=
-- END SPEC
  by
    rw [partition_eq]
    induction xs with
    | nil => exact .refl _
    | cons x xs ih =>
      cases h : p x
      · simp only [List.filter_cons, h] at ih ⊢
        simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
        exact List.perm_middle.trans (ih.cons x)
      · simp only [List.filter_cons, h] at ih ⊢
        simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false, List.cons_append]
        exact ih.cons x

end M021

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove `partition_eq` first; `partition_perm` then starts with `rw [partition_eq]` and is a
    statement about the two filters only.
H2. Both proofs: induction on `xs`, and in the `cons` case `cases h : p x` (keep the fact `h`!).
    Part 1: in each Boolean case one `simp` with `partition`, `ih`, `List.filter_cons` and `h`.
    Part 2: rewrite with `List.filter_cons` and `h` in `ih` and the goal, clean the `if`s and `!`,
    then chain permutations.
H3. Part 2, `p x = false`: the goal is `filter p xs ++ x :: filter (!p ·) xs ~ x :: xs`:
    `exact List.perm_middle.trans (ih.cons x)`; `p x = true`: after `List.cons_append`, `exact ih.cons x`.
-/
