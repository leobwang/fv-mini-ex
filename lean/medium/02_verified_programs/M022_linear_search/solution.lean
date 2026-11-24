/- M022 | Linear search | 15 min | Option, xs[i]?, induction generalizing [R04]
GOAL
  Implement `search k xs`: the index of the first occurrence of `k` in `xs`, or `none`.
  Prove the result is correct, is the first occurrence, and that `none` means `k ∉ xs`.

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M022

/- SKELETON · search
  1. Recurse on the list:                                                   R1
       `[]`      → `k` does not occur: `none`
       `x :: xs` → branch on `x = k`:                                       R2
                     hit:  the first index is `0`
                     miss: the tail's answer, every index shifted by one    R3
-/
-- BEGIN SPEC
def search (k : Nat) (xs : List Nat) : Option Nat :=
-- END SPEC
  match xs with
  | [] => none
  | x :: xs => if x = k then some 0 else (search k xs).map (· + 1)

/- SKELETON · search_some
  1. Induct on `xs` generalizing `i` (the tail's answer is a different
     index `i'`, and `ih` must apply to it):                                R4
  2. `nil`: unfold `search` in `h`; it becomes `none = some i`:             R6 → R5
  3. `cons x xs ih`: unfold `h` one step, split its `if`:                   R6, R7
       `isTrue` (`x = k`): `h : some 0 = some i` → `0 = i`; substitute;
                           finish from the hypotheses:                      R8 → R9 → R11 (uses R10)
       `isFalse` (`¬x = k`): split on the tail call, recorded as `hs`:      R12
         `none`:     rewrite `h` with `hs`; it becomes `none = some i`:     R13
         `some i'`:  rewrite `h` with `hs` → `i' + 1 = i`; substitute:      R14 → R9
                     the IH at `i'` and `hs` → `h1`, `h2`:                  R15
                     first conjunct from `h1`:                              R16 + R18 (uses R17)
                     second: `intro j hj`, split `j`:                       R19
                       `zero`:   finish from the hypotheses                 R11 (uses R10)
                       `succ j`: from `h2 j` with `j < i'` by arithmetic    R18 (uses R17), R20
-/
-- BEGIN SPEC
theorem search_some (k : Nat) (xs : List Nat) (i : Nat) (h : search k xs = some i) :
    xs[i]? = some k ∧ ∀ j < i, xs[j]? ≠ some k :=
-- END SPEC
  by
    induction xs generalizing i with
    | nil => simp [search] at h
    | cons x xs ih =>
      simp only [search] at h
      split at h
      · simp at h
        subst h
        simp_all
      · cases hs : search k xs with
        | none => simp [hs] at h
        | some i' =>
          simp [hs] at h
          subst h
          obtain ⟨h1, h2⟩ := ih i' hs
          refine ⟨by simpa using h1, ?_⟩
          intro j hj
          cases j with
          | zero => simp_all
          | succ j => simpa using h2 j (by omega)

/- SKELETON · search_none
  1. Induct on `xs` (no index to generalize):                               R4 without `generalizing`
  2. `nil`: `k ∉ []`:                                                       R21
  3. `cons x xs ih`: unfold `h` one step, split its `if`:                   R6, R7
       `isTrue`:  `h : some 0 = none`:                                      R5
       `isFalse`: `h` → `search k xs = none` (the premise of `ih`):         R22
                  goal `k ∉ x :: xs` → `¬k = x ∧ ¬k ∈ xs`:                  R23, R24
                  close it: left from `h✝ : ¬x = k`, right is `ih h`:       R25 (left part: R11)
-/
-- BEGIN SPEC
theorem search_none (k : Nat) (xs : List Nat) (h : search k xs = none) : k ∉ xs :=
-- END SPEC
  by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [search] at h
      split at h
      · simp at h
      · simp at h
        simp only [List.mem_cons, not_or]
        exact ⟨fun hk => by simp_all, ih h⟩

end M022

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `search` by recursion on the list; on a miss, shift the tail's answer by one with
    `Option.map` (R1–R3). In both proofs, induct on `xs`, and in the `cons` case start by unfolding `h`
    one step and splitting its `if` (`simp only [search] at h; split at h`, R6, R7).
H2. `search_some`: induct generalizing `i` (R4). In the `isFalse` branch split on the tail call with
    `cases hs : search k xs` (R12) and rewrite `h` with `simp [hs] at h` (R13, R14); then use `ih` at the
    tail's index and prove `∀ j < i' + 1, …` by `cases j` (R19). `search_none`: plain induction; in
    `isFalse`, `simp at h` gives `search k xs = none` (R22); turn the goal into `¬k = x ∧ ¬k ∈ xs` (R23, R24).
H3. Implementation: `match xs with | [] => none | x :: xs => if x = k then some 0 else (search k xs).map (· + 1)`.
    `search_some`, case `some i'`: `simp [hs] at h; subst h; obtain ⟨h1, h2⟩ := ih i' hs`, then
    `refine ⟨by simpa using h1, ?_⟩`, `intro j hj; cases j`, and `simpa using h2 j (by omega)` for `succ`.
    `search_none`, `isFalse`: `simp only [List.mem_cons, not_or]; exact ⟨fun hk => by simp_all, ih h⟩`.
-/
