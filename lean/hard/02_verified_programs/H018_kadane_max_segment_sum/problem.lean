/- H018 | Kadane's maximum segment sum | 1-1.5 h | foldl invariant, List.IsInfix, List.IsSuffix, optimality spec, max
GOAL
  Kadane's one-pass algorithm returns the maximum sum over all contiguous segments of `xs` (the
  empty segment counts): it bounds the sum of every segment, and some segment attains it.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H018

-- BEGIN SPEC
/-- One step of Kadane's algorithm. State `(best, cur)`: `best` is the best segment sum seen so
    far, `cur` the best sum of a suffix of the prefix read so far (both ≥ 0: `[]` counts). -/
def kadaneStep (st : Int × Int) (x : Int) : Int × Int :=
  let cur := max 0 (st.2 + x)
  (max st.1 cur, cur)

def kadane (xs : List Int) : Int := (xs.foldl kadaneStep (0, 0)).1
-- END SPEC

/- SKELETON · the MILESTONES (prove these FIRST, in this order)
  `Inv` is given (keep it). inv_step is used in inv_foldl's `cons` case; inv_nil and inv_foldl
  are used in both main theorems, to get the invariant at the end of the loop.
  inv_nil:
    1. split into the two bounds, with `[]` as the witness of both `∃`               R1, R2
    2. each bound: `intro ys h`; `ys` is a segment / suffix of `[]`, so it is `[]`    R3, R4
       what is left, `0 ≤ (0, 0).fst`, closes by `omega` or `simp`                   R10
  inv_step:
    1. take `h` apart into its four parts                                            R5
    2. suffix bound FIRST:
         hsuf : ∀ ys, ys <:+ p ++ [x] → ys.sum ≤ max 0 (st.2 + x)
       `intro`, then case on the suffix                                              R6, R7
         `[]`  → sum 0                                                              R4, R10
         `t ++ [x]` → the old suffix bound at `t` (a `have`), then the sums          R8, R9, R10
    3. suffix attainment:
         hatt : ∃ ys, ys <:+ p ++ [x] ∧ ys.sum = max 0 (st.2 + x)
       case on `st.2 + x ≤ 0`                                                        R11
         yes → witness `[]`                                                          R2, R4, R10
         no  → witness: the old attaining suffix `++ [x]`                           R12, R8, R9, R10
    4. assemble the four parts with `refine`, hsuf and hatt in slots 2 and 4         R1, R22
    5. segment bound: `intro`, unfold the step, case on the segment                  R13, R14
         a suffix of `p ++ [x]` → hsuf;  a segment of `p` → the old bound;  then     R10
    6. segment attainment: unfold the step, case on `max 0 (st.2 + x) ≤ st.1`        R13, R11
         yes → the old attaining segment, made a segment of `p ++ [x]`               R14, R10
         no  → take hatt apart, its suffix made a segment                            R5, R15, R10
  inv_foldl:
    1. induction on `l`, generalizing `p` and `st`                                   R16
    2. nil: `h`, up to `p ++ []` and `List.foldl … []`                               R20 (R17, R18)
    3. cons: `ih` at the prefix `p ++ [x]`, fed with inv_step                        R20 (R17, R19)
-/
-- MILESTONE (optional: change or delete)
-- The loop invariant after reading the prefix `p`: `st.1` is the maximum segment sum of `p`
-- and `st.2` the maximum suffix sum of `p` (each an upper bound that is attained).
def Inv (p : List Int) (st : Int × Int) : Prop :=
  (∀ ys, ys <:+: p → ys.sum ≤ st.1) ∧ (∀ ys, ys <:+ p → ys.sum ≤ st.2) ∧
  (∃ ys, ys <:+: p ∧ ys.sum = st.1) ∧ (∃ ys, ys <:+ p ∧ ys.sum = st.2)

-- MILESTONE (optional: change or delete)
theorem inv_nil : Inv [] (0, 0) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem inv_step (p : List Int) (st : Int × Int) (x : Int) (h : Inv p st) :
    Inv (p ++ [x]) (kadaneStep st x) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem inv_foldl (l p : List Int) (st : Int × Int) (h : Inv p st) :
    Inv (p ++ l) (l.foldl kadaneStep st) := by
  sorry

/- SKELETON · kadane_upper  (uses inv_nil, inv_foldl)
  1. The invariant at the end of the loop, from inv_foldl with `p := []`:
       hI : Inv xs (xs.foldl kadaneStep (0, 0))                                      R20 (R18)
  2. The first part of hI, applied to `ys` and `h`                                   R21
     (`kadane xs` is `(xs.foldl kadaneStep (0, 0)).1` by definition)                 R22
-/
-- BEGIN SPEC
theorem kadane_upper (xs ys : List Int) (h : ys <:+: xs) : ys.sum ≤ kadane xs :=
-- END SPEC
  sorry

/- SKELETON · kadane_attained  (uses inv_nil, inv_foldl)
  1. The same `hI` as in kadane_upper                                                R20 (R18)
  2. The third part of hI                                                            R21, R22
-/
-- BEGIN SPEC
theorem kadane_attained (xs : List Int) : ∃ ys, ys <:+: xs ∧ ys.sum = kadane xs :=
-- END SPEC
  sorry

end H018

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems are parts of one loop invariant `Inv` about `xs.foldl kadaneStep (0, 0)`. Reading the
    input left to right, the new suffixes of `p ++ [x]` are `[]` and `t ++ [x]` for old suffixes `t`
    (`List.suffix_concat_iff`), and a segment of `p ++ [x]` is a suffix of it or a segment of `p`
    (`List.infix_concat_iff`).
H2. `inv_step`: first prove the suffix half about `max 0 (st.2 + x)` (bound by cases on the suffix,
    attainment by cases on `st.2 + x ≤ 0`), then the segment half: `simp only [kadaneStep]`, cases on
    the segment, and for attainment cases on `max 0 (st.2 + x) ≤ st.1`; `omega` closes the arithmetic.
    `inv_foldl`: `induction l generalizing p st`, since the prefix read so far and the state both change.
H3. Suffix cases: `rcases List.suffix_concat_iff.mp hys with rfl | ⟨t, rfl, ht⟩`; the attaining suffix
    is `⟨yc ++ [x], List.suffix_concat_iff.mpr (.inr ⟨yc, rfl, hyc⟩), _⟩`. Cons case of `inv_foldl`:
    `simpa using ih (p ++ [x]) _ (inv_step p st x h)`. Main theorems:
    `have hI : Inv xs (xs.foldl kadaneStep (0, 0)) := by simpa using inv_foldl xs [] (0, 0) inv_nil`,
    then `hI.1 ys h` and `hI.2.2.1`.
-/
