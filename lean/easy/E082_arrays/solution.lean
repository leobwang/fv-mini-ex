/- E082 | Arrays | 2-3 min | Array, #[..], push, size, getElem?, unfold, if_neg
GOAL
  Implement `pushTwice a x` (append `x` twice to the array `a`) and prove its size, its list view,
  and that every old index still holds its old element.
BANNED: grind, try?, exact?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E082

/- SKELETON · pushTwice
  1. Append `x` to `a`, then append `x` to that result:                        R1
-/
-- BEGIN SPEC
def pushTwice (a : Array Nat) (x : Nat) : Array Nat :=
-- END SPEC
  (a.push x).push x

/- SKELETON · lit_size
  1. A literal array: Lean counts its entries.                                  R2
-/
-- BEGIN SPEC
theorem lit_size : #[1, 2, 3].size = 3 :=
-- END SPEC
  rfl

/- SKELETON · pushTwice_size
  1. Unfold `pushTwice` and simplify in one call; `simp` rewrites each push's
     size and closes `a.size + 1 + 1 = a.size + 2`:                            R3 (uses R4)
-/
-- BEGIN SPEC
theorem pushTwice_size (a : Array Nat) (x : Nat) : (pushTwice a x).size = a.size + 2 :=
-- END SPEC
  by simp [pushTwice]

/- SKELETON · pushTwice_toList
  1. Unfold and simplify in one call; `simp` turns each push into `++ [x]`
     and merges `a.toList ++ [x] ++ [x]` into `a.toList ++ [x, x]`:            R3 (uses R5, R6)
-/
-- BEGIN SPEC
theorem pushTwice_toList (a : Array Nat) (x : Nat) : (pushTwice a x).toList = a.toList ++ [x, x] :=
-- END SPEC
  by simp [pushTwice]

/- SKELETON · pushTwice_old
  1. Expose the two pushes `(a.push x).push x`:                                 R7
  2. Outer push: rewrite its `[i]?` into an `if`, take the `else` branch;
     the condition `¬i = (a.push x).size` needs the size rewritten first:      R8, R9 with R10
  3. Inner push: the same, condition `¬i = a.size` (omega alone):              R8, R9
  4. What is left is `a[i]? = some a[i]`; the bound is `h`:                    R11
-/
-- BEGIN SPEC
theorem pushTwice_old (a : Array Nat) (x i : Nat) (h : i < a.size) :
    (pushTwice a x)[i]? = some a[i] :=
-- END SPEC
  by
  unfold pushTwice
  -- WHY: the outer `push` sees an array of size `a.size + 1`, so its `if` needs `simp` before `omega`
  rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]
  exact Array.getElem?_eq_getElem h

end E082

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `pushTwice` is two `push`es (R1); a literal's size is computed by `rfl` (R2). For size and list view,
    `simp` knows the `push` lemmas once it can see through `pushTwice` (R3–R6).
H2. Size and list view: `simp [pushTwice]`. Old index: `unfold pushTwice` (R7), then twice
    `rw [Array.getElem?_push]` + `if_neg` (R8, R9): `i < a.size`, so neither `if` condition holds. The outer
    condition talks about `(a.push x).size`: simplify it before `omega` (R10). Finish with R11.
H3. `rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]`,
    then `exact Array.getElem?_eq_getElem h`.
-/
