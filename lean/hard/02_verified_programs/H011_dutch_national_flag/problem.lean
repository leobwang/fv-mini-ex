/- H011 | Dutch national flag | 1-1.5 h | Array, swap, loop invariant, fun_induction [R19]
GOAL
  Dijkstra's one-pass three-way partition sorts an array of colours by swapping. Prove the
  result is a permutation of the input and is sorted by colour (all reds, then whites, then blues).

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H011

-- BEGIN SPEC
inductive Color where
  | red
  | white
  | blue
  deriving DecidableEq

def rank : Color → Nat
  | .red => 0
  | .white => 1
  | .blue => 2

def dnfLoop (a : Array Color) (lo mid hi : Nat) : Array Color :=
  if h : lo ≤ mid ∧ mid < hi ∧ hi ≤ a.size then
    match a[mid] with
    | .red => dnfLoop (a.swap lo mid) (lo + 1) (mid + 1) hi
    | .white => dnfLoop a lo (mid + 1) hi
    | .blue => dnfLoop (a.swap mid (hi - 1)) lo mid (hi - 1)
  else a
termination_by hi - mid

def dnf (a : Array Color) : Array Color := dnfLoop a 0 0 a.size

def SortedByColor (a : Array Color) : Prop :=
  ∀ i j (hij : i ≤ j) (hj : j < a.size), rank a[i] ≤ rank a[j]
-- END SPEC

-- MILESTONE (optional: change or delete)
def FlagInv (a : Array Color) (lo mid hi : Nat) : Prop :=
  lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ a.size ∧
  (∀ i (h : i < a.size), i < lo → a[i] = .red) ∧
  (∀ i (h : i < a.size), lo ≤ i → i < mid → a[i] = .white) ∧
  (∀ i (h : i < a.size), hi ≤ i → a[i] = .blue)

/- SKELETON · loop_perm   (milestone: prove it first, for ALL lo mid hi; dnf_perm uses it)
  1. Induction following dnfLoop's recursion: cases red / white / blue / exit          R1
  2. red and blue branches (a swap, then the loop): IH chained with "a swap permutes"  R3, R2
  3. white branch: the IH is already the goal                                          exact
  4. exit: the array is returned unchanged                                             R4
-/
-- MILESTONE (optional: change or delete)
theorem loop_perm (a : Array Color) (lo mid hi : Nat) : (dnfLoop a lo mid hi).Perm a := by
  sorry

/- SKELETON · loop_sorted   (milestone: prove it before dnf_sorted, for ALL lo mid hi)
  FlagInv: [0, lo) red, [lo, mid) white, [mid, hi) unread, [hi, size) blue, plus the bounds.
  0. Start the induction with `hinv` still in the context, so each IH is
       FlagInv (next a) (next lo) (next mid) (next hi) → SortedByColor (dnfLoop …)  R1, R6
  Red, white and blue branches:
  1. split `hinv` into its six parts                                                 R7
  2. reduce the goal to the invariant at the next state                              R8
  3. three bound parts inline, three region parts left as goals                      R9, R10, R11
     (white branch: the red and blue regions are unchanged, pass the old facts)
  4. each region part after a swap:
       index, its bound, the region premises into the context                       R12
       the swapped cell → nested `if`; case on which cell it is                     R13, R14, R14
       the cell swapped in: `hc`, or the old region fact at `lo` / an impossible
         index combination                                                          R10
       an untouched cell: the old region fact, bound transferred to `a`             R15
       blue branch, cell `hi - 1` when `hi - 1 = mid`: change the index first       R10, R18
  5. white branch, white region: is `i` the newly added cell `mid`?                  R16, R17
  Exit branch:
  6. split `hinv`; the negated guard plus the bounds give `mid = hi`                 R7, R10, R17
  7. take i ≤ j < size; case on the region of `i` (red / white / blue), for a white
     `i` also on the region of `j`                                                   R12, R16
  8. rewrite both cells to their colours, then compare ranks                         R19, R20 or R21
-/
-- MILESTONE (optional: change or delete)
theorem loop_sorted (a : Array Color) (lo mid hi : Nat) (hinv : FlagInv a lo mid hi) :
    SortedByColor (dnfLoop a lo mid hi) := by
  sorry

/- SKELETON · dnf_perm
  1. `dnf a` unfolds to `dnfLoop a 0 0 a.size` (R5, not needed before `exact`):
     the milestone `loop_perm` at lo = mid = 0, hi = a.size
-/
-- BEGIN SPEC
theorem dnf_perm (a : Array Color) : (dnf a).Perm a :=
-- END SPEC
  sorry

/- SKELETON · dnf_sorted
  1. The milestone `loop_sorted` at lo = mid = 0, hi = a.size                         R5
  2. Its premise `FlagInv a 0 0 a.size` as one anonymous constructor ⟨…⟩ of 6 parts:
       the three bounds                                                               R10
       the three regions are empty, so each premise `i < 0`, `i < 0`, `a.size ≤ i`
       contradicts a bound                                                            R22, R10
-/
-- BEGIN SPEC
theorem dnf_sorted (a : Array Color) : SortedByColor (dnf a) :=
-- END SPEC
  sorry

end H011

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the two milestones for arbitrary `lo mid hi` by `fun_induction dnfLoop a lo mid hi`; the spec
    theorems are their instances at `0 0 a.size`. Permutation: each branch is a swap or nothing.
    Sortedness: keep `hinv : FlagInv a lo mid hi` in the context, so the IH asks for the invariant at the
    next state.
H2. Each loop branch: `obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv; apply ih`, then
    `refine ⟨by omega, by omega, by simp; omega, ?_, ?_, ?_⟩` (white branch: pass `h3`, `hr`, `hb`). Each
    region: `intro i hk …; rw [Array.getElem_swap]; split` and `split` again; `omega` kills impossible
    index cases, `by simpa using hk` moves a bound back to `a`. Exit: `mid = hi` by `omega`, `subst`, then
    `by_cases` on the region of `i` (and of `j`).
H3. Red branch: the new red cell `lo` holds the old `a[mid]` (`hc`); the new white cell `mid` holds the old
    `a[lo]`, white by `hw lo` because `lo < mid` there. Blue branch: the new blue cell `hi - 1` holds the
    old `a[mid]` (`hc`); when the cell is `mid = hi - 1`, `have e : hi - 1 = mid := by omega; simp only [e]`
    then `exact hc`. White branch: `by_cases him : i = mid; subst him; exact hc`. `dnf_sorted`:
    `loop_sorted a 0 0 a.size ⟨by omega, by omega, by omega, fun i _ h => absurd h (by omega), …⟩`.
-/
