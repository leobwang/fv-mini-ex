/- M032 | Palindrome | 10-15 min | Bool check, getElem?, List.ext_getElem? [R17]
GOAL
  Implement `isPal`, and prove it returns `true` exactly when element `i` equals element
  `n - 1 - i` for every index `i < n`.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M032

/- SKELETON · isPal
  1. Compare the list with its reverse, as a `Bool`:                       R1, R2
-/
-- BEGIN SPEC
def isPal (xs : List Nat) : Bool :=
-- END SPEC
  sorry

/- SKELETON · isPal_iff
  1. Unfold `isPal` and turn `(_ == _) = true` into `=`, in one
     `simp only`; the left side becomes `xs = xs.reverse`:                  R3, R4 (W1)
  2. Split the `↔`:                                                         R5
  3. `mp`: take the equation `h`, the index `i` and its bound `hi`:         R6
       rewrite only the FIRST `xs` with `h` (a plain `rw [h]` also hits
       the `xs` in `xs.length` and on the right):                           R7
       the goal is now the reverse-indexing lemma at `hi`:                  R8
  4. `mpr`: take the pointwise hypothesis `h`:                              R6
       list equality → equality at every index (no bound!); `intro i`:     R9
       split on `i < xs.length`:                                            R10
       in range:     rewrite with `h` at `i`, then reverse-indexing:        R11, R8
       out of range: both sides are `none`; one rewrite per side, each
                     with its own side proof (the second is about
                     `xs.reverse.length`):                                  R13 (R12), R13 (R14 → R12)
                     (W2, W3)
-/
-- BEGIN SPEC
theorem isPal_iff (xs : List Nat) :
    isPal xs = true ↔ ∀ i < xs.length, xs[i]? = xs[xs.length - 1 - i]? :=
-- END SPEC
  sorry

end M032

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A list is a palindrome iff it equals its reverse; the index statement is that equation read
    pointwise, with `List.getElem?_reverse` (R8) as the bridge.
H2. `isPal xs := xs == xs.reverse`. Start with `simp only [isPal, beq_iff_eq]; constructor`.
    → : rewrite only the left `xs` into `xs.reverse` (`conv => lhs; rw [h]`), then R8.
    ← : `apply List.ext_getElem?; intro i`, then `by_cases hi : i < xs.length`.
H3. ← in range: `rw [h i hi, List.getElem?_reverse hi]`; out of range:
    `rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]`.
-/
