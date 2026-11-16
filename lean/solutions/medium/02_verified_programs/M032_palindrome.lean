/- M032 | Palindrome | 10-15 min | Bool check, getElem?, List.ext_getElem? [R17]
GOAL
  Implement `isPal`, and prove it returns `true` exactly when element `i` equals element
  `n - 1 - i` for every index `i < n`.

REFERENCE
  example (xs ys : List Nat) : (xs == ys) = true ↔ xs = ys := beq_iff_eq   -- `==` on lists
  #check List.getElem?_reverse   -- i < l.length → l.reverse[i]? = l[l.length - 1 - i]?
  #check List.ext_getElem?       -- (∀ i, l₁[i]? = l₂[i]?) → l₁ = l₂
  #check List.getElem?_eq_none   -- l.length ≤ i → l[i]? = none
  -- `conv => lhs; rw [h]` rewrites only the left-hand side of the goal.
-/

namespace M032

-- BEGIN SPEC
def isPal (xs : List Nat) : Bool :=
-- END SPEC
  xs == xs.reverse

-- BEGIN SPEC
theorem isPal_iff (xs : List Nat) :
    isPal xs = true ↔ ∀ i < xs.length, xs[i]? = xs[xs.length - 1 - i]? :=
-- END SPEC
  by
    simp only [isPal, beq_iff_eq]
    constructor
    · intro h i hi
      conv => lhs; rw [h]
      exact List.getElem?_reverse hi
    · intro h
      apply List.ext_getElem?
      intro i
      by_cases hi : i < xs.length
      · rw [h i hi, List.getElem?_reverse hi]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end M032

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A list is a palindrome iff it equals its reverse; the index statement is that equation read pointwise.
H2. `isPal xs := xs == xs.reverse`. → : rewrite one `xs` into `xs.reverse` and use `getElem?_reverse`. ← : `List.ext_getElem?`, splitting on `i < xs.length`.
H3. ← in range: `rw [h i hi, List.getElem?_reverse hi]`; out of range: both sides are `none` by `List.getElem?_eq_none`.
-/
