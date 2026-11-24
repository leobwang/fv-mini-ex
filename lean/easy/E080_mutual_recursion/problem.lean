/- E080 | Mutual recursion | 3 min | mutual, Bool, recursive theorem
GOAL
  `isEven` and `isOdd` are defined by mutual recursion (each calls the other). Prove that they are
  complementary, that `isEven` agrees with `n % 2 == 0`, and that `2 * n + 1` is odd.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E080

-- BEGIN SPEC
mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end
-- END SPEC

/- SKELETON · isEven_not_odd
  1. Induction on `n`:                                                      R1
  2. Case `zero`: `isEven 0 = !isOdd 0` is a closed computation:            R2
  3. Case `succ k ih`: unfold both functions one step,                      R3
       ⊢ isOdd k = !isEven k
     rewrite `isEven k` with `ih`, then drop the double negation:           rw [ih], R4
     (one `simp` with the two function names and `ih` does step 3)
-/
-- BEGIN SPEC
theorem isEven_not_odd (n : Nat) : isEven n = !isOdd n :=
-- END SPEC
  sorry

/- SKELETON · isEven_mod
  1. Split `n` into `0`, `1`, `n + 2` (term-mode `match` after `:=`):       R5
  2. Cases `0` and `1`: closed computations:                                R2
  3. Case `n + 2`: unfold `isEven`, then `isOdd`, back to `isEven n`:       R6, R6
       ⊢ isEven n = ((n + 2) % 2 == 0)
     recursive call at the smaller `n`:                                     R7
       ⊢ (n % 2 == 0) = ((n + 2) % 2 == 0)
     drop the `+ 2` under `% 2`; both sides are then equal:                 R8
-/
-- BEGIN SPEC
theorem isEven_mod (n : Nat) : isEven n = (n % 2 == 0) :=
-- END SPEC
  sorry

/- SKELETON · isOdd_double_add_one
  1. `2 * n + 1` has the shape `_ + 1`: unfold `isOdd` once:                R3
       ⊢ isEven (2 * n) = true
  2. `isEven (2 * n)` does not unfold; rewrite with `isEven_mod`:           rw [isEven_mod]
  3. `2 * n % 2` → `0`, then `(0 == 0)` → `true`:                           R9, R10
     (one `simp` with `isOdd` and `isEven_mod` does all three steps)
-/
-- BEGIN SPEC
theorem isOdd_double_add_one (n : Nat) : isOdd (2 * n + 1) = true :=
-- END SPEC
  sorry

end E080

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfolding one step turns `isEven (k + 1)` into `isOdd k` and `isOdd (k + 1)` into `isEven k`; an
    equation applies only to an argument of the shape `0` or `_ + 1`.
H2. `isEven_not_odd`: induction on `n`, unfolding both functions in the step and using `ih`.
    `isEven_mod`: two unfoldings take `n + 2` back to `n`, so recurse with cases `0`, `1`, `n + 2` and
    call `isEven_mod n`; `Nat.add_mod_right` removes the `+ 2`. `isOdd_double_add_one`: unfold `isOdd`
    once and use `isEven_mod`.
H3. Step of `isEven_not_odd`: `simp [isEven, isOdd, ih]`. `isEven_mod`: `match n with | 0 => rfl | 1 => rfl`
    `| n + 2 => by rw [isEven, isOdd, isEven_mod n, Nat.add_mod_right]`. Last: `simp [isOdd, isEven_mod]`.
-/
