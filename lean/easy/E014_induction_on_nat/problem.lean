/- E014 | Induction on Nat | 3 min | induction, Nat
GOAL
  Prove closed forms for two recursive functions by induction on `n`.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2

def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)
-- END SPEC

/- SKELETON · dbl_eq
  1. Induct on `n`, the argument `dbl` recurses on:                         R1
  2. Case `zero`: `dbl 0` and `2 * 0` both compute to `0`:                  R2
  3. Case `succ`: one `simp only` with `dbl` and `ih`:
       unfold `dbl (n + 1)` to `dbl n + 2`                                  R3
       replace `dbl n` by `2 * n`                                           R4
       left over: `2 * n + 2 = 2 * (n + 1)`, linear                         R7
-/
-- BEGIN SPEC
theorem dbl_eq (n : Nat) : dbl n = 2 * n :=
-- END SPEC
  sorry

/- SKELETON · sumOdd_eq
  1. Induct on `n`:                                                         R1
  2. Case `zero`: both sides compute to `0`:                                R2
  3. Case `succ`: one `simp only` that unfolds, uses `ih` and expands
     the product `(n + 1) * (n + 1)` on the right:                          R3, R4, R5, R6
       left over: linear in `n` and the single atom `n * n`
  4. Finish the arithmetic:                                                 R7
-/
-- BEGIN SPEC
theorem sumOdd_eq (n : Nat) : sumOdd n = n * n :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both functions recurse on `n`, so induct on `n` (R1). In the `succ` case, unfold one step of the
    definition (R3) so that `ih` applies (R4).
H2. `dbl_eq`: after unfolding and `ih` the rest is linear, so `omega` (R7) finishes. `sumOdd_eq`: `omega`
    cannot multiply variables; it treats `n * n` and `(n + 1) * (n + 1)` as two unrelated atoms. Expand
    the product first with `Nat.add_mul` and `Nat.mul_add` (R5, R6).
H3. Case `zero`: `rfl`. Case `succ`: `simp only [dbl, ih]` then `omega`; for `sumOdd_eq`,
    `simp only [sumOdd, ih, Nat.add_mul, Nat.mul_add]` then `omega`.
-/
