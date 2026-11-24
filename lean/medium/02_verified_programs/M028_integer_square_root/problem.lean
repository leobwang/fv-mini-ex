/- M028 | Integer square root | 10-15 min | recursion, nonlinear facts via omega atoms [R12]
GOAL
  Implement `isqrt n`, the largest `r` with `r * r ≤ n`, and prove `r² ≤ n < (r+1)²`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M028

/- SKELETON · isqrt
  1. Recurse on `n`:                                                          R1
       `0`     → the root is `0`
       `n + 1` → name the root of the predecessor `r` (a recursive call)       R2
                 the root of `n + 1` is `r + 1` if `(r + 1) * (r + 1)` still
                 fits under `n + 1`, else `r`                                  R3
-/
-- BEGIN SPEC
def isqrt (n : Nat) : Nat :=
-- END SPEC
  sorry

/- SKELETON · isqrt_spec
  1. Induct on `n`:                                                           R4
  2. `zero`: unfold `isqrt 0` and close                                       R5
  3. `succ n ih`: unfold one step; the `let` is substituted, so the goal
     mentions `isqrt n` and four copies of the `if`:                           R6
  4. Case on the `if`, then name the condition `h` in each branch:            R7, R8
       then-branch (`h : (isqrt n + 1) * (isqrt n + 1) ≤ n + 1`):
         the first conjunct IS `h`                                             R9
         expand every product of sums in `ih`, `h` and the goal                R12 (R10, R11)
         linear arithmetic, `isqrt n * isqrt n` as an atom                     R13
       else-branch (`h : ¬…`): the same expansion, then arithmetic            R12, R13
-/
-- BEGIN SPEC
theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
-- END SPEC
  sorry

end M028

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recursion on `n`: from `r = isqrt n`, the root of `n + 1` is `r` or `r + 1` (R1–R3). Prove the
    spec by induction on `n` (R4), following the definition's two cases.
H2. Definition step: `let r := isqrt n` then `if (r + 1) * (r + 1) ≤ n + 1 then r + 1 else r`.
    Proof step: `simp only [isqrt]` (R6), `split` (R7), `rename_i h` (R8) in each branch. `omega`
    alone fails: `(isqrt n + 1) * (isqrt n + 1)` and `isqrt n * isqrt n` are unrelated atoms to it.
H3. In each branch: `simp only [Nat.add_mul, Nat.mul_add] at ih h ⊢; omega` (R12, R13); in the
    `then` branch first `refine ⟨h, ?_⟩` (R9). Base case: `simp [isqrt]` (R5).
-/
