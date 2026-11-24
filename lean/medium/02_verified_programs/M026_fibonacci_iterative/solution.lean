/- M026 | Fibonacci, iterative | 10-15 min | accumulator pair, induction generalizing [R10]
GOAL
  `fibIter` computes Fibonacci numbers in linear time with two accumulators. Prove it equals the
  exponential-time recursive definition `fib`.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M026

-- BEGIN SPEC
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fibAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fibAux n b (a + b)

def fibIter (n : Nat) : Nat := fibAux n 0 1
-- END SPEC

theorem fibAux_eq (n k : Nat) : fibAux n (fib k) (fib (k + 1)) = fib (k + n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    have h : fib k + fib (k + 1) = fib (k + 1 + 1) := rfl
    simp only [fibAux, h, ih (k + 1)]
    congr 1
    omega

/- SKELETON · fibIter_eq   (prove the MILESTONE helper first, above this theorem)
  Why a helper: `fibIter (n + 1) = fibAux n 1 1` restarts from the pair `(1, 1)`, not `(0, 1)`, so
  induction on this statement gets stuck. Generalise the start of the accumulator pair.
  1. MILESTONE `fibAux_eq (n k : Nat)`: an equation saying what `fibAux n` returns when started from
     the pair `(fib k, fib (k + 1))`, for EVERY start index `k`. Its proof:
       induction on `n`, generalizing `k`                                       R1
       zero: both sides compute to the same term                               R2
       succ n ih:
         the unfolding fact  h : fib k + fib (k + 1) = fib (k + 1 + 1)         R3
         one accumulator step `fibAux (n + 1) a b`                             R4
         fold the sum                                                          rw [h]
         use `ih` at the next index `k + 1`                                    R5
         strip `fib` from both sides, then arithmetic on the indices           R6 → R7
  2. fibIter_eq, using the milestone at `k := 0`:
       instantiate it as a hypothesis                                          R8
       turn `0 + _` into `_` in it                                             R9
       close: the goal is that hypothesis up to unfolding `fibIter`,
       `fib 0`, `fib 1`                                                        R10
-/
-- BEGIN SPEC
theorem fibIter_eq (n : Nat) : fibIter n = fib n :=
-- END SPEC
  by
    have h := fibAux_eq n 0
    simp only [Nat.zero_add] at h
    exact h

end M026

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `fibIter_eq` is not inductive as stated: one step from `(0, 1)` gives `(1, 1)`. After `k` steps the
    accumulators are `(fib k, fib (k + 1))`; say what `fibAux n` returns from THAT pair, for every `k`,
    in a helper lemma above the theorem (SKELETON step 1).
H2. Helper: `fibAux n (fib k) (fib (k + 1)) = fib (k + n)`, by `induction n generalizing k` (R1); the zero
    case is `rfl` (R2). The theorem is the helper at `k := 0`: `have h := fibAux_eq n 0`, then
    `simp only [Nat.zero_add] at h` and `exact h` (R8–R10).
H3. Succ case: `have h : fib k + fib (k + 1) = fib (k + 1 + 1) := rfl`, then
    `simp only [fibAux]; rw [h, ih (k + 1)]` (or all in one `simp only [fibAux, h, ih (k + 1)]`),
    then `congr 1; omega`.
-/
