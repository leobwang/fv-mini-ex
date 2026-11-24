/- M015 | Sum by accumulator | 10 min | accumulator, induction generalizing, loop invariant [R03]
GOAL
  `sumLoop n` adds 1..n with a tail-recursive accumulator (a loop). Prove the closed form
  `2 * sumLoop n = n * (n + 1)`.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def sumAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

def sumLoop (n : Nat) : Nat := sumAcc n 0
-- END SPEC

/- SKELETON · sumLoop_spec
  0. MILESTONE first, as your own theorem above this one (outside the spec), the loop invariant
     for EVERY accumulator:
       theorem sumAcc_eq (n acc : Nat) : 2 * sumAcc n acc = 2 * acc + n * (n + 1)
     a. Induction on `n`, generalizing the accumulator:                       R1
     b. zero:  unfold `sumAcc 0 acc`, clean up `0 * (0 + 1)`:                 R2
     c. succ n ih:  in one `simp only`, unfold one loop step (new accumulator
        `acc + (n + 1)`), use `ih` at that accumulator, expand every product:  R3 → R4 → R5, R6
        left over: linear in `acc`, `n` and the atom `n * n`:                 R7
  1. `sumLoop_spec`:  unfold `sumLoop`, rewrite with the milestone at
     `acc = 0`, clean up `2 * 0 + …` (one `simp` with both names):            R8 → R9 → R10
-/
-- BEGIN SPEC
theorem sumLoop_spec (n : Nat) : 2 * sumLoop n = n * (n + 1) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction straight on `sumLoop n` gets stuck: the recursive call has accumulator `0 + (n + 1)`,
    not `0`. What is `2 * sumAcc n acc` for ANY `acc`? Prove that first.
H2. Milestone `sumAcc_eq`, by `induction n generalizing acc`: `zero` is `simp [sumAcc]`; in `succ`,
    unfold, use `ih`, and expand products with `Nat.mul_add`, `Nat.add_mul` so `omega` sees `n * n`
    as an atom. Then `sumLoop_spec` is the case `acc = 0`.
H3. `theorem sumAcc_eq (n acc : Nat) : 2 * sumAcc n acc = 2 * acc + n * (n + 1)`; its `succ` case is
    `simp only [sumAcc, ih, Nat.mul_add, Nat.add_mul]; omega`. Then `simp [sumLoop, sumAcc_eq]`.
-/
