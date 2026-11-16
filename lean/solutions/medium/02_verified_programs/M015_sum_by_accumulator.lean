/- M015 | Sum by accumulator | 10 min | accumulator, induction generalizing, loop invariant [R03]
GOAL
  `sumLoop n` adds 1..n with a tail-recursive accumulator (a loop). Prove the closed form
  `2 * sumLoop n = n * (n + 1)`.

REFERENCE
  -- The theorem about `sumAcc n 0` is not inductive: the accumulator changes on each call.
  -- Generalise: state a lemma for every `acc` (the "loop invariant"), prove it, then specialise.
  theorem foo (n acc : Nat) : acc ≤ acc + n := by omega
  example (n : Nat) : 0 ≤ 0 + n := foo n 0          -- specialise a general lemma
  #check Nat.mul_add   -- n * (m + k) = n * m + n * k   (and Nat.add_mul)
  `induction n generalizing acc` makes the IH hold for every accumulator.
-/

-- BEGIN SPEC
def sumAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => sumAcc n (acc + (n + 1))

def sumLoop (n : Nat) : Nat := sumAcc n 0
-- END SPEC

theorem sumAcc_eq (n acc : Nat) : 2 * sumAcc n acc = 2 * acc + n * (n + 1) := by
  induction n generalizing acc with
  | zero => simp [sumAcc]
  | succ n ih =>
    simp only [sumAcc, ih, Nat.mul_add, Nat.add_mul]
    omega

-- BEGIN SPEC
theorem sumLoop_spec (n : Nat) : 2 * sumLoop n = n * (n + 1) :=
-- END SPEC
  by simp [sumLoop, sumAcc_eq]

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Find what `sumAcc n acc` equals for an arbitrary `acc`, and prove that first.
H2. Induct on `n` generalising `acc`; expand products so `omega` sees `n * n` as an atom.
H3. `theorem sumAcc_eq (n acc : Nat) : 2 * sumAcc n acc = 2 * acc + n * (n + 1)`, proved with `simp only [sumAcc, ih, Nat.mul_add, Nat.add_mul]; omega`.
-/
