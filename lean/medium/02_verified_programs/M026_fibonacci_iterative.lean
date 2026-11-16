/- M026 | Fibonacci, iterative | 10-15 min | accumulator pair, induction generalizing [R10]
GOAL
  `fibIter` computes Fibonacci numbers in linear time with two accumulators. Prove it equals the
  exponential-time recursive definition `fib`.

REFERENCE
  example (k : Nat) : M026.fib (k + 2) = M026.fib k + M026.fib (k + 1) := rfl   -- by definition
  example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by rw [h]
  example (k n : Nat) : k + 1 + n = k + (n + 1) := by omega
  -- Which invariant links the accumulators `a b` to `fib`? Try `a = fib k`, `b = fib (k + 1)`.
  `congrArg f h : f a = f b` from `h : a = b`; in tactics, `congr 1` reduces `f a = f b` to `a = b`.
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

-- BEGIN SPEC
theorem fibIter_eq (n : Nat) : fibIter n = fib n :=
-- END SPEC
  sorry

end M026

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. After `k` steps from `(0, 1)` the accumulators are `(fib k, fib (k + 1))`.
H2. Prove `fibAux n (fib k) (fib (k + 1)) = fib (k + n)` for all `k`, by induction on `n` generalising `k`.
H3. Succ case: rewrite `fib k + fib (k + 1)` to `fib (k + 1 + 1)` (true by `rfl`), apply `ih (k + 1)`, then `congr 1; omega`.
-/
