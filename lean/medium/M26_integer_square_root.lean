/- M26 | Integer square root | 10-15 min | recursion, nonlinear facts via omega atoms [R12]
GOAL
  Implement `isqrt n`, the largest `r` with `r * r ≤ n`, and prove `r² ≤ n < (r+1)²`.

REFERENCE
  -- omega cannot multiply variables, but treats `r * r` as an atom. Expand products first:
  example (r n : Nat) (h : n < (r + 1) * (r + 1)) : n < r * r + 2 * r + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at h ⊢; omega
  example (n : Nat) : (match n with | 0 => 0 | k + 1 => k) ≤ n := by split <;> omega
  -- `let r := isqrt n` inside a def is unfolded by `simp only [isqrt]`.
  `rename_i h` names the hypothesis that `split` introduced anonymously.
-/

namespace M26

-- BEGIN SPEC
def isqrt (n : Nat) : Nat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) :=
-- END SPEC
  sorry

end M26

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recursion on `n`: from `r = isqrt n`, the root of `n + 1` is `r` or `r + 1`.
H2. `isqrt (n+1) = if (r+1)*(r+1) ≤ n+1 then r+1 else r`. Prove the spec by induction on `n`, splitting that `if`.
H3. In each branch: `simp only [Nat.add_mul, Nat.mul_add] at ih h ⊢; omega` (the only nonlinear atom is `r * r`).
-/
