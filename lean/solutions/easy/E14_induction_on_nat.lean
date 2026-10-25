/- E14 | Induction on Nat | 3 min | induction, Nat
GOAL
  Prove closed forms for two recursive functions by induction on `n`.

REFERENCE
  def tri : Nat → Nat | 0 => 0 | n + 1 => tri n + (n + 1)
  example (n : Nat) : tri n ≤ tri (n + 1) := by
    induction n with
    | zero => decide
    | succ k ih => simp only [tri]; omega   -- `ih : tri k ≤ tri (k + 1)`
  #check Nat.add_mul   -- (n + m) * k = n * k + m * k   (also Nat.mul_add)
  `rw [f]` / `simp only [f]` unfolds one step of a recursive `f` applied to `k + 1`.
-/

-- BEGIN SPEC
def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2

def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)
-- END SPEC

-- BEGIN SPEC
theorem dbl_eq (n : Nat) : dbl n = 2 * n :=
-- END SPEC
  by
    induction n with
    | zero => rfl
    | succ n ih => simp only [dbl, ih]; omega

-- BEGIN SPEC
theorem sumOdd_eq (n : Nat) : sumOdd n = n * n :=
-- END SPEC
  by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [sumOdd, ih, Nat.add_mul, Nat.mul_add]
      omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. In the `succ` case, unfold one step of the definition and use `ih`.
H2. `omega` cannot multiply variables, but it treats `n * n` as an atom: expand `(n + 1) * (n + 1)` first.
H3. `simp only [sumOdd, ih, Nat.add_mul, Nat.mul_add]` then `omega`.
-/
