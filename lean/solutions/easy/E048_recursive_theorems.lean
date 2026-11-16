/- E048 | Recursive theorems | 3-5 min | recursion, match, two-step induction
GOAL
  Prove `fib n < 2 ^ n` and two facts about a two-step parity test `evenB` with theorems that call
  themselves on smaller arguments from the `n + 2` case: a proof by induction is a recursive function.

REFERENCE
  def half : Nat → Nat | 0 => 0 | 1 => 0 | n + 2 => half n + 1
  theorem half_le : (n : Nat) → half n ≤ n      -- `match` on n, written as equations
    | 0 => Nat.le_refl 0
    | 1 => Nat.zero_le 1
    | n + 2 => by have ih := half_le n; simp only [half]; omega   -- recursive call = IH
  example (n : Nat) : 2 * (n + 1) = 2 * n + 2 := rfl   -- so `show evenB (2 * n + 2) = _` is accepted
  #check @Nat.pow_succ   -- n ^ (m + 1) = n ^ m * n     (omega treats `2 ^ n` as an unknown number)
  -- `simp only [evenB]` / `rw [evenB]` unfold one equation once the argument looks like `_ + 2`.
  -- Lean accepts the recursive call because `n` is structurally smaller than `n + 2`.
BANNED: induction, grind, fun_induction, fun_cases, Nat.rec, Nat.recOn, Nat.casesOn, Nat.recAux, Nat.casesAuxOn, Nat.div2Induction, Nat.strongRecOn, Nat.caseStrongRecOn, exact?, apply?, try?
NOTE: the induction tactics and recursors are banned so you write the recursion yourself; `fib (n + 2)` needs both `n` and `n + 1`.
-/

namespace E048

-- BEGIN SPEC
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- END SPEC

-- BEGIN SPEC
def evenB : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => evenB n
-- END SPEC

-- BEGIN SPEC
theorem fib_lt_two_pow (n : Nat) : fib n < 2 ^ n :=
-- END SPEC
  match n with
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
    have h1 := fib_lt_two_pow n
    have h2 := fib_lt_two_pow (n + 1)
    simp only [fib, Nat.pow_succ] at *
    omega

-- BEGIN SPEC
theorem evenB_double (n : Nat) : evenB (2 * n) = true :=
-- END SPEC
  match n with
  | 0 => rfl
  | n + 1 => by
    show evenB (2 * n + 2) = true
    simp only [evenB]
    exact evenB_double n

-- BEGIN SPEC
theorem evenB_double_add_one (n : Nat) : evenB (2 * n + 1) = false :=
-- END SPEC
  match n with
  | 0 => rfl
  | n + 1 => by
    show evenB (2 * n + 1 + 2) = false
    simp only [evenB]
    exact evenB_double_add_one n

end E048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Mirror the definition: `fib` has cases `0`, `1`, `n + 2`, so `fib_lt_two_pow` can too. Calling
    `fib_lt_two_pow n` and `fib_lt_two_pow (n + 1)` inside the `n + 2` case gives you two IHs.
H2. `fib_lt_two_pow`: `match n with | 0 => … | 1 => … | n + 2 => …` (small cases by `decide`).
    `evenB_double(_add_one)`: `match n with | 0 => rfl | n + 1 => …`, then `show` the argument as `_ + 2`.
H3. `fib_lt_two_pow`, last case: `have h1 := fib_lt_two_pow n; have h2 := fib_lt_two_pow (n + 1)`, then
    `simp only [fib, Nat.pow_succ] at *; omega`.
    `evenB_double`, last case: `show evenB (2 * n + 2) = true; simp only [evenB]; exact evenB_double n`.
    `evenB_double_add_one`, last case: `show evenB (2 * n + 1 + 2) = false`, then the same two steps.
-/
