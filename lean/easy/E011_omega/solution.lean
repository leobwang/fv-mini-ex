/- E011 | omega | 1-3 min | omega, Nat subtraction, Int, casts
GOAL
  Discharge linear arithmetic over `Nat` and `Int` with `omega`, including truncated subtraction.

REFERENCE
  example (n : Nat) (h : n > 2) : n - 1 ≥ 2 := by omega   -- linear (in)equalities over Nat/Int
  example (x y : Int) (h : x < y) : x + 1 ≤ y := by omega
  example (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by omega   -- / and % by literals are fine
  example (n : Nat) : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega   -- Nat→Int casts too
  omega fails on `x * y` of two variables (it treats such a product as an opaque atom).
NOTE: Nat subtraction truncates at 0 (`3 - 5 = 0`), so `n - m + m = n` needs `m ≤ n`.
-/

-- BEGIN SPEC
theorem sub_add_cancel_nat (n m : Nat) (h : m ≤ n) : n - m + m = n :=
-- END SPEC
  by omega

-- BEGIN SPEC
theorem truncated (n : Nat) : n - (n + 3) = 0 :=
-- END SPEC
  by omega

-- BEGIN SPEC
theorem solve_system (x y : Int) (h1 : 2 * x + y = 7) (h2 : x - y = 2) : x = 3 ∧ y = 1 :=
-- END SPEC
  by omega

-- BEGIN SPEC
theorem cast_sub (n : Nat) : ((n - 1 : Nat) : Int) ≥ (n : Int) - 1 :=
-- END SPEC
  by omega

-- BEGIN SPEC
theorem mod_fact (a : Nat) (h : a % 4 = 3) : a % 2 = 1 :=
-- END SPEC
  by omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal here is linear arithmetic with literals as the only multipliers.
H2. `omega` handles hypotheses in the context automatically; no need to pass them.
H3. Each proof is the single tactic `omega`.
-/
