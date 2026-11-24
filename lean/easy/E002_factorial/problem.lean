/- E002 | Factorial by pattern matching | 2-3 min | def, match, structural recursion
GOAL
  Define `fact` by structural recursion so that the three theorems hold, then prove them.

REFERENCE
  def len : List Nat → Nat | [] => 0 | _ :: xs => 1 + len xs   -- equation-style matching
  def pred' (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => k  -- `match` on an argument
  example : pred' 5 = 4 := rfl     -- structural recursion still computes, so `rfl` works
  example (k : Nat) : pred' (k + 1) = k := rfl   -- ...even on a symbolic `k + 1`
  The recursive call must be on a structurally smaller argument (`k` inside `k + 1`).
-/

-- BEGIN SPEC
def fact (n : Nat) : Nat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fact_zero : fact 0 = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem fact_five : fact 5 = 120 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `fact_zero` and `fact_succ` together say exactly what each `match` arm must return.
H2. Match on `n` with arms `0` and `k + 1`; recurse on `k`. Then each theorem is true by computation.
H3. `match n with | 0 => 1 | k + 1 => (k + 1) * fact k`, and `rfl` for all three theorems.
-/
