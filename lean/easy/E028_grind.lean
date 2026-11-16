/- E028 | grind | 2-3 min | grind
GOAL
  Meet `grind`: congruence closure + linear arithmetic + ring normalisation + case splits.

REFERENCE
  example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by grind   -- congruence
  example (x y : Int) (h : x < y) (h2 : y < x + 1) : False := by grind       -- linear arith
  example (a b : Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by grind  -- ring identities
  example (b : Bool) (h : (if b then 1 else 2) = 1) : b = true := by grind    -- splits ifs
  grind does not prove nonlinear inequalities, and does no induction.
-/

-- BEGIN SPEC
theorem grind_congr (f : Nat → Nat) (a b c : Nat) (h1 : f a = b) (h2 : a = c) (h3 : b + 1 = 5) :
    f c = 4 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem grind_antisymm (g : Int → Int) (x y : Int) (h1 : x ≤ y) (h2 : y ≤ x) : g x = g y :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem grind_ring (a b : Nat) (h : a = b + 2) : (a - 1) * (a - 1) = (b + 1) * (b + 1) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem grind_ite (n : Nat) (f : Nat → Nat) (hf : f n = if n < 5 then 0 else n) (h : f n ≠ 0) :
    5 ≤ n :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal is in grind's fragment: equalities, linear facts, ring normalisation, `if` splits.
H2. No setup is needed; grind reads the hypotheses in the context.
H3. Each proof is `grind`.
-/
