/- E20 | calc | 3 min | calc, Nat.add_mul
GOAL
  Write proofs as `calc` chains of equalities and inequalities.

REFERENCE
  example (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c :=
    calc a < b := h1
      _ ≤ c := h2                     -- `_` is the previous right-hand side; < and ≤ chain to <
  example (a b : Nat) (h : a = b) : a * 2 = b + b :=
    calc a * 2 = b * 2 := by rw [h]
      _ = b + b := by omega           -- each step is any proof term or `by` block
  #check Nat.mul_add   -- n * (m + k) = n * m + n * k   (also Nat.add_mul)
BANNED: grind
-/

-- BEGIN SPEC
theorem calc_lt (a b c d : Nat) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) : a < d :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem calc_sq (a b c : Nat) (h1 : a = b + c) (h2 : c = b) : a * a = 4 * (b * b) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `calc_lt` is three steps, one per hypothesis.
H2. `calc_sq`: substitute first, then expand the product, then collect the `b * b` terms (omega sees `b * b` as one atom).
H3. Steps: `a * a = (b + b) * (b + b)`, `_ = b * b + b * b + (b * b + b * b)` by `rw [Nat.add_mul, Nat.mul_add]`, `_ = 4 * (b * b)` by `omega`.
-/
