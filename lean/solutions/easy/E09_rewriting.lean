/- E09 | Rewriting | 2-3 min | rw, rw ←, rw at
GOAL
  Prove equalities by rewriting with hypotheses and library equations.

REFERENCE
  example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [h]   -- replace a by b, then try rfl
  example (a b : Nat) (h : a = b) : b + 1 = a + 1 := by rw [← h] -- right-to-left: b becomes a
  example (a b : Nat) (h : a = b) (h2 : a > 3) : b > 3 := by rw [h] at h2; exact h2
  example (a b : Nat) : a + b = b + a := by rw [Nat.add_comm]    -- Nat.add_comm a b : a + b = b + a
  #check List.length_append  -- (as ++ bs).length = as.length + bs.length
  `rw [h₁, h₂]` rewrites in order; it rewrites every instance of the first match it finds.
BANNED: simp, simp_all, grind, omega
-/

-- BEGIN SPEC
theorem rw_chain (a b c : Nat) (h1 : a = b + 1) (h2 : b = c) : a = c + 1 :=
-- END SPEC
  by rw [h1, h2]

-- BEGIN SPEC
theorem rw_back (f : Nat → Nat) (a b : Nat) (h : f a = b) (h' : f a + 1 = 5) : b + 1 = 5 :=
-- END SPEC
  by
    rw [← h]
    exact h'

-- BEGIN SPEC
theorem rw_at (a b c : Nat) (h1 : a + 0 = b) (h2 : b = c) : a = c :=
-- END SPEC
  by
    rw [Nat.add_zero] at h1
    rw [h1, h2]

-- BEGIN SPEC
theorem rw_lemmas (xs ys : List Nat) (h : xs = ys ++ [7]) : xs.length = 1 + ys.length :=
-- END SPEC
  by
    rw [h, List.length_append, Nat.add_comm]
    rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `rw [h]` needs the left side of `h` to appear literally in the goal (or hypothesis).
H2. `rw_back`: the goal mentions `b` but `h'` mentions `f a`; rewrite one into the other.
H3. `rw_at`: `rw [Nat.add_zero] at h1`, then `rw [h1, h2]`. `rw_lemmas`: `rw [h, List.length_append, Nat.add_comm]`.
-/
