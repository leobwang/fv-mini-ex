/- E080 | Mutual recursion | 3 min | mutual, Bool, recursive theorem
GOAL
  `isEven` and `isOdd` are defined by mutual recursion (each calls the other). Prove that they are
  complementary, that `isEven` agrees with `n % 2 == 0`, and that `2 * n + 1` is odd.

REFERENCE
  mutual                                       -- functions that call each other share one block
  def f : Nat → Nat | 0 => 0 | n + 1 => g n
  def g : Nat → Nat | 0 => 1 | n + 1 => f n
  end
  example (n : Nat) : f (n + 1) = g n := by simp [f]   -- equation lemmas work as usual
  example : (5 % 2 == 0) = false := rfl        -- `==` is Bool equality; `!b` is Bool negation
  theorem fg : (n : Nat) → f n + g n = 1 | 0 => rfl | n + 1 => by rw [f, g, Nat.add_comm, fg n]
    -- a theorem defined by recursion: the `n + 1` case calls `fg n` (as in E048)
  #check Nat.add_mod_right                     -- (x z : Nat) : (x + z) % z = x % z
-/

namespace E080

-- BEGIN SPEC
mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end
-- END SPEC

-- BEGIN SPEC
theorem isEven_not_odd (n : Nat) : isEven n = !isOdd n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem isEven_mod (n : Nat) : isEven n = (n % 2 == 0) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem isOdd_double_add_one (n : Nat) : isOdd (2 * n + 1) = true :=
-- END SPEC
  sorry

end E080

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfolding one step turns `isEven (k + 1)` into `isOdd k` and `isOdd (k + 1)` into `isEven k`.
H2. `isEven_not_odd`: plain induction on `n`, unfolding both functions in the step. `isEven_mod`: two
    steps of unfolding take `n + 2` back to `n`, so recurse on `n` with cases `0`, `1`, `n + 2`.
    `isOdd_double_add_one`: unfold `isOdd` once and use `isEven_mod`.
H3. `isEven_mod` (the binder `n` is already named, so `match n with`): `| 0 => rfl | 1 => rfl`
    `| n + 2 => by rw [isEven, isOdd, isEven_mod n, Nat.add_mod_right]`;
    the last one is `simp [isOdd, isEven_mod]`.
-/
