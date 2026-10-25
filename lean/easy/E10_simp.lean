/- E10 | simp | 2-3 min | simp, simp only, simp at, simp [f]
GOAL
  Let the simplifier do routine rewriting, with and without extra lemmas and definitions.

REFERENCE
  example (xs : List Nat) : (xs ++ []).length = xs.length := by simp   -- default simp set
  example (n : Nat) (h : n + 0 = 3) : n = 3 := by simp at h; exact h   -- simplify a hypothesis
  example (xs : List Nat) : (xs ++ []).length = xs.length := by simp only [List.append_nil]
    -- `simp only [..]`: just these lemmas (predictable, fast)
  def sq (n : Nat) : Nat := n * n
  example : sq 2 = 4 := by simp [sq]       -- `simp [f]` unfolds the definition `f`
  `simp [h]` also rewrites with hypothesis `h`; `simp_all` simplifies everything.
BANNED: omega, grind
-/

-- BEGIN SPEC
def square (n : Nat) : Nat := n * n
-- END SPEC

-- BEGIN SPEC
theorem simp_default (xs ys : List Nat) : (xs ++ [] ++ ys).length = xs.length + ys.length :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem simp_unfold (n : Nat) : square (n + 0) = n * n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem simp_hyp (a b : Nat) (h : a * 1 + 0 = b + 0) : a = b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem simp_with (f : Nat → Nat) (a : Nat) (hf : ∀ x, f x = x + 1) : f (f a) = a + 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Plain `simp` knows lemmas like `List.append_nil` and `Nat.add_zero` already.
H2. `square` is your own definition: simp will not look inside unless you pass it.
H3. `simp [square]`, `simp at h; exact h`, and `simp [hf]` (simp then normalises `a + 1 + 1`).
-/
