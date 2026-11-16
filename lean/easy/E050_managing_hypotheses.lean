/- E050 | Managing hypotheses | 2-3 min | specialize, replace, subst, rw at
GOAL
  Reshape the context: instantiate a `∀`-hypothesis in place, replace a hypothesis by a cleaner
  one, eliminate variables with `subst`, and rewrite in two hypotheses at once.

REFERENCE
  example (f : Nat → Nat) (h : ∀ n, f n = n) : f 2 = 2 := by
    specialize h 2; exact h          -- `h` becomes `f 2 = 2` (use `have h2 := h 2` to keep h)
  example (n : Nat) (h : n + 0 = 3) : n = 3 := by
    replace h : n = 3 := h; exact h  -- new statement, same name; the old `h` is gone
  example (a b : Nat) (h1 : a = b) (h2 : b = 1) : a = 1 := by
    subst h2 h1; rfl                 -- `subst h` (h : x = e or e = x) deletes the variable x
  example (a b : Nat) (h : a = b) (h1 : a > 0) : b > 0 := by
    rw [h] at h1; exact h1           -- several at once: `at h1 h2`; everywhere: `at *`
  #check @Nat.zero_add   -- 0 + n = n          (`clear h` deletes a hypothesis)
BANNED: simp, simpa, simp_all, omega, grind, decide, exact?, apply?, try?
NOTE: `0 + n` is not definitionally `n` (`n + 0` is). `rw` alone could do it all; use the named tactics.
-/

namespace E050

-- BEGIN SPEC
theorem specialize_ex (f : Nat → Nat) (h : ∀ n, f n = 2 * n) : f 3 + f 4 = 14 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem replace_ex (n : Nat) (h : 0 + n = 5) (g : n = 5 → n * 2 = 10) : n * 2 = 10 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem subst_ex (a b c : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = 7) : a + b = 14 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem rw_at_two (a b : Nat) (h : a = b) (h1 : a + 1 = 5) (h2 : 2 * a = 8) :
    b + 1 = 5 ∧ 2 * b = 8 :=
-- END SPEC
  sorry

end E050

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Watch the hypotheses above `⊢` change after each tactic; the goal itself barely moves.
H2. `specialize_ex`: keep one copy (`have h3 := h 3`), then `specialize h 4`, then rewrite the goal.
    `replace_ex`: turn `h` into `n = 5` with `Nat.zero_add`, then feed it to `g`.
    `subst_ex`: eliminate `c`, then `b`, then `a`; what is left computes.
H3. `replace h : n = 5 := by rw [Nat.zero_add] at h; exact h`, then `exact g h`;
    `subst h3 h2 h1; rfl`; `rw [h] at h1 h2; exact ⟨h1, h2⟩`.
-/
