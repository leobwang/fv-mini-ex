/- E050 | Managing hypotheses | 2-3 min | specialize, replace, subst, rw at
GOAL
  Reshape the context: instantiate a `∀`-hypothesis in place, replace a hypothesis by a cleaner
  one, eliminate variables with `subst`, and rewrite in two hypotheses at once.

BANNED: simp, simpa, simp_all, omega, grind, decide, exact?, apply?, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E050

/- SKELETON · specialize_ex
  1. Copy the instance at 3, keeping `h`:  h3 : f 3 = 2 * 3                 R1
  2. Turn `h` itself into the instance at 4:  h : f 4 = 2 * 4               R2
  3. Rewrite the goal with both; `rw` closes `2 * 3 + 2 * 4 = 14` itself:    R3
-/
-- BEGIN SPEC
theorem specialize_ex (f : Nat → Nat) (h : ∀ n, f n = 2 * n) : f 3 + f 4 = 14 :=
-- END SPEC
  sorry

/- SKELETON · replace_ex
  1. Replace `h : 0 + n = 5` by `h : n = 5`, proving the new statement
     from the old `h` by rewriting inside it:                               R4 (proof: R5, exact h)
  2. Feed the clean `h` to `g`:                                              exact g h
-/
-- BEGIN SPEC
theorem replace_ex (n : Nat) (h : 0 + n = 5) (g : n = 5 → n * 2 = 10) : n * 2 = 10 :=
-- END SPEC
  sorry

/- SKELETON · subst_ex
  1. Eliminate `c`, then `b`, then `a` (one `subst` can take all three):   R6
  2. The goal is now `7 + 7 = 14`: close it by computation:                 rfl
-/
-- BEGIN SPEC
theorem subst_ex (a b c : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = 7) : a + b = 14 :=
-- END SPEC
  sorry

/- SKELETON · rw_at_two
  1. Rewrite `a` to `b` in both hypotheses at once:                          R7
       h1 : b + 1 = 5      h2 : 2 * b = 8
  2. They are exactly the two conjuncts:                                     R8
-/
-- BEGIN SPEC
theorem rw_at_two (a b : Nat) (h : a = b) (h1 : a + 1 = 5) (h2 : 2 * a = 8) :
    b + 1 = 5 ∧ 2 * b = 8 :=
-- END SPEC
  sorry

end E050

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Watch the hypotheses above `⊢` change after each tactic; the goal itself barely moves. Each theorem
    is one or two context moves (R1–R8) and a one-step finish.
H2. `specialize_ex`: keep one copy (`have h3 := h 3`, R1), then `specialize h 4` (R2), then rewrite the
    goal (R3). `replace_ex`: turn `h` into `n = 5` with `Nat.zero_add` (R4, R5), then feed it to `g`.
    `subst_ex`: eliminate `c`, then `b`, then `a` (R6); what is left computes. `rw_at_two`: R7, R8.
H3. `replace h : n = 5 := by rw [Nat.zero_add] at h; exact h`, then `exact g h`;
    `subst h3 h2 h1; rfl`; `rw [h] at h1 h2; exact ⟨h1, h2⟩`.
-/
