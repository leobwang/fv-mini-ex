/- E009 | Rewriting | 2-3 min | rw, rw ←, rw at
GOAL
  Prove equalities by rewriting with hypotheses and library equations.
BANNED: simp, simp_all, grind, omega

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · rw_chain
  1. Replace `a` by its value from `h1`, then `b` from `h2`, in one `rw` list:  R1, R2
  2. Both sides are now the same: `rw` closes the goal itself (no `rfl`):     R3
-/
-- BEGIN SPEC
theorem rw_chain (a b c : Nat) (h1 : a = b + 1) (h2 : b = c) : a = c + 1 :=
-- END SPEC
  by rw [h1, h2]

/- SKELETON · rw_back
  1. The goal has `b`, `h'` has `f a`: turn `b` back into `f a` with `h`
     used right to left:                                                     R4
  2. The goal is now literally `h'`: close it with `exact`.
     (or: rewrite `h'` with `h` instead, then `exact`:                       R5)
-/
-- BEGIN SPEC
theorem rw_back (f : Nat → Nat) (a b : Nat) (h : f a = b) (h' : f a + 1 = 5) : b + 1 = 5 :=
-- END SPEC
  by
    rw [← h]
    exact h'

/- SKELETON · rw_at
  1. `h1` has `a + 0`, which is not in the goal: clean `h1` itself with
     the library equation `n + 0 = n`, at the hypothesis:                    R5, R6
  2. Now `h1 : a = b`: rewrite the goal with `h1`, then `h2`; `rw` closes it:  R2, R3
-/
-- BEGIN SPEC
theorem rw_at (a b c : Nat) (h1 : a + 0 = b) (h2 : b = c) : a = c :=
-- END SPEC
  by
    rw [Nat.add_zero] at h1
    rw [h1, h2]

/- SKELETON · rw_lemmas
  1. Replace `xs` using `h`:                                                  R1
  2. Split the length of an append into a sum:                                R7
  3. Commute the sum so the `ys.length` terms line up:                        R8
  4. `rw` cannot compute `[7].length`, so the goal stays open: close it:      R10
-/
-- BEGIN SPEC
theorem rw_lemmas (xs ys : List Nat) (h : xs = ys ++ [7]) : xs.length = 1 + ys.length :=
-- END SPEC
  by
    rw [h, List.length_append, Nat.add_comm]
    rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `rw [e]` with `e : l = r` needs `l` to appear literally in the goal (or, with `at k`, in `k`), and it
    closes the goal itself when both sides end up identical. Read the infoview after every rewrite.
H2. `rw_chain`: rewrite with both hypotheses. `rw_back`: the goal has `b`, `h'` has `f a`; use `h` right to
    left. `rw_at`: `a + 0` is not in the goal, so fix `h1` first. `rw_lemmas`: `h`, then the append-length
    lemma, then commutativity; one goal is left that `rw` cannot close.
H3. `rw_back`: after `rw [← h]` the goal is `h'`. `rw_at`: `rw [Nat.add_zero] at h1`, then `rw [h1, h2]`.
    `rw_lemmas`: `rw [h, List.length_append, Nat.add_comm]` leaves `[7].length + ys.length = 1 + ys.length`.
-/
