/- E028 | grind | 2-3 min | grind
GOAL
  Meet `grind`: congruence closure + linear arithmetic + ring normalisation + case splits.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · grind_congr
  1. Equalities between terms: `h2` puts `a`, `c` in one class, so `f a` and `f c`
     are congruent, and `h1` adds `b` to their class:                       R1
  2. `h3` is linear: arithmetic gives `b = 4`, which closes the goal:       R2
  Both happen inside one call; no `rw` or `subst` first.
-/
-- BEGIN SPEC
theorem grind_congr (f : Nat → Nat) (a b c : Nat) (h1 : f a = b) (h2 : a = c) (h3 : b + 1 = 5) :
    f c = 4 :=
-- END SPEC
  by grind

/- SKELETON · grind_antisymm
  1. `h1`, `h2` pin `x` and `y` together; arithmetic derives `x = y`:       R4
  2. That equality is passed to congruence, which closes `g x = g y`:       R3
-/
-- BEGIN SPEC
theorem grind_antisymm (g : Int → Int) (x y : Int) (h1 : x ≤ y) (h2 : y ≤ x) : g x = g y :=
-- END SPEC
  by grind

/- SKELETON · grind_ring
  1. `h` gives `a ≥ 2`, which rules out the truncated case `a < 1` of
     `a - 1`, so `a - 1 = b + 1`:                                            R5
  2. The two products now have equal factors (congruence); ring
     normalisation covers any rearrangement:                                R1, R6
-/
-- BEGIN SPEC
theorem grind_ring (a b : Nat) (h : a = b + 2) : (a - 1) * (a - 1) = (b + 1) * (b + 1) :=
-- END SPEC
  by grind

/- SKELETON · grind_ite
  1. `grind` assumes the negated goal `¬ 5 ≤ n`, i.e. `n < 5`:              R8
  2. It splits the `if` in `hf` on `n < 5`:                                 R7
  3. Branch `n < 5`: `f n = 0` (from `hf`) contradicts `h`. Branch
     `¬ n < 5`: contradicts step 1:                                         R1, R8, R2
-/
-- BEGIN SPEC
theorem grind_ite (n : Nat) (f : Nat → Nat) (hf : f n = if n < 5 then 0 else n) (h : f n ≠ 0) :
    5 ≤ n :=
-- END SPEC
  by grind

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every goal is in grind's fragment: equalities and congruence (R1, R3), linear `Nat`/`Int`
    arithmetic with truncated `-` (R2, R4, R5), ring normalisation (R6), `if` splits and the
    negated goal (R7, R8). The SKELETON of each theorem names the modules it combines.
H2. No setup is needed: `grind` reads every hypothesis in the context, negates the goal, and lets
    the modules exchange the facts they derive, all in one call. No `intro`, `rw` or `split` first.
H3. Each proof is the single tactic `grind`.
-/
