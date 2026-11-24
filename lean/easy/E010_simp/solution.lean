/- E010 | simp | 2-3 min | simp, simp only, simp at, simp [f]
GOAL
  Let the simplifier do routine rewriting, with and without extra lemmas and definitions.
BANNED: omega, grind

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def square (n : Nat) : Nat := n * n
-- END SPEC

/- SKELETON · simp_default
  1. One plain `simp`; every lemma it needs is in the default simp set:    R1
     inside that call, in this order:
       `xs ++ []` → `xs`                                                    R2
       `(xs ++ ys).length` → `xs.length + ys.length`                       R3
       both sides now equal → cancelled and closed                          R11
-/
-- BEGIN SPEC
theorem simp_default (xs ys : List Nat) : (xs ++ [] ++ ys).length = xs.length + ys.length :=
-- END SPEC
  by simp

/- SKELETON · simp_unfold
  1. `square` is your own definition: plain `simp` does not unfold it. It only
     drops the `+ 0` and stops at `square n = n * n`.
     One `simp` that is given the name `square`:                            R4
     inside that call, in this order:
       `square (n + 0)` → its body, with `n + 0` in both places             R4
       `n + 0` → `n`                                                        R5
       both sides now equal → closed (`eq_self`)                            R1
-/
-- BEGIN SPEC
theorem simp_unfold (n : Nat) : square (n + 0) = n * n :=
-- END SPEC
  by simp [square]

/- SKELETON · simp_hyp
  1. The clutter is in the hypothesis, not the goal: simplify `h`:          R6
       `a * 1` → `a`, `+ 0` dropped on both sides, so `h : a = b`           R7, R5
  2. The goal is now exactly `h`:                                           R8
-/
-- BEGIN SPEC
theorem simp_hyp (a b : Nat) (h : a * 1 + 0 = b + 0) : a = b :=
-- END SPEC
  by
    simp at h
    exact h

/- SKELETON · simp_with
  1. One `simp` that is given the hypothesis `hf`:                          R9
     inside that call:
       `hf` rewrites the inner `f a`, then the outer `f (…)`                R9
       left over: an equation of the form `a + 1 + 1 = a + 2`
       cancel the `+ 1` on the right, then the `a` on the left,
       then `1 = 1` → closed                                                R10 → R11
-/
-- BEGIN SPEC
theorem simp_with (f : Nat → Nat) (a : Nat) (hf : ∀ x, f x = x + 1) : f (f a) = a + 2 :=
-- END SPEC
  by simp [hf]

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each goal is routine rewriting. Ask what `simp` already knows (the `@[simp]` lemmas R2, R3, R5, R7,
    R10) and what you must hand it: your own definition `square`, the hypothesis `hf`, or the place
    to work (`at h`).
H2. `simp_default`: plain `simp` (R1). `simp_unfold`: plain `simp` does not unfold `square` and stops
    at `square n = n * n`; pass the name (R4). `simp_hyp`: simplify the hypothesis (R6), then close the goal with it (R8).
    `simp_with`: pass `hf` (R9); `simp` uses it twice and finishes the arithmetic itself (R10, R11).
H3. `simp`, `simp [square]`, `simp at h` then `exact h`, `simp [hf]`.
-/
