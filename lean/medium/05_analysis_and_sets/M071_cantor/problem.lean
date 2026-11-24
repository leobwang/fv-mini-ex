/- M071 | Cantor's theorem | 10 min | diagonal argument, Set, Function.Surjective, mathlib
GOAL
  No function `α → Set α` is surjective; and no list of Boolean sequences indexed by ℕ contains
  every sequence.

BANNED: Function.cantor_surjective, Function.cantor_injective

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M071

/- SKELETON · cantor
  1. Assume surjectivity `hf`; the goal becomes `False`:                      R1
  2. Ask `hf` for the diagonal set `{x | x ∉ f x}`; open the `∃`:
       `a : α`, `ha : f a = {x | x ∉ f x}`                                     R2
  3. Prove first, as a `have`:  h : a ∈ f a ↔ a ∉ f a                         R6
       →  assume `a ∈ f a`; copy it, rewrite the copy with `ha`,
          and read the set-builder off                                         R5, R4 (R3)
       ←  assume `a ∉ f a`; `rw [ha]` in the goal, read it off                 R4
  4. Refute `h` (the liar, W1): split on `a ∈ f a`, use `h` in the
     matching direction, apply the negation                                    R7, R8, R9
-/
-- BEGIN SPEC
theorem cantor {α : Type} (f : α → Set α) : ¬ Function.Surjective f :=
-- END SPEC
  sorry

/- SKELETON · diagonal
  1. Witness: the flipped diagonal `fun n => !f n n`; the `≠` part gives
     `n`, `h : f n = fun n => !f n n`, goal `False`:                           R10
  2. Evaluate `h` at `n` itself:  `this : f n n = !f n n`                      R11
  3. Split on the Bool value of `f n n`, keeping its equation `hfn`:           R12
  4. In both goals the hypotheses contradict each other:                       R13
-/
-- BEGIN SPEC
theorem diagonal (f : ℕ → ℕ → Bool) : ∃ g : ℕ → Bool, ∀ n, f n ≠ g :=
-- END SPEC
  sorry

end M071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Diagonalise: build the set (or sequence) that disagrees with row `f a` at the index `a` itself,
    and ask surjectivity for it (R2). The contradiction comes from comparing at that index.
H2. `cantor`: `intro hf`, `obtain` a row `a` with `ha : f a = {x | x ∉ f x}`, prove
    `a ∈ f a ↔ a ∉ f a` with `constructor` and `ha` (R6, R5, R4), then refute it like the liar (W1).
    `diagonal`: witness `fun n => !f n n` (R10), then evaluate the equation at `n` (R11).
H3. `cantor`: `obtain ⟨a, ha⟩ := hf {x | x ∉ f x}`; finally `by_cases hp : a ∈ f a` with
    `h.mp hp hp` and `hp (h.mpr hp)`. `diagonal`: `refine ⟨fun n => !f n n, fun n h => ?_⟩`,
    `have := congrFun h n`, then `cases hfn : f n n` and `simp_all` in both goals.
-/
