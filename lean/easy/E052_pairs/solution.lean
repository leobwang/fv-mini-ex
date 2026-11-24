/- E052 | Pairs | 2 min | Prod, .1, .2, Prod.ext, pattern lambda
GOAL
  Work with pairs `α × β`: projections, eta (rebuilding a pair gives it back), extensionality,
  and a function defined by a pattern-matching lambda.

BANNED: grind

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E052

-- BEGIN SPEC
def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)
def addPair : Nat × Nat → Nat := fun (a, b) => a + b
-- END SPEC

/- SKELETON · swap_swap
  1. Unfold `swap` (both occurrences); the goal is a pair built from projections:   R3
  2. Reduce the projections of the literal pairs. What is left, `(p.fst, p.snd) = p`,
     is eta, and `dsimp only` closes it by itself (no `rfl` after it):               R1
     Shortcut for steps 1–2: R2 (`rfl` unfolds, reduces and uses eta by itself).
-/
-- BEGIN SPEC
theorem swap_swap {α β : Type} (p : α × β) : swap (swap p) = p :=
-- END SPEC
  rfl

/- SKELETON · pair_ext
  1. An equation of pairs from equations of components: the library's extensionality
     lemma, with the two component goals closed by `h1` and `h2`:                   R4
     (as a tactic, or as one term)
-/
-- BEGIN SPEC
theorem pair_ext (p q : Nat × Nat) (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q :=
-- END SPEC
  Prod.ext h1 h2

/- SKELETON · addPair_swap
  1. Split `p` into its components so that `addPair` can compute:                  R5
  2. Optional, to see the goal: unfold both names and reduce the `match`es;
     the goal becomes `b + a = a + b`:                                              R3 → R1, R6
  3. Close with commutativity of `+` (mind the argument order):                     R7
-/
-- BEGIN SPEC
theorem addPair_swap (p : Nat × Nat) : addPair (swap p) = addPair p :=
-- END SPEC
  by
    obtain ⟨a, b⟩ := p
    exact Nat.add_comm b a

end E052

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `swap_swap`: unfold `swap (swap p)` by hand: which pair do you get, and what does eta say about it?
    `pair_ext` is extensionality for `×`. `addPair p` cannot compute while `p` is a variable.
H2. `swap_swap` holds by definition (R3 → R1, or just R2). `pair_ext` is one library lemma (R4).
    For `addPair_swap`, split `p` into `(a, b)` (R5); both sides then compute to plain sums (R3, R6),
    and commutativity of `+` finishes (R7).
H3. `swap_swap`: `rfl`. `pair_ext`: `Prod.ext h1 h2`. `addPair_swap`: `obtain ⟨a, b⟩ := p`, then
    `exact Nat.add_comm b a`.
-/
