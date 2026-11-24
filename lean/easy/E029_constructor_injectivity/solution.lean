/- E029 | Constructor injectivity | 2-3 min | injection, nomatch, nofun, noConfusion
GOAL
  Use the facts that constructors are injective and that different constructors never coincide.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
-- END SPEC

/- SKELETON · circle_inj
  1. Same constructor `Shape.circle` on both sides of `h`, one argument: injectivity
     gives `a = b`, which is exactly the goal, so the step closes it:              R1
     (or: R8 at `h`, then use `h`)
-/
-- BEGIN SPEC
theorem circle_inj (a b : Nat) (h : Shape.circle a = Shape.circle b) : a = b :=
-- END SPEC
  by injection h

/- SKELETON · rect_inj
  1. Same constructor `Shape.rect`, two arguments: get both argument equations,
     NAMED, into the context:                                                     R2
  2. Pair them into the `∧`:                                                      R3
     (or: R8 at `h` turns `h` into the conjunction itself)
-/
-- BEGIN SPEC
theorem rect_inj (a b c d : Nat) (h : Shape.rect a b = Shape.rect c d) : a = c ∧ b = d :=
-- END SPEC
  by
    injection h with h1 h2
    exact ⟨h1, h2⟩

/- SKELETON · circle_ne_rect
  1. Different constructors (`circle` vs `rect`). Either the whole proof is one
     term:                                                                         R6
     or in tactic mode: open the `≠`, then refute the clash in the new
     hypothesis:                                                                   R4 → R5
     (name it `e`, not `h`: `h` is already one of the `Nat` arguments here)
-/
-- BEGIN SPEC
theorem circle_ne_rect (r w h : Nat) : Shape.circle r ≠ Shape.rect w h :=
-- END SPEC
  nofun

/- SKELETON · cons_inj_head
  1. `::` is the constructor `List.cons` (head, tail): name both argument
     equations:                                                                    R7 (= R2 on lists)
  2. Pair them into the `∧`:                                                      R3
-/
-- BEGIN SPEC
theorem cons_inj_head (x y : Nat) (xs ys : List Nat) (h : x :: xs = y :: ys) : x = y ∧ xs = ys :=
-- END SPEC
  by
    injection h with h1 h2
    exact ⟨h1, h2⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Equal constructor applications have equal arguments (injectivity); different constructors are
    never equal (disjointness). `::` is a constructor too (`List.cons`).
H2. Injectivity: `injection h` (R1), naming the equations with `with` when you need them (R2), then
    `⟨_, _⟩` (R3). Disjointness: `intro e; nomatch e` (R4, R5) or the term `nofun` (R6).
H3. `circle_inj`: `by injection h`. `rect_inj`, `cons_inj_head`: `injection h with h1 h2` then
    `exact ⟨h1, h2⟩`. `circle_ne_rect`: `nofun`.
-/
