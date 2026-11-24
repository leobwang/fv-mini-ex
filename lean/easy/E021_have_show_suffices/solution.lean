/- E021 | have, show, suffices | 3 min | have, show, suffices
GOAL
  Structure proofs with intermediate facts (`have`), a restated goal (`show`), and backward steps (`suffices`).

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · have_chain
  1. Instantiate `h` at 0, 1 and 2, writing each type out
     (`f 1`, not `f (0 + 1)`):                                                    R1, R1, R1  (not R2)
  2. The goal is now linear arithmetic in the atoms `f 0, f 1, f 2, f 3`:        R3
-/
-- BEGIN SPEC
theorem have_chain (f : Nat → Nat) (h : ∀ n, f n < f (n + 1)) : f 0 + 3 ≤ f 3 :=
-- END SPEC
  by
    have h0 : f 0 < f 1 := h 0
    have h1 : f 1 < f 2 := h 1
    have h2 : f 2 < f 3 := h 2
    omega

/- SKELETON · suffices_mono
  1. The goal `f n ≤ f (n * 2)` is the conclusion of `mono`. Say it suffices to prove
     its premise `hs : n ≤ n * 2`, closing the old goal by feeding `mono` its
     two numbers and `hs`:                                                       R4 with R5 inside
  2. Prove the premise (linear arithmetic):                                      R3
-/
-- BEGIN SPEC
theorem suffices_mono (f : Nat → Nat) (mono : ∀ a b, a ≤ b → f a ≤ f b) (n : Nat) :
    f n ≤ f (n * 2) :=
-- END SPEC
  by
    suffices hs : n ≤ n * 2 by exact mono n (n * 2) hs
    omega

/- SKELETON · show_ne
  1. `xs ≠ []` is `xs = [] → False`: introduce `hx : xs = []`:                  R7
  2. (Optional) restate the goal, to see what is left:                           R6
  3. Substitute `[]` for `xs` in `h`:                                            R8
  4. `h : [].length = 3` simplifies to `False`, which closes the goal:          R10 (uses R9)
-/
-- BEGIN SPEC
theorem show_ne (xs : List Nat) (h : xs.length = 3) : xs ≠ [] :=
-- END SPEC
  by
    intro hx
    show False
    rw [hx] at h
    simp at h

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `have_chain`: three instances of `h` give `f 0 < f 1 < f 2 < f 3`; each `<` adds at least 1.
    `suffices_mono`: the goal is what `mono` concludes. `show_ne`: `≠` is `= … → False`, so `intro`.
H2. `have_chain`: `have` each instance with its type written out (R1), then `omega` (R3).
    `suffices_mono`: `suffices` the premise of `mono` (R4), then `omega`.
    `show_ne`: `intro`, rewrite `h` with the new hypothesis, then simplify `h` (R7, R8, R10).
H3. `have h0 : f 0 < f 1 := h 0` (and the same at 1, 2), then `omega`.
    `suffices hs : n ≤ n * 2 by exact mono n (n * 2) hs`, then `omega`.
    `intro hx; rw [hx] at h; simp at h`.
-/
