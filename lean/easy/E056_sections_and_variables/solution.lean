/- E056 | Sections and variables | 2-3 min | section, variable, include, namespace, open in
GOAL
  Read a `section` whose `variable` line supplies arguments to every declaration in it: prove facts about
  `twice`, one of which needs a hypothesis that arrives only via `include … in`. Then use a lemma that
  lives in the namespace `Shape`.
BANNED: Nat.mul_comm, ac_rfl, grind, exact?, try?

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E056

section Lists
-- BEGIN SPEC
variable {α : Type} (xs ys : List α) (hne : xs ≠ [])

def twice : List α := xs ++ xs
-- END SPEC

/- SKELETON · twice_length
  1. The context holds only `α` and `xs`, the variables the statement mentions:   R1
     `twice xs` is the section `def` applied to its one argument `xs`:          R2
  2. Unfold `twice` and the length of an append in one `simp` call:              R4 (does R2, R3)
  3. What is left is linear in the unknown `xs.length`:                          R5
-/
-- BEGIN SPEC
theorem twice_length : (twice xs).length = 2 * xs.length :=
-- END SPEC
  by simp [twice]; omega

/- SKELETON · twice_append
  1. Both sides are the same list once `twice` is unfolded:                      R6
-/
-- BEGIN SPEC
theorem twice_append : twice (xs ++ ys) = xs ++ ys ++ (xs ++ ys) :=
-- END SPEC
  rfl

/- SKELETON · twice_ne_nil
  1. `hne : xs ≠ []` is in the context only because of the frozen `include hne in`:   R7
  2. Assume the list is empty: context gains `h : twice xs = []`, goal `False`:  R8
  3. `h` is `xs ++ xs = []` up to unfolding, so the iff applies to it directly:  R9 (.mp)
  4. Take one half of the conjunction, `xs = []`:                                R10
  5. Feed it to `hne`:                                                           R11
-/
-- BEGIN SPEC
include hne in
theorem twice_ne_nil : twice xs ≠ [] :=
-- END SPEC
  -- WHY: `hne` is usable here only because of `include hne in`.
  fun h => hne (List.append_eq_nil_iff.mp h).1
end Lists

namespace Shape
-- BEGIN SPEC
def area (w h : Nat) : Nat := w * h
theorem area_comm (w h : Nat) : area w h = area h w := Nat.mul_comm w h
-- END SPEC
end Shape

/- SKELETON · area_twice
  1. `area` and `area_comm` live in namespace `Shape`: outside it they are
     `Shape.area`, `Shape.area_comm`:                                            R12
  2. Make both summands the same: rewrite the SECOND one with `Shape.area_comm`,
     giving it the arguments that select that occurrence:                        R12 or R13
  3. Now linear in the unknown `Shape.area w h`:                                 R5
-/
-- BEGIN SPEC
theorem area_twice (w h : Nat) : Shape.area w h + Shape.area h w = 2 * Shape.area w h :=
-- END SPEC
  by open Shape in rw [area_comm h w]; omega

end E056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Inside the section, `twice xs` is `xs ++ xs` (R2), and `hne : xs ≠ []` is in scope in `twice_ne_nil` only
    because of `include hne in` (R7). `area_twice` is about `w * h` versus `h * w`, which `omega` treats as two
    unrelated unknowns (R5): do not unfold `Shape.area`.
H2. `twice_length`: `simp [twice]` (R4) leaves `xs.length + xs.length = 2 * xs.length`, then `omega` (R5).
    `twice_append` holds by definition (R6). `twice_ne_nil`: assume `twice xs = []` (R8) and split it with
    `List.append_eq_nil_iff` (R9, R10, R11). `area_twice`: rewrite the second area with the namespaced lemma
    (R12/R13), then it is linear (R5).
H3. `simp [twice]; omega`; `rfl`; `intro h; exact hne (List.append_eq_nil_iff.mp h).1`;
    `rw [Shape.area_comm h w]; omega` (or `open Shape in rw [area_comm h w]`, then `omega`).
-/
