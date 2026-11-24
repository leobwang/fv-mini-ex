/- E015 | Induction on lists | 3 min | induction, List
GOAL
  Prove facts about your own `len` and `app` (append) by induction on the first list.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E015

-- BEGIN SPEC
def len {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => len xs + 1

def app {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys
-- END SPEC

/- SKELETON · app_nil
  1. Induct on `xs`, the list `app` recurses on:                            R1
  2. Case `nil`: `app [] []` computes to `[]`:                              R2
  3. Case `cons`: one `simp` with `app` and `ih` does three things:
       unfold `app (x :: xs) []` to `x :: app xs []`                        R3
       peel the common head `x`                                             R4
       the tails' equation is `ih`                                          R5
-/
-- BEGIN SPEC
theorem app_nil {α : Type} (xs : List α) : app xs [] = xs :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [app, ih]

/- SKELETON · len_app
  1. Induct on `xs`:                                                        R1
  2. Case `nil`: unfold `app` and `len`; the goal is `len ys = 0 + len ys`,
     which `rfl` cannot close but `simp` can:                               R3 → R6
  3. Case `cons`: unfold `app` and `len`, rewrite with `ih`:                R5
       left over: `len xs + len ys + 1 = len xs + 1 + len ys`
  4. Reorder the sum:                                                       R7
-/
-- BEGIN SPEC
theorem len_app {α : Type} (xs ys : List α) : len (app xs ys) = len xs + len ys :=
-- END SPEC
  by
    induction xs with
    | nil => simp [app, len]
    | cons x xs ih => simp [app, len, ih]; omega

/- SKELETON · app_assoc
  1. Induct on `xs` (first argument of the inner `app` on the left and of
     the outer `app` on the right):                                         R1
  2. Case `nil`: both sides compute to `app ys zs`:                         R2
  3. Case `cons`: unfold `app` (twice on the left, once on the right),
     peel the head `x`, finish with `ih`, all in one `simp`:                R3, R4, R5
-/
-- BEGIN SPEC
theorem app_assoc {α : Type} (xs ys zs : List α) : app (app xs ys) zs = app xs (app ys zs) :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [app, ih]

end E015

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `len` and `app` recurse on their first list argument, so induct on `xs` (R1): then every `app xs _`
    and `len xs` in the goal becomes `app [] _` / `app (x :: xs) _`, which compute.
H2. Case `nil`: `rfl` (R2), except in `len_app`, where `0 + len ys` is left and `simp [app, len]` is
    needed (R6). Case `cons`: `simp` with the definitions and `ih` (R5); in `len_app` it leaves a sum in
    another order, which `omega` closes (R7).
H3. `induction xs with | nil => rfl | cons x xs ih => simp [app, ih]` (`app_nil`, `app_assoc`);
    `len_app`: `| nil => simp [app, len] | cons x xs ih => simp [app, len, ih]; omega`.
-/
