/- E015 | Induction on lists | 3 min | induction, List
GOAL
  Prove facts about your own `len` and `app` (append) by induction on the first list.

REFERENCE
  def sz {α : Type} : List α → Nat | [] => 0 | _ :: xs => sz xs + 1
  example {α : Type} (xs : List α) : sz (xs ++ []) = sz xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.cons_append, sz, ih]   -- ih : sz (xs ++ []) = sz xs
  `x :: xs` is cons; `[]` is nil. `simp [f]` unfolds `f` on a cons/nil argument.
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

-- BEGIN SPEC
theorem app_nil {α : Type} (xs : List α) : app xs [] = xs :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem len_app {α : Type} (xs ys : List α) : len (app xs ys) = len xs + len ys :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem app_assoc {α : Type} (xs ys zs : List α) : app (app xs ys) zs = app xs (app ys zs) :=
-- END SPEC
  sorry

end E015

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each statement recurses on `xs`, the first argument of `app`, so induct on `xs`.
H2. In the `cons` case, `simp [app, len, ih]` unfolds one step and uses the hypothesis.
H3. `induction xs with | nil => simp [app, len] | cons x xs ih => simp [app, len, ih]; omega`.
-/
