/- M020 | Insertion sort | 20 min | inductive Sorted, List.Perm, induction on derivations [R14]
GOAL
  Prove insertion sort returns a sorted permutation of its input.

REFERENCE
  -- `l₁.Perm l₂` (notation `l₁ ~ l₂`): same elements with multiplicity
  example (l : List Nat) : l.Perm l := .refl l
  example (x : Nat) (l₁ l₂ : List Nat) (h : l₁.Perm l₂) : (x :: l₁).Perm (x :: l₂) := h.cons x
  #check List.Perm.swap    -- (x y : α) (l : List α) : (y :: x :: l).Perm (x :: y :: l)
  #check List.Perm.trans   -- l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃
  example (x y : Nat) (h : ¬ x ≤ y) : y ≤ x := by omega
  -- `induction h` on `h : Sorted l` gives cases nil / single / cons (name args with `@cons y z rest hyz hs ih`).
-/

namespace M020

-- BEGIN SPEC
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons {x y : Nat} {rest : List Nat} : x ≤ y → Sorted (y :: rest) → Sorted (x :: y :: rest)

def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (isort xs)
-- END SPEC

theorem ins_sorted (x : Nat) {l : List Nat} (h : Sorted l) : Sorted (ins x l) := by
  induction h with
  | nil => exact .single x
  | single y =>
    by_cases hxy : x ≤ y
    · simp only [ins, hxy, if_true]
      exact .cons hxy (.single y)
    · simp only [ins, hxy, if_false]
      exact .cons (by omega) (.single x)
  | @cons y z rest hyz hs ih =>
    by_cases hxy : x ≤ y
    · simp only [ins, hxy, if_true]
      exact .cons hxy (.cons hyz hs)
    · by_cases hxz : x ≤ z
      · simp only [ins, hxz, if_true] at ih
        simp only [ins, hxy, hxz, if_true, if_false]
        exact .cons (by omega) ih
      · simp only [ins, hxz, if_false] at ih
        simp only [ins, hxy, hxz, if_false]
        exact .cons hyz ih

theorem ins_perm (x : Nat) (l : List Nat) : (ins x l).Perm (x :: l) := by
  induction l with
  | nil => exact .refl _
  | cons y ys ih =>
    by_cases hxy : x ≤ y
    · simp only [ins, hxy, if_true]
      exact .refl _
    · simp only [ins, hxy, if_false]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

-- BEGIN SPEC
theorem isort_sorted (xs : List Nat) : Sorted (isort xs) :=
-- END SPEC
  by
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact ins_sorted x ih

-- BEGIN SPEC
theorem isort_perm (xs : List Nat) : (isort xs).Perm xs :=
-- END SPEC
  by
    induction xs with
    | nil => exact .refl _
    | cons x xs ih => exact (ins_perm x (isort xs)).trans (ih.cons x)

end M020

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems reduce to facts about one `ins` step: it keeps lists sorted and adds exactly `x`.
H2. `ins_sorted : Sorted l → Sorted (ins x l)` by induction on the `Sorted` derivation; in the `cons` case split on `x ≤ y` and `x ≤ z`. `ins_perm : (ins x l).Perm (x :: l)` by induction on `l`.
H3. In the cons case with `¬ x ≤ y`, the IH is `Sorted (ins x (z :: rest))`; unfold it with `simp only [ins, hxz, ...] at ih` and use `.cons`. Perm step: `(ih.cons y).trans (List.Perm.swap x y ys)`.
-/
