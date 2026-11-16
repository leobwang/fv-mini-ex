/- M022 | Linear search | 15 min | Option, xs[i]?, induction generalizing [R04]
GOAL
  Implement `search k xs`: the index of the first occurrence of `k` in `xs`, or `none`.
  Prove the result is correct, is the first occurrence, and that `none` means `k ∉ xs`.

REFERENCE
  example (xs : List Nat) (x : Nat) : (x :: xs)[0]? = some x := rfl       -- List.getElem?_cons_zero
  example (xs : List Nat) (x i : Nat) : (x :: xs)[i + 1]? = xs[i]? := rfl -- List.getElem?_cons_succ
  #check Option.map_eq_some_iff   -- Option.map f x = some b ↔ ∃ a, x = some a ∧ f a = b
  example (o : Option Nat) : o.map (· + 1) = none ↔ o = none := by simp
  example (j : Nat) (h : j < 0) : False := by omega
  -- `cases hs : search k xs with | none => .. | some i' => ..` splits on the recursive result.
-/

namespace M022

-- BEGIN SPEC
def search (k : Nat) (xs : List Nat) : Option Nat :=
-- END SPEC
  match xs with
  | [] => none
  | x :: xs => if x = k then some 0 else (search k xs).map (· + 1)

-- BEGIN SPEC
theorem search_some (k : Nat) (xs : List Nat) (i : Nat) (h : search k xs = some i) :
    xs[i]? = some k ∧ ∀ j < i, xs[j]? ≠ some k :=
-- END SPEC
  by
    induction xs generalizing i with
    | nil => simp [search] at h
    | cons x xs ih =>
      simp only [search] at h
      split at h
      · simp at h
        subst h
        simp_all
      · cases hs : search k xs with
        | none => simp [hs] at h
        | some i' =>
          simp [hs] at h
          subst h
          obtain ⟨h1, h2⟩ := ih i' hs
          refine ⟨by simpa using h1, ?_⟩
          intro j hj
          cases j with
          | zero => simp_all
          | succ j => simpa using h2 j (by omega)

-- BEGIN SPEC
theorem search_none (k : Nat) (xs : List Nat) (h : search k xs = none) : k ∉ xs :=
-- END SPEC
  by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [search] at h
      split at h
      · simp at h
      · simp at h
        simp only [List.mem_cons, not_or]
        exact ⟨fun hk => by simp_all, ih h⟩

end M022

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recurse on the list; on a miss, shift the recursive answer by one with `Option.map`.
H2. `search_some`: induction on `xs` generalising `i`; split on the `if`; in the miss case split on the recursive call.
H3. Implementation: `match xs with | [] => none | x :: xs => if x = k then some 0 else (search k xs).map (· + 1)`. In the miss case use `ih i' hs`, and for `∀ j < i' + 1` do `cases j`.
-/
