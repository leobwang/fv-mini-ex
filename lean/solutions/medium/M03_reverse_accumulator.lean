/- M03 | Reverse with an accumulator | 10 min | accumulator, List.reverse, getElem? [R07]
GOAL
  Show that the linear-time `rev` (tail-recursive with an accumulator) equals `List.reverse`,
  and that it puts element `n-1-i` at position `i`.

REFERENCE
  #check List.reverse_cons      -- (a :: as).reverse = as.reverse ++ [a]
  #check List.append_assoc      -- as ++ bs ++ cs = as ++ (bs ++ cs)
  #check List.getElem?_reverse  -- i < l.length → l.reverse[i]? = l[l.length - 1 - i]?
  example (xs : List Nat) : xs[0]? = xs.head? := by cases xs <;> rfl  -- `xs[i]?` : Option
  Generalise the accumulator (as in M02) before inducting.
BANNED: List.reverseAux_eq, List.reverse_eq_reverseAux
-/

namespace M03

-- BEGIN SPEC
def revAcc {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def rev {α : Type} (xs : List α) : List α := revAcc xs []
-- END SPEC

theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [revAcc, ih]

-- BEGIN SPEC
theorem rev_eq_reverse {α : Type} (xs : List α) : rev xs = xs.reverse :=
-- END SPEC
  by simp [rev, revAcc_eq]

-- BEGIN SPEC
theorem rev_getElem {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    (rev xs)[i]? = xs[xs.length - 1 - i]? :=
-- END SPEC
  by rw [rev_eq_reverse, List.getElem?_reverse h]

end M03

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. What is `revAcc xs acc` in terms of `List.reverse` and `++`, for any `acc`?
H2. Prove that lemma by induction on `xs` generalising `acc`; then `rev_eq_reverse` is one `simp`.
H3. `theorem revAcc_eq (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc` (cons case: `simp [revAcc, ih]`). Then `rw [rev_eq_reverse, List.getElem?_reverse h]`.
-/
