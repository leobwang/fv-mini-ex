/- M016 | Reverse with an accumulator | 10 min | accumulator, List.reverse, getElem? [R07]
GOAL
  Show that the linear-time `rev` (tail-recursive with an accumulator) equals `List.reverse`,
  and that it puts element `n-1-i` at position `i`.
BANNED: List.reverseAux_eq, List.reverse_eq_reverseAux

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M016

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

/- SKELETON · rev_eq_reverse
  0. MILESTONE first, as your own theorem above this one (outside the spec):
       theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc
     a. Induction on `xs`, generalizing the accumulator:                       R1
     b. nil:  both sides compute to `acc`:                                     R2
     c. cons x xs ih:  unfold `revAcc`, use `ih` at `x :: acc`, then
        reverse_cons, append_assoc, `[x] ++ acc = x :: acc`
        (one `simp` with `revAcc` and `ih` does all of these):                  R3 → R4 → R5 → R6 → R7
  1. `rev_eq_reverse`:  unfold `rev`, rewrite with the milestone at `acc = []`,
     drop `++ []`:                                                              R3 → R4 → R8
-/
-- BEGIN SPEC
theorem rev_eq_reverse {α : Type} (xs : List α) : rev xs = xs.reverse :=
-- END SPEC
  by simp [rev, revAcc_eq]

/- SKELETON · rev_getElem
  1. Replace `rev xs` by `xs.reverse` with the theorem above:                   rw [rev_eq_reverse]
  2. Index into the reversed list, passing `h` for the side condition:          R9
-/
-- BEGIN SPEC
theorem rev_getElem {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    (rev xs)[i]? = xs[xs.length - 1 - i]? :=
-- END SPEC
  by rw [rev_eq_reverse, List.getElem?_reverse h]

end M016

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction straight on `rev xs = xs.reverse` gets stuck: the recursive call has accumulator
    `x :: []`, not `[]`. What is `revAcc xs acc` in terms of `List.reverse` and `++`, for ANY `acc`?
H2. State the milestone `revAcc_eq : revAcc xs acc = xs.reverse ++ acc` and prove it by
    `induction xs generalizing acc` (nil: `rfl`). Then `rev_eq_reverse` is the case `acc = []`, and
    `rev_getElem` rewrites with `rev_eq_reverse` and `List.getElem?_reverse`.
H3. `theorem revAcc_eq (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc`; its cons case is
    `simp [revAcc, ih]`. Then `rw [rev_eq_reverse, List.getElem?_reverse h]` for `rev_getElem`.
-/
