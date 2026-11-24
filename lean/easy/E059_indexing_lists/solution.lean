/- E059 | Indexing lists | 2-3 min | getElem, xs[i], xs[i]'h, xs[i]?, dependent if
GOAL
  Implement a total `safeGet` (out-of-range index gives 0) with a dependent `if`, and meet the
  indexing forms `l[i]` (bound proved automatically), `l[i]'h` (bound given by you) and `l[i]?` (an `Option`).

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E059

/- SKELETON · safeGet
  1. Test the bound with a dependent `if`, naming the fact `h`:                 R1
  2. `then` branch: index; `h : i < l.length` is the bound:                     R2
  3. `else` branch: the default `0`.
-/
-- BEGIN SPEC
def safeGet (l : List Nat) (i : Nat) : Nat :=
-- END SPEC
  if h : i < l.length then l[i] else 0

/- SKELETON · lit_get
  1. A literal list, a literal index: the lookup evaluates.                     R3
-/
-- BEGIN SPEC
theorem lit_get : [10, 20, 30][1] = 20 :=
-- END SPEC
  rfl

/- SKELETON · lit_get?
  1. Index 5 is out of range, so `?` gives `none`; it evaluates.                R4
-/
-- BEGIN SPEC
theorem lit_get? : [10, 20, 30][5]? = none :=
-- END SPEC
  rfl

/- SKELETON · safeGet_lt
  1. Expose the body of `safeGet`:                                              R5
  2. Take the `then` branch with `h` (rw's closing `rfl` finishes):             R6
-/
-- BEGIN SPEC
theorem safeGet_lt (l : List Nat) (i : Nat) (h : i < l.length) : safeGet l i = l[i] :=
-- END SPEC
  by unfold safeGet; rw [dif_pos h]

/- SKELETON · safeGet_ge
  1. Expose the body of `safeGet`:                                              R5
  2. Take the `else` branch; its argument `¬ i < l.length` comes from `h`:      R7 with R8
-/
-- BEGIN SPEC
theorem safeGet_ge (l : List Nat) (i : Nat) (h : l.length ≤ i) : safeGet l i = 0 :=
-- END SPEC
  by unfold safeGet; rw [dif_neg (by omega)]

/- SKELETON · get?_eq_some
  1. Replace `safeGet l i` by `l[i]` with the theorem `safeGet_lt` above:       rw [safeGet_lt l i h]
  2. Relate `l[i]?` to `l[i]`:                                                   R9
-/
-- BEGIN SPEC
theorem get?_eq_some (l : List Nat) (i : Nat) (h : i < l.length) : l[i]? = some (safeGet l i) :=
-- END SPEC
  by rw [safeGet_lt l i h]; exact List.getElem?_eq_getElem h

/- SKELETON · get_map_double
  1. Read the statement: `'(by simpa using h)` is the bound of the mapped list. R10, R11
  2. Entry of a mapped list = the function applied to the entry; the leftover
     `(fun x => x * 2) l[i] = l[i] * 2` holds by β-reduction:                   R12
-/
-- BEGIN SPEC
theorem get_map_double (l : List Nat) (i : Nat) (h : i < l.length) :
    (l.map (· * 2))[i]'(by simpa using h) = l[i] * 2 :=
-- END SPEC
  List.getElem_map _

end E059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `safeGet` is a dependent `if` on `i < l.length`: in the `then` branch `h` is the bound that makes `l[i]`
    legal (R1, R2). The two literal lookups just compute (R3, R4).
H2. `safeGet_lt` / `safeGet_ge`: `unfold safeGet`, then pick the branch with `dif_pos` / `dif_neg` (R5–R8).
    `get?_eq_some`: rewrite with `safeGet_lt` first, then R9. `get_map_double`: one lemma, R12.
H3. `safeGet_ge`: `unfold safeGet; rw [dif_neg (by omega)]`. `get?_eq_some`:
    `rw [safeGet_lt l i h]; exact List.getElem?_eq_getElem h`. `get_map_double`: `List.getElem_map _`.
-/
