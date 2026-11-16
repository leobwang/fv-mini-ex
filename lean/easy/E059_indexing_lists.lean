/- E059 | Indexing lists | 2-3 min | getElem, xs[i], xs[i]'h, xs[i]?, dependent if
GOAL
  Implement a total `safeGet` (out-of-range index gives 0) with a dependent `if`, and meet the
  indexing forms `l[i]` (bound proved automatically), `l[i]'h` (bound given by you) and `l[i]?` (an `Option`).

REFERENCE
  example (xs : List Nat) (i : Nat) (h : i < xs.length) : Nat := xs[i]   -- bound found from context
  example (xs : List Nat) (h : 0 < xs.length) : Nat := xs[0]'h       -- pass the bound proof explicitly
  example : [10, 20, 30][7]? = none := rfl     -- `xs[i]? : Option α` never fails (`[..][1]? = some 20`)
  example : [10, 20, 30][7]! = 0 := rfl        -- `xs[i]!` falls back to `default` (and panics at runtime)
  example (xs : List Nat) (i : Nat) : Nat := if h : i < xs.length then xs[i] else 0  -- `h` named in branches
  #check @dif_pos   -- (hc : c) : (if h : c then t h else e h) = t hc   (`dif_neg` for ¬c)
  #check @List.getElem_map   -- (List.map f l)[i] = f l[i]
  #check @List.getElem?_eq_getElem   -- (h : i < l.length) : l[i]? = some l[i]
-/

namespace E059

-- BEGIN SPEC
def safeGet (l : List Nat) (i : Nat) : Nat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem lit_get : [10, 20, 30][1] = 20 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem lit_get? : [10, 20, 30][5]? = none :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem safeGet_lt (l : List Nat) (i : Nat) (h : i < l.length) : safeGet l i = l[i] :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem safeGet_ge (l : List Nat) (i : Nat) (h : l.length ≤ i) : safeGet l i = 0 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem get?_eq_some (l : List Nat) (i : Nat) (h : i < l.length) : l[i]? = some (safeGet l i) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem get_map_double (l : List Nat) (i : Nat) (h : i < l.length) :
    (l.map (· * 2))[i]'(by simpa using h) = l[i] * 2 :=
-- END SPEC
  sorry

end E059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `safeGet` is the dependent `if` from the card: in the `then` branch `h : i < l.length` makes `l[i]` legal.
H2. Literal lookups compute (`rfl`). For `safeGet_lt`/`safeGet_ge`, unfold `safeGet` and pick the branch with
    `dif_pos`/`dif_neg` (or let `simp [safeGet, h]` do it). `get?_eq_some`: rewrite with `safeGet_lt` first.
H3. `safeGet_ge`: `unfold safeGet; rw [dif_neg (by omega)]`; `get?_eq_some`:
    `rw [safeGet_lt l i h]; exact List.getElem?_eq_getElem h`; `get_map_double`: `List.getElem_map _` (or `simp`).
-/
