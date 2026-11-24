/- E024 | List library facts | 3 min | List.map, List.filter, List.foldl, simp lemmas
GOAL
  Prove standard facts about `map`, `filter` and `foldl` using library lemmas.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · map_append_length
  1. Peel the outer `map` off the left side's length:                       R1
       left over: `(xs ++ ys).length = xs.length + ys.length`
  2. Expand the length of the append; both sides now agree and `rw`
     closes the goal by itself:                                              R2
-/
-- BEGIN SPEC
theorem map_append_length (f : Nat → Nat) (xs ys : List Nat) :
    ((xs ++ ys).map f).length = xs.length + ys.length :=
-- END SPEC
  sorry

/- SKELETON · filter_le_append
  1. Add the library bound for `xs` to the context:                          R3
       h : (List.filter p xs).length ≤ xs.length
  2. Expand the right side's length:                                         R2
       left over: `(List.filter p xs).length ≤ xs.length + ys.length`
  3. Linear arithmetic from `h`:                                             R4
-/
-- BEGIN SPEC
theorem filter_le_append (p : Nat → Bool) (xs ys : List Nat) :
    (xs.filter p).length ≤ (xs ++ ys).length :=
-- END SPEC
  sorry

/- SKELETON · foldl_split
  1. The statement is one library lemma whose arguments are all implicit;
     its bare name proves the goal (term mode, or `exact` in tactic mode):   R5
-/
-- BEGIN SPEC
theorem foldl_split (f : Nat → Nat → Nat) (a : Nat) (xs ys : List Nat) :
    (xs ++ ys).foldl f a = ys.foldl f (xs.foldl f a) :=
-- END SPEC
  sorry

/- SKELETON · filter_after_map
  1. Move the filter inside the map on the left side:                        R6
       left over: `List.map f (List.filter (p ∘ f) xs)
                     = List.map f (List.filter (fun x => p (f x)) xs)`
  2. `p ∘ f` unfolds to `fun x => p (f x)`:                                  R7
-/
-- BEGIN SPEC
theorem filter_after_map (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. No induction: each statement is one or two library lemmas away. Read each left side from the
    outside in (`length` of `map` of `++`, …) and look up the lemma named after that shape (R1–R6).
H2. `map_append_length`: rewrite `map` away, then `++` (R1, R2). `filter_le_append`: `have` the filter
    bound, rewrite the append length, `omega` (R3, R2, R4). `foldl_split`: the lemma itself (R5).
    `filter_after_map`: rewrite, then `rfl` for `p ∘ f` (R6, R7).
H3. `rw [List.length_map, List.length_append]`; `have h := List.length_filter_le p xs`;
    `List.foldl_append`; `rw [List.filter_map]` then `rfl`.
-/
