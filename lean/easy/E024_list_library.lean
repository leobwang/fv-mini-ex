/- E024 | List library facts | 3 min | List.map, List.filter, List.foldl, simp lemmas
GOAL
  Prove standard facts about `map`, `filter` and `foldl` using library lemmas.

REFERENCE
  #check List.length_map      -- (List.map f as).length = as.length
  #check List.length_append   -- (as ++ bs).length = as.length + bs.length
  #check List.length_filter_le  -- (p : α → Bool) (l : List α) : (List.filter p l).length ≤ l.length
  #check List.foldl_append    -- List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l) l'
  #check List.filter_map      -- List.filter p (List.map f l) = List.map f (List.filter (p ∘ f) l)
  example : [1, 2, 3].foldl (· + ·) 0 = 6 := rfl   -- foldl f init list, left to right
-/

-- BEGIN SPEC
theorem map_append_length (f : Nat → Nat) (xs ys : List Nat) :
    ((xs ++ ys).map f).length = xs.length + ys.length :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem filter_le_append (p : Nat → Bool) (xs ys : List Nat) :
    (xs.filter p).length ≤ (xs ++ ys).length :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem foldl_split (f : Nat → Nat → Nat) (a : Nat) (xs ys : List Nat) :
    (xs ++ ys).foldl f a = ys.foldl f (xs.foldl f a) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem filter_after_map (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) :
    (xs.map f).filter p = (xs.filter (fun x => p (f x))).map f :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each statement is one or two library lemmas away; read the `#check` lines.
H2. `filter_le_append`: get the filter bound with `have`, rewrite the append length, then `omega`.
H3. `rw [List.length_map, List.length_append]`; `exact List.foldl_append`; `rw [List.filter_map]; rfl` (`p ∘ f` unfolds to `fun x => p (f x)`).
-/
