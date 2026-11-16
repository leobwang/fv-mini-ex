/- M037 | Rose trees: nested inductives | 15-20 min | nested inductive types, structural recursion through map, recursive theorems, List.map_congr_left
GOAL
  A rose tree node holds a *list* of children. Prove that flattening and mirroring preserve the
  size, and that mirroring twice gives the tree back.

REFERENCE
  -- `induction t` rejects nested inductives. Write a recursive theorem instead: it calls itself
  -- on each child, and Lean checks the recursion is structural, as for a recursive def:
  --   theorem thm (t : Rose) : P t := by
  --     match t with
  --     | .node x cs =>
  --       have ih : ∀ c ∈ cs, P c := fun c _ => thm c
  --       ...
  #check @List.map_congr_left -- (∀ a ∈ l, f a = g a) → l.map f = l.map g
  #check @List.map_map        -- (l.map f).map g = l.map (g ∘ f)
  #check @List.length_flatten -- L.flatten.length = (L.map List.length).sum
  -- also useful: List.map_reverse, List.sum_reverse, List.reverse_reverse, List.map_id
-/

namespace M037

-- BEGIN SPEC
/-- A rose tree: each node has a list of children (a nested inductive type). -/
inductive Rose where
  | node (x : Nat) (cs : List Rose)

def Rose.size : Rose → Nat
  | .node _ cs => 1 + (cs.map Rose.size).sum

def Rose.flatten : Rose → List Nat
  | .node x cs => x :: (cs.map Rose.flatten).flatten

def Rose.mirror : Rose → Rose
  | .node x cs => .node x (cs.map Rose.mirror).reverse
-- END SPEC

-- BEGIN SPEC
theorem length_flatten (t : Rose) : t.flatten.length = t.size :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem size_mirror (t : Rose) : t.mirror.size = t.size :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mirror_mirror (t : Rose) : t.mirror.mirror = t :=
-- END SPEC
  sorry

end M037

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the definitions with `simp only [...]` and push `map` through `reverse` and `map`; the
    goal then compares `cs.map (g ∘ f)` with `cs.map h`, which is exactly what `ih` controls.
H2. Turn `ih` into an equation of maps with `List.map_congr_left`. Lean cannot guess `f` and `g`
    from `ih` alone, so name them: `List.map_congr_left (f := Rose.size ∘ Rose.mirror) (g := Rose.size) ih`.
H3. `mirror_mirror`: after `simp only [Rose.mirror, List.map_reverse, List.reverse_reverse, List.map_map]`,
    rewrite with `List.map_congr_left (f := Rose.mirror ∘ Rose.mirror) (g := id) ih`.
-/
