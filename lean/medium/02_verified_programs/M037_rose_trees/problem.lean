/- M037 | Rose trees: nested inductives | 15-20 min | nested inductive types, structural recursion through map, recursive theorems, List.map_congr_left
GOAL
  A rose tree node holds a *list* of children. Prove that flattening and mirroring preserve the
  size, and that mirroring twice gives the tree back.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · length_flatten
  1. Split `t` by its one constructor (`induction t` rejects a nested type):  R1
       match t with | .node x cs => …
  2. Call the theorem itself on each child: the induction hypothesis           R2
       ih : ∀ c ∈ cs, c.flatten.length = c.size
  3. Unfold both definitions, then push `length` through `::`, `flatten`,
     and fuse the two maps (one `simp only [...]` can do all of it):          R3, R4, R5, R6
  4. Under the map, replace `List.length ∘ Rose.flatten` by `Rose.size`
     using ih (name `f` and `g`):                                              R7
  5. Close `s + 1 = 1 + s`:                                                    R8
-/
-- BEGIN SPEC
theorem length_flatten (t : Rose) : t.flatten.length = t.size :=
-- END SPEC
  sorry

/- SKELETON · size_mirror
  1. Split `t`:                                                                R1
  2. Induction hypothesis  ih : ∀ c ∈ cs, c.mirror.size = c.size               R2
  3. Unfold `Rose.mirror`, `Rose.size`; move the map inside the reverse,
     drop the reverse under the sum, fuse the maps (one `simp only`):         R3, R9, R10, R6
  4. Replace `Rose.size ∘ Rose.mirror` by `Rose.size` using ih; both sides
     are then equal and `rw` closes the goal:                                  R7
-/
-- BEGIN SPEC
theorem size_mirror (t : Rose) : t.mirror.size = t.size :=
-- END SPEC
  sorry

/- SKELETON · mirror_mirror
  1. Split `t`:                                                                R1
  2. Induction hypothesis  ih : ∀ c ∈ cs, c.mirror.mirror = c                  R2
  3. Unfold `Rose.mirror` (twice, one `simp only`); move the outer map inside
     the reverse, cancel the two reverses, fuse the maps:                      R3, R9, R11, R6
  4. Replace `Rose.mirror ∘ Rose.mirror` by `id` using ih, then drop `map id`
     (the last `rw` closes the goal):                                          R7 → R12
-/
-- BEGIN SPEC
theorem mirror_mirror (t : Rose) : t.mirror.mirror = t :=
-- END SPEC
  sorry

end M037

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `induction t` is rejected for a nested inductive. Make each theorem recursive (R1, R2):
    `match t with | .node x cs =>`, then `have ih : ∀ c ∈ cs, … := fun c _ => <this theorem> c`.
    Unfold with `simp only` until the goal has a single `List.map (g ∘ f) cs`; `ih` controls exactly that.
H2. Per theorem, one `simp only [defs, lemmas]`: `length_flatten` needs R3–R6 (`List.length_cons`,
    `List.length_flatten`, `List.map_map`), `size_mirror` R3, R9, R10, R6, `mirror_mirror` R3, R9, R11, R6.
    Then `rw [List.map_congr_left (f := …) (g := …) ih]` (R7), naming `f` as it appears in the goal.
H3. `size_mirror`: `rw [List.map_congr_left (f := Rose.size ∘ Rose.mirror) (g := Rose.size) ih]`.
    `length_flatten`: `(f := List.length ∘ Rose.flatten) (g := Rose.size)`, then `omega`.
    `mirror_mirror`: `(f := Rose.mirror ∘ Rose.mirror) (g := id)`, then `List.map_id`.
-/
