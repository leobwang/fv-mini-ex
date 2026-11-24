/- H014 | BST delete | 1-1.5 h | inductive invariant, Option match, helper specs, BST, split at
GOAL
  Deleting a key from a binary search tree (a deleted node is replaced by the minimum of its right
  subtree, removed by `popMin`) keeps the search-tree invariant and removes exactly that key.

GUIDE
  Entries R1–R24: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H014

-- BEGIN SPEC
inductive Tree where
  | leaf
  | node (l : Tree) (k : Nat) (r : Tree)

def mem (x : Nat) : Tree → Prop
  | .leaf => False
  | .node l k r => mem x l ∨ x = k ∨ mem x r

def All (p : Nat → Prop) : Tree → Prop
  | .leaf => True
  | .node l k r => All p l ∧ p k ∧ All p r

inductive BST : Tree → Prop
  | leaf : BST .leaf
  | node {l : Tree} {k : Nat} {r : Tree} :
      All (· < k) l → All (k < ·) r → BST l → BST r → BST (.node l k r)

/-- Remove the minimum: returns it with the rest of the tree (`none` on a leaf). -/
def popMin : Tree → Option (Nat × Tree)
  | .leaf => none
  | .node l k r =>
    match popMin l with
    | none => some (k, r)
    | some (m, l') => some (m, .node l' k r)

def delete (x : Nat) : Tree → Tree
  | .leaf => .leaf
  | .node l k r =>
    if x < k then .node (delete x l) k r
    else if k < x then .node l k (delete x r)
    else
      match popMin r with
      | none => l
      | some (m, r') => .node l m r'
-- END SPEC

/- SKELETON · all_iff   (MILESTONE 1: prove first. popMin_spec, mem_delete and delete_bst use it
   to turn every `All p t` into `∀ y, mem y t → p y`, forward with `rw` (R10), backward with `.2` (R15))
  1. Induction on `t`:                                                       R1
  2. leaf: unfold `All` and `mem`; `simp` closes `True ↔ ∀ y, False → p y`:  R2
  3. node: unfold `All` and `mem`, and rewrite both IHs, in one `simp only`: R2, R3
     the goal is now logic over the atoms `mem y l`, `y = k`, `mem y r`:     R4
-/
-- MILESTONE (optional: change or delete)
theorem all_iff (p : Nat → Prop) (t : Tree) : All p t ↔ ∀ y, mem y t → p y := by
  sorry

/- SKELETON · popMin_none   (MILESTONE 2: used in the `none` arm of popMin_spec and mem_delete)
  1. Case on `t` (no IH needed):                                             R5
  2. leaf: the goal is `leaf = leaf`:                                         rfl
  3. node: unfold `popMin` in `h`, then split the `match popMin l` in `h`:   R2 (at h), R6
     both arms leave `h : some … = none`, which closes the goal:            R7
-/
-- MILESTONE (optional: change or delete)
theorem popMin_none (t : Tree) (h : popMin t = none) : t = .leaf := by
  sorry

/- SKELETON · popMin_spec   (MILESTONE 3: after all_iff and popMin_none. mem_delete and delete_bst
   use it in their last arm, where the root `k` is replaced by the minimum `m` of `r`)
  1. Induction on `t` generalizing `m t'` (the IH is needed at the minimum of `l`, not at `m`;
     `h : BST t` is generalized automatically, so each IH first asks for `BST l` / `BST r`):  R8
  2. leaf: `hp : popMin leaf = some …`: unfold, contradiction:              R2 (at hp), R7
  3. node: invert `h` into `hl hr bl br`; `All` → `∀` in `hl hr`:           R9, R10 (all_iff)
  4. Unfold `popMin` in `hp`, split its `match popMin l`, name the new facts: R2 (at hp), R6, R11
  5. Arm `none`: `l = leaf` by popMin_none:                                 R12
       `hp : some (k, r) = some (m, t')` → substitute `m t'`:               R13, R14
       the triple (`refine ⟨?_, ?_, ?_⟩`): `br`; membership by `simp` with `mem`;
       `.2` of all_iff on `hr`:                                              R15
  6. Arm `some (m', l')`: substitute from `hp` as in 5:                     R13, R14
       IH at `l` (`bl`, `hs`) → `b', hmem, hlt`; `All` → `∀` in `hlt`:      R16, R10
       first:  hmk : m' < k      (`hl` at `m'`; `mem m' l` by `(hmem m').2 (.inl rfl)`):  R15
       triple, part 1: the `BST.node` constructor with `b'`, `br` (R17); its two `All` premises
               by `.2` of all_iff (R15): for `l'`, a key `y` of `l'` is a key of `l`
               (`(hmem y).2 (.inr hy)`), so `hl` bounds it; for `r`, `hr` as it is
       part 2: unfold `mem`, rewrite with `hmem`, close the logic:          R2, R3, R4
       part 3: `.2` of all_iff, then `intro y hy`, unfold `mem` at `hy`:    R15, R18, R2
               three cases (R19): in `l'` → `hlt`; `y = k` → `hmk`; in `r` → R20 with `hmk`, `hr`
-/
-- MILESTONE (optional: change or delete)
theorem popMin_spec (t : Tree) (h : BST t) (m : Nat) (t' : Tree) (hp : popMin t = some (m, t')) :
    BST t' ∧ (∀ y, mem y t ↔ y = m ∨ mem y t') ∧ All (m < ·) t' := by
  sorry

/- SKELETON · mem_delete   (uses all_iff, popMin_none, popMin_spec)
  1. Induction on `t`; leaf: unfold `delete` and `mem`, `simp`:             R1, R2
  2. node: invert `h`; `All` → `∀` in `hl hr`; instantiate both at `y` (optional: `grind`
     can find these instances itself). This is where `BST` is used: `mem y l → y < k` and
     `mem y r → k < y` rule out `y = x` on the wrong side of `k`:          R9, R10, R21
  3. Unfold `delete` (R2), split the first `if` (R22):
       `x < k`: unfold `mem`, rewrite with `ihl bl`, close:                 R2, R3, R4
       else split the second `if` (R22):
         `k < x`: the same with `ihr br`:                                    R2, R3, R4
         else split the `match popMin r` (R23), name the new facts (R11):
           `none`:  `r = leaf` by popMin_none (R12); unfold `mem`, close:   R2, R4
           `some (m, r')`: membership part of popMin_spec r br m r' hs (R16); instantiate
                    `hr` at `m` (R21); unfold `mem` and rewrite with it everywhere (R24); close (R4)
-/
-- BEGIN SPEC
theorem mem_delete (x y : Nat) (t : Tree) (h : BST t) : mem y (delete x t) ↔ mem y t ∧ y ≠ x :=
-- END SPEC
  sorry

/- SKELETON · delete_bst   (uses all_iff, mem_delete, popMin_spec)
  1. Induction on `t`; leaf: the constructor `BST.leaf`:                     R1
  2. node: invert `h` (R9); unfold `delete` (R2); split both `if`s and the `match` (R22, R23).
  3. `x < k`: `BST.node` with a hole for `All (· < k) (delete x l)`, the IH `ihl bl`, `hr`, `br`:  R17
       the hole: `All` → `∀` in `hl` and the goal (R10), `intro y hy` (R18); `mem y (delete x l)`
       gives `mem y l` by `.1` of mem_delete, then `.1` of the `∧` (R15); `hl` finishes
  4. `k < x`: the mirror image, with a hole for `All (k < ·) (delete x r)`: R17, R10, R18, R15
  5. Arm `none`: the result is `l`; `bl` proves it.
  6. Arm `some (m, r')`: popMin_spec r br m r' hs → `b', hmem, hlt` (R16); `All` → `∀` in `hl hr` (R10)
       first:  hkm : k < m       (`hr` at `m`; `mem m r` by `(hmem m).2 (.inl rfl)`):  R15
       then `BST.node`: left premise by `.2` of all_iff and `y < k < m` (R15, R20); right premise `hlt`;
       then `bl`, `b'`:                                                      R17
-/
-- BEGIN SPEC
theorem delete_bst (x : Nat) (t : Tree) (h : BST t) : BST (delete x t) :=
-- END SPEC
  sorry

end H014

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `All` is awkward to use directly. Prove the milestones in order: `all_iff` restates `All p t` as
    "every member satisfies p"; `rw [all_iff] at …` (R10) and `(all_iff _ _).2` (R15) then move between
    the two forms, so everything is about `mem`, which `simp only [mem]` unfolds (R2).
H2. `popMin_spec` by `induction t generalizing m t'` (R8), `cases h` (R9), `simp only [popMin] at hp`
    and `split at hp` (R6). In the `none` arm `l = .leaf` (`popMin_none`, R12). In the `some (m', l')`
    arm the IH gives the minimum `m'` of `l`, which is `< k` and therefore below every key of `r` too.
    `mem_delete` and `delete_bst`: induction on `t`, `cases h`, `simp only [delete]`, then `split` on
    the two `if`s and the `match popMin r` (R22, R23).
H3. `popMin_spec`: `have hmk : m' < k := hl m' ((hmem m').2 (.inl rfl))` after
    `obtain ⟨b', hmem, hlt⟩ := ihl bl _ _ hs`. `mem_delete`: after `rw [all_iff] at hl hr`, `have := hl y; have := hr y`
    makes explicit the facts `grind` uses: `y = x` cannot occur on the wrong side (in the `x < k` branch every key
    of `r` is `> k > x`). In the last arm add `have := hr m` and `simp only [mem, hmem] at *`.
    `delete_bst`, last arm: `have hkm : k < m := hr m ((hmem m).2 (.inl rfl))`; the new root `m` is
    `> k`, hence above all of `l` (`Nat.lt_trans`).
-/
