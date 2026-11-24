/- H014 | BST delete | 1-1.5 h | inductive invariant, Option match, helper specs, BST, split at
GOAL
  Deleting a key from a binary search tree (a deleted node is replaced by the minimum of its right
  subtree, removed by `popMin`) keeps the search-tree invariant and removes exactly that key.

REFERENCE
  -- `Tree`, `mem`, `All`, `BST` are M019's. `All p t` says `p` holds at every key of `t`.
  -- `(· < k)` is `fun y => y < k`, so `All (· < k) l`: every key of `l` is below `k`.
  example (l r : H014.Tree) (k : Nat) (h : H014.BST (.node l k r)) : H014.BST l := by
    cases h with | node hl hr bl br => exact bl     -- invert a BST proof: the four premises
  -- `split at hp` cases on the `match popMin l with ...` inside a hypothesis `hp : popMin .. = ..`.
  example (a b : Nat) (p : Nat × Nat) (h : some p = some (a, b)) : p.1 = a := by simp at h; simp [h]
  example (P Q R : Prop) (h : P ∨ Q ∨ R) : R ∨ Q ∨ P := by rcases h with h | h | h <;> simp [h]
  #check @Nat.lt_trans  -- n < m → m < k → n < k
  -- `induction t generalizing m t'` keeps the IH general when the statement mentions `popMin t = some (m, t')`.
  -- `omega` closes `y ≠ x` from `y < k` and `x = k`, but cannot see inside `mem y l`: `grind` mixes both.
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

-- MILESTONE (optional: change or delete)
theorem all_iff (p : Nat → Prop) (t : Tree) : All p t ↔ ∀ y, mem y t → p y := by
  induction t with
  | leaf => simp [All, mem]
  | node l k r ihl ihr => simp only [All, mem, ihl, ihr]; grind

-- MILESTONE (optional: change or delete)
theorem popMin_none (t : Tree) (h : popMin t = none) : t = .leaf := by
  cases t with
  | leaf => rfl
  | node l k r => simp only [popMin] at h; split at h <;> simp at h

-- MILESTONE (optional: change or delete)
theorem popMin_spec (t : Tree) (h : BST t) (m : Nat) (t' : Tree) (hp : popMin t = some (m, t')) :
    BST t' ∧ (∀ y, mem y t ↔ y = m ∨ mem y t') ∧ All (m < ·) t' := by
  induction t generalizing m t' with
  | leaf => simp [popMin] at hp
  | node l k r ihl ihr =>
    cases h with
    | node hl hr bl br =>
    rw [all_iff] at hl hr
    simp only [popMin] at hp
    split at hp
    · rename_i hn
      obtain rfl := popMin_none l hn
      simp at hp; obtain ⟨rfl, rfl⟩ := hp
      exact ⟨br, fun y => by simp [mem], (all_iff _ _).2 hr⟩
    · rename_i m' l' hs
      simp at hp; obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨b', hmem, hlt⟩ := ihl bl _ _ hs
      rw [all_iff] at hlt
      have hmk : m' < k := hl m' ((hmem m').2 (.inl rfl))
      refine ⟨.node ((all_iff _ _).2 fun y hy => hl y ((hmem y).2 (.inr hy))) ((all_iff _ _).2 hr) b' br,
        fun y => by simp only [mem, hmem]; grind, (all_iff _ _).2 fun y hy => ?_⟩
      simp only [mem] at hy
      rcases hy with hy | rfl | hy
      · exact hlt y hy
      · exact hmk
      · exact Nat.lt_trans hmk (hr y hy)

-- BEGIN SPEC
theorem mem_delete (x y : Nat) (t : Tree) (h : BST t) : mem y (delete x t) ↔ mem y t ∧ y ≠ x :=
-- END SPEC
  by
    induction t with
    | leaf => simp [delete, mem]
    | node l k r ihl ihr =>
      cases h with
      | node hl hr bl br =>
      rw [all_iff] at hl hr
      have := hl y; have := hr y
      simp only [delete]
      split
      · simp only [mem, ihl bl]; grind
      · split
        · simp only [mem, ihr br]; grind
        · split
          · rename_i hn
            obtain rfl := popMin_none r hn
            simp only [mem]; grind
          · rename_i m r' hs
            obtain ⟨_, hmem, _⟩ := popMin_spec r br m r' hs
            have := hr m
            simp only [mem, hmem] at *; grind

-- BEGIN SPEC
theorem delete_bst (x : Nat) (t : Tree) (h : BST t) : BST (delete x t) :=
-- END SPEC
  by
    induction t with
    | leaf => exact .leaf
    | node l k r ihl ihr =>
      cases h with
      | node hl hr bl br =>
      simp only [delete]
      split
      · refine .node ?_ hr (ihl bl) br
        rw [all_iff] at hl ⊢; intro y hy; exact hl y ((mem_delete x y l bl).1 hy).1
      · split
        · refine .node hl ?_ bl (ihr br)
          rw [all_iff] at hr ⊢; intro y hy; exact hr y ((mem_delete x y r br).1 hy).1
        · split
          · exact bl
          · rename_i m r' hs
            obtain ⟨b', hmem, hlt⟩ := popMin_spec r br m r' hs
            rw [all_iff] at hl hr
            -- WHY: the new root `m` came from `r`, so `k < m`; that puts all of `l` below it.
            have hkm : k < m := hr m ((hmem m).2 (.inl rfl))
            exact .node ((all_iff _ _).2 fun y hy => Nat.lt_trans (hl y hy) hkm) hlt bl b'

end H014

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `All` is awkward to use directly; restate it as "every member satisfies p" (`all_iff`) and rewrite
    with it. Then everything is about `mem`, which `simp only [mem]` unfolds.
H2. Prove `popMin_spec` first, by induction on `t` generalizing `m t'`: case on `popMin l` with
    `split at hp`; in the `none` case `l = .leaf` (`popMin_none`). The minimum of `l` is `< k`, so it
    is below everything in `r` too. Then `mem_delete` and `delete_bst` go by induction on `t`,
    `cases h`, and `split` on the two `if`s and the `match popMin r`.
H3. Where `BST t` is needed in `mem_delete`: in the `x < k` branch, `y = x` cannot occur in `r` since
    every key of `r` is `> k > x`. In the root case of `delete_bst`, get
    `obtain ⟨b', hmem, hlt⟩ := popMin_spec r br m r' hs`; the new root `m` is `> k`, hence above all of `l`.
-/
