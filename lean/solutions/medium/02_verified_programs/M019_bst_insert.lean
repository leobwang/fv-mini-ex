/- M019 | BST insert | 15-20 min | inductive tree, inductive invariant, recursive Prop
GOAL
  Prove that inserting into a binary search tree adds exactly the new key and keeps the
  search-tree invariant.

REFERENCE
  -- `mem` and `All` are recursive functions into Prop: unfold them with `simp [mem]`.
  example (x : Nat) : ¬ M019.mem x .leaf := by simp [M019.mem]
  example (p : Nat → Prop) (l r : M019.Tree) (k : Nat) (h : M019.All p (.node l k r)) : p k := h.2.1
  -- Split on the `if`s inside `insert` with `split`, then `simp only [mem, ih]` and `grind`
  -- (omega cannot reason about `mem y l` atoms; grind mixes propositional logic and arithmetic).
  -- A BST proof needs: `All p t → p x → All p (insert x t)`; prove that first.
-/

namespace M019

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

def insert (x : Nat) : Tree → Tree
  | .leaf => .node .leaf x .leaf
  | .node l k r =>
    if x < k then .node (insert x l) k r
    else if k < x then .node l k (insert x r)
    else .node l k r
-- END SPEC

theorem all_insert (p : Nat → Prop) (x : Nat) (t : Tree) (ht : All p t) (hx : p x) :
    All p (insert x t) := by
  induction t with
  | leaf => simp [insert, All, hx]
  | node l k r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := ht
    unfold insert
    split
    · exact ⟨ihl hl, hk, hr⟩
    · split
      · exact ⟨hl, hk, ihr hr⟩
      · exact ⟨hl, hk, hr⟩

-- BEGIN SPEC
theorem mem_insert (x y : Nat) (t : Tree) : mem y (insert x t) ↔ y = x ∨ mem y t :=
-- END SPEC
  by
    induction t with
    | leaf => simp [insert, mem]
    | node l k r ihl ihr =>
      unfold insert
      split
      · simp only [mem, ihl]; grind
      · split
        · simp only [mem, ihr]; grind
        · simp only [mem]; grind

-- BEGIN SPEC
theorem insert_bst (x : Nat) (t : Tree) (h : BST t) : BST (insert x t) :=
-- END SPEC
  by
    induction h with
    | leaf => exact .node trivial trivial .leaf .leaf
    | @node l k r hl hr bl br ihl ihr =>
      unfold insert
      split
      · exact .node (all_insert _ x l hl (by assumption)) hr ihl br
      · split
        · exact .node hl (all_insert _ x r hr (by assumption)) bl ihr
        · exact .node hl hr bl br

end M019

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both proofs follow the shape of `insert`: induction on the tree (or on `h : BST t`), then split the two `if`s.
H2. For `insert_bst`, first prove `all_insert : All p t → p x → All p (insert x t)`.
H3. `induction h with | leaf => exact .node trivial trivial .leaf .leaf | @node l k r hl hr bl br ihl ihr => unfold insert; split; ...` using `all_insert _ x l hl (by assumption)`.
-/
