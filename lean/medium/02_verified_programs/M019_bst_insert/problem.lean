/- M019 | BST insert | 15-20 min | inductive tree, inductive invariant, recursive Prop
GOAL
  Prove that inserting into a binary search tree adds exactly the new key and keeps the
  search-tree invariant.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · mem_insert
  1. Induction on the tree `t`:                                                R1
  2. `leaf`: unfold `insert` and `mem` on the constructors; `simp` closes it:  R2
  3. `node l k r ihl ihr`:
       unfold the one call `insert x (l.node k r)` → two nested `if`s:         R3
       split `x < k`; in the `isFalse` goal split `k < x` (three goals):       R4, R4
       in each: unfold `mem` on the nodes and rewrite with the IH of the
       subtree that changed (`ihl`, `ihr`, or none in the third goal):         R2 + R5
       reorder the `∨`s; the third goal also needs `x = k` from the `h✝`s:     R6
-/
-- BEGIN SPEC
theorem mem_insert (x y : Nat) (t : Tree) : mem y (insert x t) ↔ y = x ∨ mem y t :=
-- END SPEC
  sorry

/- SKELETON · insert_bst   (milestone first: `all_insert`)
  0. MILESTONE, stated and proved before this theorem (outside the spec):
       all_insert (p : Nat → Prop) (x : Nat) (t : Tree) (ht : All p t) (hx : p x) :
         All p (insert x t)
     proof: induction on `t` (`ht` is carried into the IHs):                   R1
       `leaf`: `simp` with `insert`, `All`, `hx`                               R2
       `node`: take `ht` apart into `hl hk hr`:                                R7
               unfold `insert`, split both `if`s:                              R3, R4, R4
               rebuild `All p (…)` from the parts, `ihl hl` / `ihr hr`:        R8
  1. Induction on the proof `h : BST t`, naming the implicit `l k r` with `@`: R9
  2. `leaf`: `insert x .leaf` computes to the one-node tree, so `.node` applies
     with no unfolding; both `All` facts are `True`:                           R10
  3. `node`: unfold `insert`, split both `if`s:                                R3, R4, R4
       `x < k`:  `.node` with `all_insert` for the new left subtree; its
                 `p` is inferred and `p x` is the `h✝ : x < k`:                R10, R12, R11
       `k < x`:  the mirror image on the right subtree:                        R10, R12, R11
       else:     the tree is unchanged:                                        R10
-/
-- BEGIN SPEC
theorem insert_bst (x : Nat) (t : Tree) (h : BST t) : BST (insert x t) :=
-- END SPEC
  sorry

end M019

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both proofs follow the shape of `insert`: induction (on `t` for `mem_insert`, on the proof
    `h : BST t` for `insert_bst`), then `unfold insert` and `split` the two `if`s: three cases.
H2. `mem_insert`: in each case `simp only [mem, ihl]` (or `ihr`, or neither), then `grind`, which also
    derives `x = k` in the last case. `insert_bst`: first prove the milestone
    `all_insert : All p t → p x → All p (insert x t)` (induction on `t`, `obtain ⟨hl, hk, hr⟩ := ht`,
    split, rebuild with `⟨_, _, _⟩`).
H3. `insert_bst`: `induction h with | leaf => exact .node trivial trivial .leaf .leaf
    | @node l k r hl hr bl br ihl ihr => …`; in the `x < k` case
    `exact .node (all_insert _ x l hl (by assumption)) hr ihl br`.
-/
