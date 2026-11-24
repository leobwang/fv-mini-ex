/- M035 | Iterative in-order traversal | 10-15 min | explicit stack, termination_by, well-founded recursion, equation lemmas, generalising the stack
GOAL
  The textbook stack-based in-order traversal (push the left spine; pop a node, emit it, push the
  left spine of its right subtree) returns exactly the recursive `inorder` list.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M035

-- BEGIN SPEC
inductive Tree where
  | leaf
  | node (l : Tree) (x : Nat) (r : Tree)

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def inorder : Tree → List Nat
  | .leaf => []
  | .node l x r => inorder l ++ x :: inorder r

/-- Push the left spine of `t`: each node is saved with its right subtree. -/
def pushLeft : Tree → List (Nat × Tree) → List (Nat × Tree)
  | .leaf, st => st
  | .node l x r, st => pushLeft l ((x, r) :: st)

/-- Termination measure: total number of nodes still on the stack (saved node + its right subtree). -/
def weight (st : List (Nat × Tree)) : Nat := (st.map (fun p => p.2.size + 1)).sum

theorem weight_pushLeft (t : Tree) (st : List (Nat × Tree)) :
    weight (pushLeft t st) = t.size + weight st := by
  induction t generalizing st with
  | leaf => simp [pushLeft, Tree.size]
  | node l x r ihl _ => rw [pushLeft, ihl]; simp [weight, Tree.size]; omega

/-- The iterative traversal: pop a node, emit it, push its right subtree's left spine. -/
def loop : List (Nat × Tree) → List Nat
  | [] => []
  | (x, r) :: st => x :: loop (pushLeft r st)
termination_by st => weight st
decreasing_by rw [weight_pushLeft]; simp [weight]

def iterInorder (t : Tree) : List Nat := loop (pushLeft t [])
-- END SPEC

-- Helper (the generalised invariant): what `loop` does with a freshly pushed spine, for any stack `st`.
theorem loop_pushLeft (t : Tree) (st : List (Nat × Tree)) :
    loop (pushLeft t st) = inorder t ++ loop st := by
  induction t generalizing st with
  | leaf => rfl
  | node l x r ihl ihr => rw [pushLeft, ihl, loop, ihr]; simp [inorder]

/- SKELETON · iterInorder_eq   (prove the MILESTONE helper first, above this theorem)
  Why a helper: `iterInorder t` is `loop (pushLeft t [])`, but after the first pop the stack is no
  longer `[]`, so induction on this statement gets stuck. Generalise the stack.
  1. MILESTONE `loop_pushLeft (t : Tree) (st : List (Nat × Tree))`: an equation saying what
     `loop (pushLeft t st)` emits for ANY stack `st` underneath (all of `t`, then what `st` gives).
     Its proof:
       induction on `t`, generalizing `st`                                       R1
       leaf: both sides unfold (structural definitions only) to the same list    R2
       node l x r:
         unfold one `pushLeft` step: the stack becomes `(x, r) :: st`            R3
         use `ihl` at that stack                                                 R4
         pop `(x, r)`: one step of the well-founded `loop`                       R5
         use `ihr` at the stack `st`                                             R4
         unfold `inorder`, reassociate `++`, close                               R8 (R6, R7)
  2. iterInorder_eq, using the milestone at `st := []`:
       unfold `iterInorder` (non-recursive definition)                           rw [iterInorder]
       rewrite with the milestone                                                R4
       `loop [] = []`                                                            R9
       drop `++ []`                                                              R10
-/
-- BEGIN SPEC
theorem iterInorder_eq (t : Tree) : iterInorder t = inorder t :=
-- END SPEC
  by simp [iterInorder, loop_pushLeft, loop]

end M035

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `iterInorder t = inorder t` is not inductive: after one step the stack is no longer empty, and
    the left subtree's spine sits on top of saved nodes. State what `loop` does on `pushLeft t st` for
    an arbitrary stack `st` underneath, as a helper lemma above the main theorem (SKELETON step 1).
H2. Prove the helper by `induction t generalizing st` (R1). The `leaf` case is `rfl` (R2). In the
    `node` case: `rw [pushLeft]`, then `ihl`, then `rw [loop]` (it pops `(x, r)`; `loop` is well-founded,
    so only its equation lemmas unfold it), then `ihr`, and close with `simp [inorder]`. The main
    theorem is the helper at `st := []` plus `loop [] = []` and `List.append_nil`.
H3. Helper: `theorem loop_pushLeft (t : Tree) (st : List (Nat × Tree)) : loop (pushLeft t st) =
    inorder t ++ loop st`; node case `rw [pushLeft, ihl, loop, ihr]; simp [inorder]`.
-/
