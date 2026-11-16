/- M035 | Iterative in-order traversal | 10-15 min | explicit stack, termination_by, well-founded recursion, equation lemmas, generalising the stack
GOAL
  The textbook stack-based in-order traversal (push the left spine; pop a node, emit it, push the
  left spine of its right subtree) returns exactly the recursive `inorder` list.

REFERENCE
  -- `loop`'s argument does not shrink structurally, so it is defined by well-founded recursion on
  -- `weight st` (`termination_by`). Such definitions do not compute by `rfl`/`decide`:
  --   example : loop [] = [] := rfl              -- fails
  example : loop [] = [] := by rw [loop]         -- unfold one step with the equation lemma
  #check @loop.eq_2   -- loop ((x, r) :: st) = x :: loop (pushLeft r st)
  #check @List.append_assoc  -- as ++ bs ++ cs = as ++ (bs ++ cs)
  -- `induction t generalizing st with | leaf => _ | node l x r ihl ihr => _`
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

-- BEGIN SPEC
theorem iterInorder_eq (t : Tree) : iterInorder t = inorder t :=
-- END SPEC
  by simp [iterInorder, loop_pushLeft, loop]

end M035

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `iterInorder t = inorder t` is not inductive: after one step the stack is no longer empty, and
    the left subtree's spine sits on top of saved nodes. State what `loop` does on `pushLeft t st` for
    an arbitrary stack `st` underneath, as a helper lemma above the main theorem.
H2. Prove the helper by induction on `t` generalizing `st`. In the `node` case, unfold `pushLeft` once,
    use `ihl`, then unfold one `loop` step (it pops `(x, r)`), then use `ihr`.
H3. Helper: `theorem loop_pushLeft (t : Tree) (st : List (Nat × Tree)) : loop (pushLeft t st) =
    inorder t ++ loop st`. The main theorem is then `loop_pushLeft t []` plus `loop [] = []`.
-/
