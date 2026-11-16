/- M014 | A hand-built state monad and tree relabelling | 15-20 min | Monad instance, LawfulMonad, do-notation, induction generalizing, List.range'
GOAL
  Prove that the hand-built state monad `St σ α := σ → α × σ` is a `LawfulMonad`. Then verify Hutton's
  `relabel`: it numbers the leaves `s, s+1, …` left to right, so the final counter is `s + size` and
  the labels, read in order, are `List.range' s size` (the list `[s, s+1, …, s+size-1]`).

REFERENCE
  -- LawfulMonad.mk' (m) (id_map) (pure_bind) (bind_assoc) : LawfulMonad m   (other laws: automatic)
  #check @LawfulMonad.mk'   -- the three laws are the explicit arguments after `m`
  example : List.range' 3 4 = [3, 4, 5, 6] := rfl
  #check @List.range'_append_1  -- range' s m ++ range' (s + m) n = range' s (m + n)   (step 1)
  -- `simp only [relabel, bind, pure]` unfolds a `do` block over this hand-made instance;
  -- after that, `(relabel t s).2` is a plain pair projection you can rewrite.
  -- `induction t generalizing s with | leaf => _ | node l r ihl ihr => _`
NOTE: Give `LawfulMonad.mk'` its three laws as arguments; `apply LawfulMonad.mk'` turns the automatic ones into goals.
-/

namespace M014

-- BEGIN SPEC
/-- The state monad, built by hand: a computation reads a state and returns a value and a new state. -/
def St (σ α : Type) : Type := σ → α × σ

instance stMonad {σ : Type} : Monad (St σ) where
  pure a := fun s => (a, s)
  bind m f := fun s => f (m s).1 (m s).2

def St.get {σ : Type} : St σ σ := fun s => (s, s)
def St.set {σ : Type} (s : σ) : St σ Unit := fun _ => ((), s)
-- END SPEC

-- BEGIN SPEC
instance stLawful {σ : Type} : LawfulMonad (St σ) :=
-- END SPEC
  sorry

-- BEGIN SPEC
inductive Tree where
  | leaf
  | node (l : Tree) (r : Tree)

inductive LTree where
  | leaf (n : Nat)
  | node (l r : LTree)

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

def LTree.labels : LTree → List Nat
  | .leaf n => [n]
  | .node l r => l.labels ++ r.labels

/-- Hand out the next fresh number. -/
def fresh : St Nat Nat := do
  let n ← St.get
  St.set (n + 1)
  return n

/-- Replace every leaf by a fresh label, left to right. -/
def relabel : Tree → St Nat LTree
  | .leaf => do
    let n ← fresh
    return .leaf n
  | .node l r => do
    let l' ← relabel l
    let r' ← relabel r
    return .node l' r'

theorem relabel_spec (t : Tree) (s : Nat) :
    (relabel t s).2 = s + t.size ∧ (relabel t s).1.labels = List.range' s t.size :=
-- END SPEC
  sorry

end M014

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the instance by hand on each law: both sides are functions `σ → _ × σ` that compute the same pair.
    For `relabel_spec`, the right subtree starts from the counter the left subtree left behind.
H2. The laws hold definitionally, so each is `rfl` (as a `fun`). For `relabel_spec`, induct on `t`
    generalizing `s`, and in the `node` case use `ihl s` and `ihr (relabel l s).2`.
H3. Each law is `rfl` once wrapped in as many `fun _ =>` binders as it has arguments; pass the three to
    `LawfulMonad.mk' (St σ)`. Node case: `simp only [relabel, bind, pure] at *`, then `omega` for the
    counter; for the labels rewrite with both IHs and `ihl`'s counter equation, unfold `Tree.size`, and
    finish with `simp` (it knows `List.range'_append_1`).
-/
