/- M014 | A hand-built state monad and tree relabelling | 15-20 min | Monad instance, LawfulMonad, do-notation, induction generalizing, List.range'
GOAL
  Prove that the hand-built state monad `St σ α := σ → α × σ` is a `LawfulMonad`. Then verify Hutton's
  `relabel`: it numbers the leaves `s, s+1, …` left to right, so the final counter is `s + size` and
  the labels, read in order, are `List.range' s size` (the list `[s, s+1, …, s+size-1]`).

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · stLawful
  1. The body is a term: `LawfulMonad.mk' (St σ)` applied to the three laws
     id_map, pure_bind, bind_assoc (the other five fields fill themselves):     R1
  2. Each law holds by computation: one `fun … => rfl` per law, with one `_`
     per explicit binder of that law (1, 2, 3):                                 R4 (= R2 then R3)
-/
-- BEGIN SPEC
instance stLawful {σ : Type} : LawfulMonad (St σ) :=
-- END SPEC
  sorry

/- SKELETON · relabel_spec
  1. Induct on `t`, generalizing the start counter `s`:                          R5
  2. `leaf`: one `simp [...]` naming everything the leaf computation passes
     through (relabel, fresh, bind, pure, St.get, St.set, LTree.labels,
     Tree.size); it finishes with `List.range' s 1 = [s]` by itself:            R7, R11
  3. `node`: instantiate both hypotheses, the right one at the counter the
     left subtree left behind:
       hl1, hl2 from `ihl s`;  hr1, hr2 from `ihr (relabel l s).2`              R6
  4. Unfold the node's `do` block (in the hypotheses too):                       R7
  5. Split the `∧`:                                                              refine ⟨?_, ?_⟩
  6. Counter: rw [hr1, hl1], unfold `Tree.size`, then the arithmetic:            R8, R9
  7. Labels: unfold `LTree.labels`, rw [hl2, hr2, hl1], unfold `Tree.size`,
     join the two ranges:                                                        R8, R8, R10
-/
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
H1. `St σ α` is a function type and `pure`, `bind` are plain `fun`s, so every monad law is true by
    computation (`rfl`, R3). In `relabel_spec` the counter moves: the right subtree starts where the left
    one stopped, so the induction hypotheses must hold for every start counter.
H2. Instance: `LawfulMonad.mk' (St σ)` with the three laws as arguments, each a `fun … => rfl` (R1, R4);
    not `apply`, which leaves the five automatic fields as goals. Theorem: `induction t generalizing s`;
    leaf by one `simp` with all the names; node: instantiate `ihl s` and `ihr (relabel l s).2`, unfold the
    `do` block with `simp only [relabel, bind, pure] at *`, split, counter by `omega`, labels by
    `List.range'_append_1`.
H3. Laws: `fun _ => rfl`, `fun _ _ => rfl`, `fun _ _ _ => rfl`. Node case:
    `obtain ⟨hl1, hl2⟩ := ihl s` and `obtain ⟨hr1, hr2⟩ := ihr (relabel l s).2`. Counter: rewrite with
    `hr1` before `hl1`, unfold `Tree.size`, `omega`. Labels: unfold `LTree.labels`, rewrite with `hl2`, `hr2`,
    then `hl1` (so the second range starts at `s + l.size`), unfold `Tree.size`, `List.range'_append_1`.
-/
