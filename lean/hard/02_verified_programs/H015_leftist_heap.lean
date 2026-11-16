/- H015 | Leftist heap | 1.5-2 h | priority queue, rank invariant, List.Perm, fun_induction
GOAL
  A leftist heap is a heap-ordered binary tree whose right spine is short. Prove the priority-queue
  API correct (merge/insert/deleteMin keep the invariants and the elements, findMin is the minimum)
  and the logarithmic bound `2 ^ rank ≤ size + 1` that makes merge fast.

REFERENCE
  #check List.perm_iff_count  -- l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂   (then `omega` on counts)
  #check List.count_append    -- count a (l₁ ++ l₂) = count a l₁ + count a l₂
  #check List.count_cons      -- count a (b :: l) = count a l + if (b == a) = true then 1 else 0
  #check List.Perm.cons       -- (x : α) : l₁ ~ l₂ → x :: l₁ ~ x :: l₂
  #check List.perm_append_comm   -- l₁ ++ l₂ ~ l₂ ++ l₁
  #check Nat.pow_le_pow_right    -- n > 0 → m ≤ k → n ^ m ≤ n ^ k
  -- fun_induction merge h1 h2 generalizing lo with | case1 .. | case2 .. | case3 .. ih | case4 .. ih
  -- (case3/case4 are the `x ≤ y` / `¬ x ≤ y` branches; `merge` terminates lexicographically)
  -- `unfold mkNode; split` to case on the rank comparison inside `mkNode`.
NOTE: `l₁ ~ l₂` is `List.Perm l₁ l₂` (same elements with multiplicity); `HeapOrd lo h` carries a lower bound `lo`.
-/

namespace H015

-- BEGIN SPEC
/-- Leftist heap: each node caches its rank (the length of its right spine). -/
inductive Heap where
  | leaf
  | node (rk : Nat) (x : Nat) (l r : Heap)

def Heap.rank : Heap → Nat
  | .leaf => 0
  | .node rk _ _ _ => rk

/-- Build a node, putting the higher-rank child on the left. -/
def mkNode (x : Nat) (a b : Heap) : Heap :=
  if b.rank ≤ a.rank then .node (b.rank + 1) x a b else .node (a.rank + 1) x b a

/-- Merge along the right spines, keeping the smaller root on top. -/
def merge : Heap → Heap → Heap
  | .leaf, h => h
  | h, .leaf => h
  | .node r1 x l1 r1', .node r2 y l2 r2' =>
    if x ≤ y then mkNode x l1 (merge r1' (.node r2 y l2 r2'))
    else mkNode y l2 (merge (.node r1 x l1 r1') r2')

def insert (x : Nat) (h : Heap) : Heap := merge (.node 1 x .leaf .leaf) h

def findMin : Heap → Option Nat
  | .leaf => none
  | .node _ x _ _ => some x

def deleteMin : Heap → Heap
  | .leaf => .leaf
  | .node _ _ l r => merge l r

def toList : Heap → List Nat
  | .leaf => []
  | .node _ x l r => x :: (toList l ++ toList r)

/-- Every element is ≥ `lo`, and every node is ≤ everything below it. -/
def HeapOrd : Nat → Heap → Prop
  | _, .leaf => True
  | lo, .node _ x l r => lo ≤ x ∧ HeapOrd x l ∧ HeapOrd x r

/-- Ranks are cached correctly and the left child's rank is ≥ the right child's. -/
def Leftist : Heap → Prop
  | .leaf => True
  | .node rk _ l r => rk = r.rank + 1 ∧ r.rank ≤ l.rank ∧ Leftist l ∧ Leftist r

def IsHeap (h : Heap) : Prop := HeapOrd 0 h ∧ Leftist h
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem mkNode_perm (x : Nat) (a b : Heap) :
    (toList (mkNode x a b)).Perm (x :: (toList a ++ toList b)) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem merge_heapOrd (lo : Nat) (h1 h2 : Heap) (o1 : HeapOrd lo h1) (o2 : HeapOrd lo h2) :
    HeapOrd lo (merge h1 h2) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem mkNode_leftist (x : Nat) (a b : Heap) (la : Leftist a) (lb : Leftist b) :
    Leftist (mkNode x a b) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem heapOrd_le {lo : Nat} {h : Heap} (o : HeapOrd lo h) : ∀ y ∈ toList h, lo ≤ y := by
  sorry

-- MILESTONE (optional: change or delete)
theorem heapOrd_weaken {lo : Nat} {h : Heap} (o : HeapOrd lo h) : HeapOrd 0 h := by
  sorry

-- BEGIN SPEC
theorem merge_spec (h1 h2 : Heap) (w1 : IsHeap h1) (w2 : IsHeap h2) :
    IsHeap (merge h1 h2) ∧ (toList (merge h1 h2)).Perm (toList h1 ++ toList h2) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem insert_spec (x : Nat) (h : Heap) (w : IsHeap h) :
    IsHeap (insert x h) ∧ (toList (insert x h)).Perm (x :: toList h) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem findMin_spec (h : Heap) (m : Nat) (w : IsHeap h) (hm : findMin h = some m) :
    m ∈ toList h ∧ ∀ y ∈ toList h, m ≤ y :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem deleteMin_spec (h : Heap) (m : Nat) (w : IsHeap h) (hm : findMin h = some m) :
    IsHeap (deleteMin h) ∧ (m :: toList (deleteMin h)).Perm (toList h) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem rank_bound (h : Heap) (w : Leftist h) : 2 ^ h.rank ≤ (toList h).length + 1 :=
-- END SPEC
  sorry

end H015

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything about `merge` is one `fun_induction merge h1 h2`; everything about `mkNode` is
    `unfold mkNode; split`. Prove the order, rank and permutation facts separately, then bundle.
H2. Order: generalize the lower bound (`generalizing lo`) and in case3 recurse with bound `x`
    (`x ≤ y` makes `node .. y ..` satisfy `HeapOrd x`). Permutation: chain `mkNode_perm` with the IH;
    the `¬ x ≤ y` case reorders `y` past `toList h1`, which `List.perm_iff_count` + `omega` handles.
    API theorems: `cases h`, then `cases hm` (substitutes `m`). `insert` is `merge_spec` on the
    singleton node. In `deleteMin` the children only satisfy `HeapOrd x`, but `merge_spec` needs
    `IsHeap` (`HeapOrd 0`): weaken them first (`heapOrd_weaken`, one `cases h`). Rank bound: induction on `h`; `2 ^ (r.rank + 1) = 2 ^ r.rank + 2 ^ r.rank ≤ 2 ^ l.rank + 2 ^ r.rank`.
H3. Perm case4: `refine (mkNode_perm _ _ _).trans ?_; simp only [toList] at ih ⊢;
    rw [List.perm_iff_count] at ih ⊢; intro a; have := ih a;
    simp only [List.count_append, List.count_cons] at this ⊢; omega`.
    Rank (node case, after `obtain ⟨rfl, hrl, ll, lr⟩ := w`): `have := Nat.pow_le_pow_right (n := 2) (by omega) hrl`,
    `show 2 ^ (r.rank + 1) ≤ (x :: (toList l ++ toList r)).length + 1`,
    `simp only [List.length_cons, List.length_append, Nat.pow_succ]; omega` (avoid `simp [Heap.rank]`:
    it unfolds `r.rank` into a `match` that `omega` cannot see through).
    findMin: `exact ⟨List.mem_cons_self, heapOrd_le (lo := m) ⟨Nat.le_refl m, w.1.2⟩⟩`.
-/
