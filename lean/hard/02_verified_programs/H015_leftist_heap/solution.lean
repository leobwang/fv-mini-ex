/- H015 | Leftist heap | 1.5-2 h | priority queue, rank invariant, List.Perm, fun_induction
GOAL
  A leftist heap is a heap-ordered binary tree whose right spine is short. Prove the priority-queue
  API correct (merge/insert/deleteMin keep the invariants and the elements, findMin is the minimum)
  and the logarithmic bound `2 ^ rank ≤ size + 1` that makes merge fast.

GUIDE
  Entries R1–R38: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · mkNode_perm
  1. Open `mkNode` and case on its `if`:                               R1, R2
  2. Branch `b.rank ≤ a.rank` (children kept): unfold `toList`           R3
  3. Branch with the children swapped: drop the head `x`, then
     swap the two appended lists                                         R4, R5
  Prove first. Used in merge_spec (helper B, merge_perm, case3 / case4).
-/
-- MILESTONE (optional: change or delete)
theorem mkNode_perm (x : Nat) (a b : Heap) :
    (toList (mkNode x a b)).Perm (x :: (toList a ++ toList b)) := by
  unfold mkNode
  split
  · simp [toList]
  · exact List.Perm.cons _ List.perm_append_comm

/- SKELETON · merge_heapOrd
  Prove first. Used in merge_spec (its HeapOrd part, at bound 0).
  1. Local fact first (a `have`, all of lo x a b bound by `∀ {lo x a b}`, braces so
     that later calls omit them, then `intro`):
       mk : lo ≤ x → HeapOrd x a → HeapOrd x b → HeapOrd lo (mkNode x a b)
     proof: open mkNode and split, then the anonymous constructor        R1, R2, R6
  2. Follow `merge` with `lo` generalized, naming each case's variables   R7, R8
  3. case1 / case2: one hypothesis already is the goal                   exact
  4. case3 (`x ≤ y`): `mk` with the root's bound and left child from `o1`, and the
     IH at bound `x`; its second premise `HeapOrd x (.node r2 y l2 r2')`
     is built from the `if` condition and `o2`'s children               R9, R6
  5. case4 (`¬x ≤ y`): the mirror image, IH at bound `y`; `y ≤ x` by     R10
-/
-- MILESTONE (optional: change or delete)
theorem merge_heapOrd (lo : Nat) (h1 h2 : Heap) (o1 : HeapOrd lo h1) (o2 : HeapOrd lo h2) :
    HeapOrd lo (merge h1 h2) := by
  have mk : ∀ {lo x a b}, lo ≤ x → HeapOrd x a → HeapOrd x b → HeapOrd lo (mkNode x a b) := by
    intro lo x a b hx ha hb
    unfold mkNode
    split <;> exact ⟨hx, by assumption, by assumption⟩
  fun_induction merge h1 h2 generalizing lo with
  | case1 => exact o2
  | case2 => exact o1
  | case3 r1 x l1 r1' r2 y l2 r2' hxy ih =>
    -- WHY: recurse with the *new* lower bound `x`, not `lo`; this is why `lo` is generalized.
    exact mk o1.1 o1.2.1 (ih x o1.2.2 ⟨hxy, o2.2⟩)
  | case4 r1 x l1 r1' r2 y l2 r2' hxy ih =>
    exact mk o2.1 o2.2.1 (ih y ⟨by omega, o1.2⟩ o2.2.2)

/- SKELETON · mkNode_leftist
  1. Open `mkNode` and case on its `if`:                               R1, R2
  2. Each branch: the anonymous constructor; the rank field by `rfl`, the rank
     comparison from `split`'s hypothesis by `omega`, then the children
     in the order the branch puts them                                   R6, R10
  Prove first. Used in merge_spec (helper A, merge_leftist, case3 / case4).
-/
-- MILESTONE (optional: change or delete)
theorem mkNode_leftist (x : Nat) (a b : Heap) (la : Leftist a) (lb : Leftist b) :
    Leftist (mkNode x a b) := by
  unfold mkNode
  split
  · exact ⟨rfl, by omega, la, lb⟩
  · exact ⟨rfl, by omega, lb, la⟩

/- SKELETON · heapOrd_le
  Prove first. Used in findMin_spec (the lower bound).
  1. Induction on `h`, generalizing `lo` (children are bounded by the root, not `lo`),
     naming `rk x l r ihl ihr`                                           R11
  2. leaf: `toList .leaf` is empty                                       simp [toList]
  3. node: split `o`, `intro y hy`, unfold the membership in `hy`        R12, R13 (with R14, R15)
  4. Three cases `y = x` / `y ∈ toList l` / `y ∈ toList r`:              R16
     the first is `hx`; the others: `lo ≤ x` and the IH at bound `x`     R17
     (`lo` is implicit here, so the IH is `∀ {lo}, HeapOrd lo l → …`: pass it the
     order fact of the child, not the bound)
-/
-- MILESTONE (optional: change or delete)
theorem heapOrd_le {lo : Nat} {h : Heap} (o : HeapOrd lo h) : ∀ y ∈ toList h, lo ≤ y := by
  induction h generalizing lo with
  | leaf => simp [toList]
  | node rk x l r ihl ihr =>
    obtain ⟨hx, ol, orr⟩ := o
    intro y hy
    simp only [toList, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · exact hx
    · exact Nat.le_trans hx (ihl ol y hy)
    · exact Nat.le_trans hx (ihr orr y hy)

/- SKELETON · heapOrd_weaken
  Prove first. Used in deleteMin_spec (the children's order, before merge_spec).
  1. Case on `h` (no induction: only the root carries the bound)         R18
  2. leaf: `True`                                                        R19
  3. node: anonymous constructor, `0 ≤ x`, children's part of `o`         R6, R20, R9
-/
-- MILESTONE (optional: change or delete)
theorem heapOrd_weaken {lo : Nat} {h : Heap} (o : HeapOrd lo h) : HeapOrd 0 h := by
  cases h with
  | leaf => trivial
  | node rk x l r => exact ⟨Nat.zero_le x, o.2⟩

theorem merge_perm (h1 h2 : Heap) : (toList (merge h1 h2)).Perm (toList h1 ++ toList h2) := by
  fun_induction merge h1 h2 with
  | case1 => simp [toList]
  | case2 => simp [toList]
  | case3 r1 x l1 r1' r2 y l2 r2' hxy ih =>
    refine (mkNode_perm _ _ _).trans ?_
    simp only [toList] at ih ⊢
    exact List.Perm.cons _ ((List.Perm.append_left _ ih).trans (by simp))
  | case4 r1 x l1 r1' r2 y l2 r2' hxy ih =>
    refine (mkNode_perm _ _ _).trans ?_
    simp only [toList] at ih ⊢
    rw [List.perm_iff_count] at ih ⊢
    intro a
    have := ih a
    simp only [List.count_append, List.count_cons] at this ⊢
    omega

theorem merge_leftist (h1 h2 : Heap) (l1 : Leftist h1) (l2 : Leftist h2) :
    Leftist (merge h1 h2) := by
  fun_induction merge h1 h2 with
  | case1 => exact l2
  | case2 => exact l1
  | case3 r1 x l1' r1' r2 y l2' r2' hxy ih =>
    exact mkNode_leftist _ _ _ l1.2.2.1 (ih l1.2.2.2 l2)
  | case4 r1 x l1' r1' r2 y l2' r2' hxy ih =>
    exact mkNode_leftist _ _ _ l2.2.2.1 (ih l1 l2.2.2.2)

/- SKELETON · merge_spec
  Uses the milestones merge_heapOrd, mkNode_leftist, mkNode_perm. Prove two more helpers
  first (theorems placed above this one):
   A. merge_leftist (h1 h2 : Heap) (l1 : Leftist h1) (l2 : Leftist h2) : Leftist (merge h1 h2)
        follow merge                                                     R7
        (name the children l1' l2' in `with`: `l1`, `l2` are already the hypotheses)
        case1 / case2: exact; case3 / case4: mkNode_leftist with a child's part
        of l1 / l2 and the IH                                            R9
   B. merge_perm (h1 h2 : Heap) : (toList (merge h1 h2)).Perm (toList h1 ++ toList h2)
        follow merge                                                     R7
        case1 / case2: unfold toList                                     R3
        case3 / case4: chain with mkNode_perm, unfold toList in ih and goal   R21, R13
        case3: drop `x`, drop the prefix with ih, reassociate            R4 → R22 → R21 → R23
        case4: count occurrences: R24 at ih ⊢, intro a, have := ih a,
               R25, R26 at this ⊢, then                                  R10
  1. Bundle: anonymous constructor of merge_heapOrd at bound 0, A and B,
     feeding them the parts of w1 and w2                                 R6, R9
-/
-- BEGIN SPEC
theorem merge_spec (h1 h2 : Heap) (w1 : IsHeap h1) (w2 : IsHeap h2) :
    IsHeap (merge h1 h2) ∧ (toList (merge h1 h2)).Perm (toList h1 ++ toList h2) :=
-- END SPEC
  ⟨⟨merge_heapOrd 0 h1 h2 w1.1 w2.1, merge_leftist h1 h2 w1.2 w2.2⟩, merge_perm h1 h2⟩

/- SKELETON · insert_spec
  1. `insert x h` is by definition `merge (.node 1 x .leaf .leaf) h`: apply merge_spec
     to the singleton and `w`.
  2. The singleton is a heap, as one anonymous-constructor term:          R6
       HeapOrd 0 part:  0 ≤ x and two `True`s                            R20, R19
       Leftist part:    rank by `rfl`, `0 ≤ 0`, two `True`s               R27, R19
-/
-- BEGIN SPEC
theorem insert_spec (x : Nat) (h : Heap) (w : IsHeap h) :
    IsHeap (insert x h) ∧ (toList (insert x h)).Perm (x :: toList h) :=
-- END SPEC
  merge_spec _ h ⟨⟨Nat.zero_le x, trivial, trivial⟩, rfl, Nat.le_refl 0, trivial, trivial⟩ w

/- SKELETON · findMin_spec
  Uses the milestone heapOrd_le.
  1. Case on `h`                                                         R18
  2. leaf: `hm` is `none = some m`                                       R29
  3. node: `cases hm` turns the root `x` into `m`                        R28
  4. membership: the head of the list                                    R30
     lower bound: heapOrd_le at bound `m`, fed `m ≤ m` and the children's
     part of `w`                                                         R31, R6, R27, R9
-/
-- BEGIN SPEC
theorem findMin_spec (h : Heap) (m : Nat) (w : IsHeap h) (hm : findMin h = some m) :
    m ∈ toList h ∧ ∀ y ∈ toList h, m ≤ y :=
-- END SPEC
  by
    cases h with
    | leaf => cases hm
    | node rk x l r =>
      cases hm
      exact ⟨List.mem_cons_self, heapOrd_le (lo := m) ⟨Nat.le_refl m, w.1.2⟩⟩

/- SKELETON · deleteMin_spec
  Uses the milestone heapOrd_weaken and merge_spec.
  1. Case on `h`, then on `hm`                                           R18, R29 / R28
  2. Split `w` into the children's order and leftist facts               R12
  3. Weaken the children's order to bound 0 (heapOrd_weaken), then call
     merge_spec on the two children and destructure its result           R32
  4. Finish: the heap part, and the permutation with `m` put in front     R6, R4 (`hp.cons m`)
-/
-- BEGIN SPEC
theorem deleteMin_spec (h : Heap) (m : Nat) (w : IsHeap h) (hm : findMin h = some m) :
    IsHeap (deleteMin h) ∧ (m :: toList (deleteMin h)).Perm (toList h) :=
-- END SPEC
  by
    cases h with
    | leaf => cases hm
    | node rk x l r =>
      cases hm
      obtain ⟨⟨_, ol, orr⟩, _, _, ll, lr⟩ := w
      have ⟨hh, hp⟩ := merge_spec l r ⟨heapOrd_weaken ol, ll⟩ ⟨heapOrd_weaken orr, lr⟩
      exact ⟨hh, hp.cons m⟩

/- SKELETON · rank_bound
  1. Induction on `h` (nothing to generalize), naming `rk x l r ihl ihr`  R11
  2. leaf:                                                               simp [Heap.rank]
  3. node: substitute the cached rank and split `w`                      R33
  4. IHs for `l` and `r` (have), and `2 ^ r.rank ≤ 2 ^ l.rank`            R34
  5. Restate the goal with `.rank` and `toList` of the node unfolded       R35
  6. Lengths and `2 ^ (k + 1)` into linear form, then finish              R36, R37, R38 → R10
     (not `simp [Heap.rank]` here: see the Traps in cheatsheet.md)
-/
-- BEGIN SPEC
theorem rank_bound (h : Heap) (w : Leftist h) : 2 ^ h.rank ≤ (toList h).length + 1 :=
-- END SPEC
  by
    induction h with
    | leaf => simp [Heap.rank]
    | node rk x l r ihl ihr =>
      obtain ⟨rfl, hrl, ll, lr⟩ := w
      have hl := ihl ll
      have hr := ihr lr
      have := Nat.pow_le_pow_right (n := 2) (by omega) hrl
      show 2 ^ (r.rank + 1) ≤ (x :: (toList l ++ toList r)).length + 1
      simp only [List.length_cons, List.length_append, Nat.pow_succ]
      omega

end H015

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything about `merge` is one `fun_induction merge h1 h2` (R7); everything about `mkNode` is
    `unfold mkNode; split` (R1, R2). Prove the order, leftist and permutation facts about `merge`
    separately, then bundle them (R6). The API theorems start with `cases h`, then `cases hm` (R18, R28, R29).
H2. Order: generalize the lower bound (`generalizing lo`, R8) and in case3 use the IH at bound `x`
    (`x ≤ y` makes `node .. y ..` satisfy `HeapOrd x`). Permutation: chain `mkNode_perm` with the IH (R21);
    case4 moves `y` past `toList h1`, which counting (R24–R26) plus `omega` handles.
    `insert` is `merge_spec` on the singleton node. In `deleteMin` the children only satisfy
    `HeapOrd x`, but `merge_spec` needs `IsHeap` (`HeapOrd 0`): weaken them first (`heapOrd_weaken`).
    Rank bound: induction on `h`; `2 ^ (r.rank + 1) = 2 ^ r.rank + 2 ^ r.rank ≤ 2 ^ l.rank + 2 ^ r.rank`.
H3. Perm case4: `refine (mkNode_perm _ _ _).trans ?_; simp only [toList] at ih ⊢;
    rw [List.perm_iff_count] at ih ⊢; intro a; have := ih a;
    simp only [List.count_append, List.count_cons] at this ⊢; omega`.
    Rank (node case, after `obtain ⟨rfl, hrl, ll, lr⟩ := w`): `have := Nat.pow_le_pow_right (n := 2) (by omega) hrl`,
    `show 2 ^ (r.rank + 1) ≤ (x :: (toList l ++ toList r)).length + 1`,
    `simp only [List.length_cons, List.length_append, Nat.pow_succ]; omega`.
    findMin: `exact ⟨List.mem_cons_self, heapOrd_le (lo := m) ⟨Nat.le_refl m, w.1.2⟩⟩`.
-/
