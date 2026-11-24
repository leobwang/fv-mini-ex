/- Guide for H015 (Leftist heap).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a guide-only tree `Tree` and a list merge `mergeL`, NOT on the exercise's `Heap`.
Part W: worked combinations on those objects.
Assumed: Lean basics (E001–E033).
-/

namespace H015Guide

/-! # Guide-only objects (not the exercise's) -/

/-- A binary tree of naturals. -/
inductive Tree where
  | tip
  | bin (x : Nat) (l r : Tree)

/-- Number of `bin` nodes. -/
def Tree.size : Tree → Nat
  | .tip => 0
  | .bin _ l r => l.size + r.size + 1

/-- Preorder list of the labels. -/
def Tree.elems : Tree → List Nat
  | .tip => []
  | .bin x l r => x :: (l.elems ++ r.elems)

/-- A node whose bigger child goes on the left. -/
def pick (x : Nat) (a b : Tree) : Tree :=
  if b.size ≤ a.size then .bin x a b else .bin x b a

/-- Every label is at least `lo` (a Prop defined by pattern matching). -/
def AllGe : Nat → Tree → Prop
  | _, .tip => True
  | lo, .bin x l r => lo ≤ x ∧ AllGe lo l ∧ AllGe lo r

/-- The root label, if any. -/
def top : Tree → Option Nat
  | .tip => none
  | .bin x _ _ => some x

/-- Merge two lists, smaller head first. Its two recursive calls shrink different arguments. -/
def mergeL : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: mergeL xs (y :: ys) else y :: mergeL (x :: xs) ys

/-! # Part R · Reference entries -/

/-! ## Opening a definition and its `if` -/

/-! ### R1. `unfold f` · goal: `f args` → the body of `f` -/
example (P : Tree → Prop) (x : Nat) (a b : Tree)
    (h : P (if b.size ≤ a.size then .bin x a b else .bin x b a)) : P (pick x a b) := by
  unfold pick
  exact h

/-! ### R2. `split` · goal list: a goal containing `if c then t else e` → two goals, `h✝ : c` / `h✝ : ¬c` -/
example {α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop) (ht : c → P t)
    (he : ¬c → P e) : P (if c then t else e) := by
  split
  · exact ht (by assumption)
  · exact he (by assumption)

/-! ## Permutations of lists (`l₁.Perm l₂`, written `l₁ ~ l₂` on paper) -/

/-! ### R3. `simp [f]` on a `Perm` goal · closes it when both sides unfold to the same list
(`List.Perm.refl : l.Perm l` is a simp lemma). -/
example (x : Nat) (a b : Tree) : (Tree.bin x a b).elems.Perm (x :: (a.elems ++ b.elems)) := by
  simp [Tree.elems]

/-! ### R4. `List.Perm.cons` · `(x : α) → l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)` · goal: drop a common head
Also written as dot notation: `hp.cons x` for `hp : l₁.Perm l₂`. -/
example {α : Type} (x : α) (l₁ l₂ : List α) (h : l₁.Perm l₂) : (x :: l₁).Perm (x :: l₂) := by
  apply List.Perm.cons
  exact h

/-! ### R5. `List.perm_append_comm` · `(l₁ ++ l₂).Perm (l₂ ++ l₁)` · closes the goal -/
example {α : Type} (l₁ l₂ : List α) : (l₁ ++ l₂).Perm (l₂ ++ l₁) := by
  exact List.perm_append_comm

/-! ## Props defined by pattern matching -/

/-! ### R6. `refine ⟨?_, ?_, ?_⟩` (or `exact ⟨…⟩`) on a defined Prop · goal list
`AllGe lo (.bin x l r)` unfolds by definition to `lo ≤ x ∧ AllGe lo l ∧ AllGe lo r`, so the
anonymous constructor splits it without any `unfold`. -/
example (lo x : Nat) (l r : Tree) (hx : lo ≤ x) (hl : AllGe lo l) (hr : AllGe lo r) :
    AllGe lo (.bin x l r) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hx
  · exact hl
  · exact hr

/-! ## Induction that follows a function -/

/-! ### R7. `fun_induction f a b` · goal list: one goal per branch of `f`, with an IH per recursive call
`case1`…`case4` are the four branches of `mergeL` (and of any function with this shape). In `case2` the
hypothesis `x✝ : xs = [] → False` records that the first pattern did not match. -/
example (xs ys : List Nat) : (mergeL xs ys).length = xs.length + ys.length := by
  fun_induction mergeL xs ys
  all_goals simp_all
  all_goals omega

/-! ### R8. `fun_induction f a b generalizing n` · each IH becomes `∀ n, …`
Without `generalizing`, an IH is only about the fixed `n`. To name the `✝` hypotheses, add
`with | case1 ys => … | case3 x xs y ys hxy ih => …` (pattern variables, then the `if` condition,
then the IH; W2). -/
example (xs ys : List Nat) (n : Nat) (P : List Nat → Nat → Prop)
    (h : ∀ zs m, P zs m) : P (mergeL xs ys) n := by
  fun_induction mergeL xs ys generalizing n
  all_goals exact h _ n

/-! ### R9. `o.1`, `o.2.1`, `o.2.2` · projections of a hypothesis whose type unfolds to `A ∧ B ∧ C` -/
example (lo x : Nat) (l r : Tree) (P : Prop) (o : AllGe lo (.bin x l r)) (h : AllGe lo r → P) :
    P := by
  have hr := o.2.2
  exact h hr

/-! ### R10. `omega` · closes linear arithmetic over `Nat`/`Int`, using `¬`, `≤`, `<`, `=` hypotheses
Terms it does not understand (`t.size`, `2 ^ k`, `if … then 1 else 0`) are treated as unknowns. -/
example (x y : Nat) (h : ¬x ≤ y) : y ≤ x := by
  omega

/-! ## Structural induction and case analysis on a tree -/

/-! ### R11. `induction t generalizing lo` · goal list: one goal per constructor; each IH is `∀ lo, …`
Write `induction t generalizing lo with | tip => … | bin x l r ihl ihr => …` to name the new
variables and IHs (W5). -/
example (P : Nat → Tree → Prop) (htip : ∀ lo, P lo .tip)
    (hbin : ∀ lo x l r, (∀ lo, P lo l) → (∀ lo, P lo r) → P lo (.bin x l r)) (lo : Nat) (t : Tree) :
    P lo t := by
  induction t generalizing lo
  · exact htip _
  · exact hbin _ _ _ _ (by assumption) (by assumption)

/-! ### R12. `obtain ⟨hx, hl, hr⟩ := o` · context: `o` (a defined conjunction) → its three parts -/
example (lo x : Nat) (l r : Tree) (P : Prop) (o : AllGe lo (.bin x l r))
    (h : lo ≤ x → AllGe lo l → AllGe lo r → P) : P := by
  obtain ⟨hx, hl, hr⟩ := o
  exact h hx hl hr

/-! ### R13. `simp only [f] at h ⊢` · context and goal: unfold `f` in `h` and in the goal at once -/
example (x : Nat) (a b : Tree) (Q : List Nat → Prop) (h : Q (Tree.bin x a b).elems) :
    Q (Tree.bin x a b).elems := by
  simp only [Tree.elems] at h ⊢
  exact h

/-! ### R14. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l` · context (here `rw … at hy`) -/
example {α : Type} (a b : α) (l : List α) (P : Prop) (hy : a ∈ b :: l) (h : a = b ∨ a ∈ l → P) :
    P := by
  rw [List.mem_cons] at hy
  exact h hy

/-! ### R15. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · context -/
example {α : Type} (a : α) (s t : List α) (P : Prop) (hy : a ∈ s ++ t) (h : a ∈ s ∨ a ∈ t → P) :
    P := by
  rw [List.mem_append] at hy
  exact h hy

/-! ### R16. `rcases hy with rfl | hy | hy` · goal list: one goal per `∨` branch; `rfl` substitutes -/
example (y x : Nat) (s t : List Nat) (P : Nat → Prop) (hx : P x) (hs : ∀ z ∈ s, P z)
    (ht : ∀ z ∈ t, P z) (hy : y = x ∨ y ∈ s ∨ y ∈ t) : P y := by
  rcases hy with rfl | hy | hy
  · exact hx
  · exact hs y hy
  · exact ht y hy

/-! ### R17. `Nat.le_trans` · `n ≤ m → m ≤ k → n ≤ k` · goal `a ≤ c` → `b ≤ c` -/
example (a b c : Nat) (hab : a ≤ b) (h : b ≤ c) : a ≤ c := by
  apply Nat.le_trans hab
  exact h

/-! ### R18. `cases t` · goal list: one goal per constructor, no IH
`cases t with | tip => … | bin x l r => …` names the new variables. -/
example (P : Tree → Prop) (htip : P .tip) (hbin : ∀ x l r, P (.bin x l r)) (t : Tree) : P t := by
  cases t
  · exact htip
  · exact hbin _ _ _

/-! ### R19. `trivial` · closes `True`, also a defined Prop that unfolds to `True` -/
example (lo : Nat) : AllGe lo .tip := by
  trivial

/-! ### R20. `Nat.zero_le` · `0 ≤ n` -/
example (n : Nat) : 0 ≤ n := by
  exact Nat.zero_le n

/-! ## Chaining permutations -/

/-! ### R21. `refine h₁.trans ?_` (`List.Perm.trans`) · goal `l₁ ~ l₃` → `l₂ ~ l₃`, given `h₁ : l₁ ~ l₂` -/
example {α : Type} (l₁ l₂ l₃ : List α) (h₁ : l₁.Perm l₂) (h : l₂.Perm l₃) : l₁.Perm l₃ := by
  refine h₁.trans ?_
  exact h

/-! ### R22. `List.Perm.append_left` · `(l : List α) → t₁ ~ t₂ → (l ++ t₁) ~ (l ++ t₂)` · drop a common prefix -/
example {α : Type} (l t₁ t₂ : List α) (h : t₁.Perm t₂) : (l ++ t₁).Perm (l ++ t₂) := by
  apply List.Perm.append_left
  exact h

/-! ### R23. `List.append_assoc` · `a ++ b ++ c = a ++ (b ++ c)` · goal; `simp` applies it by itself -/
example {α : Type} (a b c : List α) (P : List α → Prop) (h : P (a ++ (b ++ c))) :
    P (a ++ b ++ c) := by
  rw [List.append_assoc]
  exact h

/-! ### R24. `List.perm_iff_count` · `l₁ ~ l₂ ↔ ∀ a, List.count a l₁ = List.count a l₂` · goal -/
example (l₁ l₂ : List Nat) (h : ∀ a, List.count a l₁ = List.count a l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  exact h

/-! ### R25. `List.count_append` · `count a (l₁ ++ l₂) = count a l₁ + count a l₂` · goal -/
example (a : Nat) (l₁ l₂ : List Nat) (P : Nat → Prop)
    (h : P (List.count a l₁ + List.count a l₂)) : P (List.count a (l₁ ++ l₂)) := by
  rw [List.count_append]
  exact h

/-! ### R26. `List.count_cons` · `count a (b :: l) = count a l + if (b == a) = true then 1 else 0` · goal -/
example (a b : Nat) (l : List Nat) (P : Nat → Prop)
    (h : P (List.count a l + if (b == a) = true then 1 else 0)) : P (List.count a (b :: l)) := by
  rw [List.count_cons]
  exact h

/-! ## `Option` equations, membership, named arguments -/

/-! ### R27. `Nat.le_refl` · `n ≤ n` -/
example (n : Nat) : n ≤ n := by
  exact Nat.le_refl n

/-! ### R28. `cases h` with `h : top (.bin a l r) = some b` · context: `b` is replaced by `a` everywhere
`cases` first computes `top (.bin a l r)` to `some a`, then uses that `some` is injective. -/
example (a b : Nat) (l r : Tree) (P : Nat → Prop) (ha : P a) (h : top (.bin a l r) = some b) :
    P b := by
  cases h
  exact ha

/-! ### R29. `cases h` with `h : top .tip = some b` · closes the goal
`top .tip` computes to `none`, and `none = some b` has no proof (different constructors). -/
example (b : Nat) (P : Prop) (h : top .tip = some b) : P := by
  cases h

/-! ### R30. `List.mem_cons_self` · `a ∈ a :: l` (arguments implicit) -/
example {α : Type} (a : α) (l : List α) : a ∈ a :: l := by
  exact List.mem_cons_self

/-! ### R31. `f (x := v)` · named argument: fix the implicit argument `x` of `f` by its name
Here `Nat.le_trans {n m k : Nat}`; `(m := b)` picks the middle term, which `apply` cannot guess. -/
example (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  apply Nat.le_trans (m := b)
  · exact h₁
  · exact h₂

/-! ### R32. `have ⟨h₁, h₂⟩ := e` · context gains the two parts of `e : A ∧ B` -/
example (A B P : Prop) (e : A ∧ B) (h : A → B → P) : P := by
  have ⟨h₁, h₂⟩ := e
  exact h h₁ h₂

/-! ## The rank bound -/

/-! ### R33. `obtain ⟨rfl, h⟩ := w` · context: `w : k = n + 1 ∧ Q`, `k` a local variable → `k` replaced by `n + 1` -/
example (k n : Nat) (Q : Prop) (P : Nat → Prop) (w : k = n + 1 ∧ Q) (hp : Q → P (n + 1)) :
    P k := by
  obtain ⟨rfl, hq⟩ := w
  exact hp hq

/-! ### R34. `Nat.pow_le_pow_right` · `n > 0 → i ≤ j → n ^ i ≤ n ^ j` · context gains the inequality -/
example (i j : Nat) (hij : i ≤ j) (P : Prop) (h : 2 ^ i ≤ 2 ^ j → P) : P := by
  have hp := Nat.pow_le_pow_right (n := 2) (by omega) hij
  exact h hp

/-! ### R35. `show G'` · goal: replaced by `G'`, which must be equal to it by definition -/
example (x : Nat) (l r : Tree) (P : Nat → Prop) (h : P (l.size + r.size + 1)) :
    P (Tree.bin x l r).size := by
  show P (l.size + r.size + 1)
  exact h

/-! ### R36. `List.length_cons` · `(a :: l).length = l.length + 1` · goal -/
example {α : Type} (a : α) (l : List α) (P : Nat → Prop) (h : P (l.length + 1)) :
    P (a :: l).length := by
  rw [List.length_cons]
  exact h

/-! ### R37. `List.length_append` · `(s ++ t).length = s.length + t.length` · goal -/
example {α : Type} (s t : List α) (P : Nat → Prop) (h : P (s.length + t.length)) :
    P (s ++ t).length := by
  rw [List.length_append]
  exact h

/-! ### R38. `Nat.pow_succ` · `n ^ (m + 1) = n ^ m * n` · goal; `omega` reads `2 ^ m * 2` as twice an unknown -/
example (n m : Nat) (P : Nat → Prop) (h : P (n ^ m * n)) : P (n ^ (m + 1)) := by
  rw [Nat.pow_succ]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `unfold` + `split` + the anonymous constructor (R1, R2, R6, R10) -/
example (x : Nat) (a b : Tree) : (pick x a b).size = a.size + b.size + 1 := by
  unfold pick
  split
  · rfl
  · show b.size + a.size + 1 = a.size + b.size + 1
    omega

/-! ### W2. `fun_induction` with a changing bound (R7, R8, R9, R10)
`Above lo l`: every element of `l` is ≥ `lo` and `l` is sorted. The recursion in `case3` needs the
bound `x`, not `lo`: that is why `lo` is generalized. -/
def Above : Nat → List Nat → Prop
  | _, [] => True
  | lo, x :: xs => lo ≤ x ∧ Above x xs

example (lo : Nat) (xs ys : List Nat) (hx : Above lo xs) (hy : Above lo ys) :
    Above lo (mergeL xs ys) := by
  fun_induction mergeL xs ys generalizing lo with
    | case1 ys => exact hy
    | case2 xs hxs => exact hx
    | case3 x xs y ys hxy ih => exact ⟨hx.1, ih x hx.2 ⟨hxy, hy.2⟩⟩
    | case4 x xs y ys hxy ih => exact ⟨hy.1, ih y ⟨by omega, hx.2⟩ hy.2⟩

/-! ### W3. A permutation by counting (R13, R24, R25, R26, R10)
Moving `y` past a whole list is awkward with `Perm` lemmas; with counts it is arithmetic. -/
example (y : Nat) (s t u : List Nat) (ih : u.Perm (s ++ t)) :
    (y :: u).Perm (s ++ y :: t) := by
  rw [List.perm_iff_count] at ih ⊢
  intro a
  have := ih a
  simp only [List.count_append, List.count_cons] at this ⊢
  omega

/-! ### W4. Prefix + reassociation (R4, R22, R21, R23) -/
example (x : Nat) (a b c d : List Nat) (ih : d.Perm (b ++ c)) :
    (x :: (a ++ d)).Perm (x :: (a ++ b ++ c)) := by
  apply List.Perm.cons
  refine (List.Perm.append_left a ih).trans ?_
  simp

/-! ### W5. Size bound by induction with `show` and length lemmas (R11, R35, R36, R37, R10) -/
example (t : Tree) : t.elems.length = t.size := by
  induction t with
    | tip => rfl
    | bin x l r ihl ihr =>
      show (x :: (l.elems ++ r.elems)).length = l.size + r.size + 1
      simp only [List.length_cons, List.length_append]
      omega

end H015Guide
