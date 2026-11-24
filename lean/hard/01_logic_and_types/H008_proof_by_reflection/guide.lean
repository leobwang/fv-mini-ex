/- Guide for H008 (Proof by reflection: a commutative-monoid normaliser).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`f : α → α → α` with laws given as hypotheses (`hassoc`, `hc`, `hu`) stands for the monoid operation.
Part W: worked combinations on objects that are NOT the exercise's (a tree of numbered leaves,
`Nat` addition, other lists).
Assumed: Lean basics (E001–E033). Core Lean only: no imports.
-/

namespace H008Guide

/-! # Part R · Reference entries -/

/-! ## Induction on lists and unfolding recursive definitions -/

/-! ### R1. `induction l with | nil => _ | cons x xs ih => _` · goal list: one goal per constructor
The `cons` goal gets `x xs` and the induction hypothesis `ih` for `xs`. Writing `?_` as a case body
leaves that goal open, so the infoview shows both goals at once. -/
example {α : Type} (P : List α → Prop) (hnil : P []) (hcons : ∀ x xs, P xs → P (x :: xs))
    (l : List α) : P l := by
  induction l with
    | nil => ?_
    | cons x xs ih => ?_
  · exact hnil
  · exact hcons x xs ih

/-! ### R2. `simp only [g]` on a recursive `def` · goal: `g (constructor …)` → that equation's right side
`g` defined by pattern matching has one equation per pattern; `simp only [g]` rewrites with them. -/
def dbl {α : Type} : List α → List α
  | [] => []
  | x :: xs => x :: x :: dbl xs

example (x : Nat) (xs : List Nat) (P : List Nat → Prop) (h : P (x :: x :: dbl xs)) :
    P (dbl (x :: xs)) := by
  simp only [dbl]
  exact h

/-! ### R3. `List.cons_append`, `List.nil_append` · goal: an append whose left list is built
`List.cons_append : x :: xs ++ ys = x :: (xs ++ ys)` (`::` binds tighter than `++`, so the left side is
`(x :: xs) ++ ys`); `List.nil_append : [] ++ ys = ys`. `simp` applies both by itself; `simp only [g]`
(R2) cannot unfold `g (x :: xs ++ ys)` before this step. -/
example {α : Type} (x : α) (xs ys : List α) (P : List α → Prop) (h : P (x :: (xs ++ ys))) :
    P (x :: xs ++ ys) := by
  rw [List.cons_append]
  exact h

example {α : Type} (ys : List α) (P : List α → Prop) (h : P ys) : P ([] ++ ys) := by
  rw [List.nil_append]
  exact h

/-! ### R4. A class law is a term: `Semi.comb_assoc a b c : comb (comb a b) c = comb a (comb b c)`
A `class` bundles operations with laws; `[Semi α]` says "α has them". `open Semi` lets you write
`comb` and `comb_assoc` instead of `Semi.comb`, `Semi.comb_assoc`. As a rewrite rule · goal. -/
class Semi (α : Type) where
  comb : α → α → α
  comb_assoc : ∀ x y z : α, comb (comb x y) z = comb x (comb y z)

open Semi in
example {α : Type} [Semi α] (a b c : α) (P : α → Prop) (h : P (comb a (comb b c))) :
    P (comb (comb a b) c) := by
  simp only [comb_assoc]
  exact h

/-! ### R5. `simp only [ih]` · goal: the induction hypothesis used as a rewrite rule, left to right -/
example (g k : List Nat → Nat) (xs : List Nat) (P : Nat → Prop) (ih : g xs = k xs) (h : P (k xs)) :
    P (g xs) := by
  simp only [ih]
  exact h

/-! ## Induction on your own syntax type -/

/-! ### R6. `induction t with | leaf n => _ | node l r ihl ihr => _` · goal list: one goal per constructor
A constructor with two arguments of the type itself gives two induction hypotheses. -/
inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)

example (P : Tree → Prop) (hleaf : ∀ n, P (.leaf n)) (hnode : ∀ l r, P l → P r → P (.node l r))
    (t : Tree) : P t := by
  induction t with
    | leaf n => ?_
    | node l r ihl ihr => ?_
  · exact hleaf n
  · exact hnode l r ihl ihr

/-! ## Rewriting with associativity and commutativity -/

/-! ### R7. `rw [hc _ e]` · goal: commutativity with one argument fixed rewrites only `f _ e`
`hc : ∀ a b, f a b = f b a`. Plain `rw [hc]` rewrites the first `f _ _` it meets, whatever it is.
In a `simp` set, an argument fixed this way also keeps `simp` from swapping other products. -/
example {α : Type} (f : α → α → α) (e a : α) (hc : ∀ a b : α, f a b = f b a) (P : α → Prop)
    (h : P (f e a)) : P (f a e) := by
  rw [hc _ e]
  exact h

/-! ### R8. `rw [← hassoc]` · goal: `f a (f b c)` → `f (f a b) c` (regroup to the left) -/
example {α : Type} (f : α → α → α) (a b c : α)
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c)) (P : α → Prop) (h : P (f (f a b) c)) :
    P (f a (f b c)) := by
  rw [← hassoc]
  exact h

/-! ### R9. `rw [hc a b]` · goal: explicit arguments pick exactly which product to swap -/
example {α : Type} (f : α → α → α) (a b c : α) (hc : ∀ a b : α, f a b = f b a) (P : α → Prop)
    (h : P (f (f b a) c)) : P (f (f a b) c) := by
  rw [hc a b]
  exact h

/-! ## Permutations: `List.Perm` -/

/-! ### R10. `induction h` on `h : l₁.Perm l₂` · goal list: one goal per way a permutation is built
`l₁.Perm l₂` ("l₂ is a reordering of l₁") is an inductive `Prop` with four constructors, so
induction on the proof `h` gives four goals: `nil`, `cons`, `swap`, `trans`. -/
example {α β : Type} (g : List α → β)
    (hcons : ∀ (x : α) (a b : List α), g a = g b → g (x :: a) = g (x :: b))
    (hswap : ∀ (x y : α) (l : List α), g (y :: x :: l) = g (x :: y :: l))
    {l₁ l₂ : List α} (h : l₁.Perm l₂) : g l₁ = g l₂ := by
  induction h with
    | nil => ?_
    | cons x _ ih => ?_
    | swap x y l => ?_
    | trans _ _ ih1 ih2 => ?_
  · rfl
  · exact hcons x _ _ ih
  · exact hswap x y l
  · exact Eq.trans ih1 ih2

/-! ### R11. `Eq.trans` · closes `a = c` from `h1 : a = b` and `h2 : b = c`; dot form `h1.trans h2` -/
example {α : Type} (a b c : α) (h1 : a = b) (h2 : b = c) : a = c := by
  exact h1.trans h2

/-! ### R12. `List.Perm.refl l : l.Perm l` · closes the goal; `.refl _` lets Lean find `l` -/
example {α : Type} (l : List α) : l.Perm l := by
  exact .refl _

/-! ## Case split on `if` -/

/-! ### R13. `split` · goal list: `P (if c then a else b)` → one goal per branch, with `c` or `¬c` -/
example {α : Type} (i j : Nat) (a b : α) (P : α → Prop) (ha : i ≤ j → P a) (hb : ¬i ≤ j → P b) :
    P (if i ≤ j then a else b) := by
  split
  next hij => exact ha hij
  next hij => exact hb hij

/-! ## Building permutations -/

/-! ### R14. `List.Perm.cons x : l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)` · closes; dot form `h.cons x` -/
example {α : Type} (x : α) {l₁ l₂ : List α} (h : l₁.Perm l₂) : (x :: l₁).Perm (x :: l₂) := by
  exact h.cons x

/-! ### R15. `List.Perm.trans : l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃` · closes; dot form `h1.trans h2` -/
example {α : Type} {l₁ l₂ l₃ : List α} (h1 : l₁.Perm l₂) (h2 : l₂.Perm l₃) : l₁.Perm l₃ := by
  exact h1.trans h2

/-! ### R16. `List.Perm.swap x y l : (y :: x :: l).Perm (x :: y :: l)` · closes -/
example {α : Type} (x y : α) (l : List α) : (y :: x :: l).Perm (x :: y :: l) := by
  exact .swap x y l

/-! ## From lists back to the statement -/

/-! ### R17. `rw [← hg]` with `hg : ∀ x, F (k x) = G x` · goal: the first `G _` found fixes `x`
Only that instance is rewritten; a second `G b` needs a second `rw [← hg]`. -/
example {α β γ : Type} (F : β → γ) (k : α → β) (G : α → γ) (hg : ∀ x, F (k x) = G x) (a b : α)
    (h : F (k a) = F (k b)) : G a = G b := by
  rw [← hg]
  rw [← hg]
  exact h

/-! ### R18. `congrArg f : a = b → f a = f b` · closes `f a = f b` -/
example {α β : Type} (f : α → β) (a b : α) (h : a = b) : f a = f b := by
  exact congrArg f h

/-! ## Computing: `decide`, `List.getD`, definitional unfolding -/

def Tree.leaves : Tree → List Nat
  | .leaf n => [n]
  | .node l r => l.leaves ++ r.leaves

/-! ### R19. `decide` · closes a closed `Prop` with decidable equality by evaluating it
Your own structurally recursive functions on concrete data evaluate too. As an argument: `(by decide)`.
It fails on a statement with free variables (`a b : α`). -/
example : (Tree.node (.leaf 2) (.node (.leaf 0) (.leaf 1))).leaves = [2, 0, 1] := by decide

/-! ### R20. `List.getD l i d` · `l[i]`, or the default `d` when `i` is out of range
`[a, b, c].getD 1 d` is `b` by computation, so `show` accepts it (R21). -/
example {α : Type} (a b c d : α) (P : α → Prop) (h : P b) : P ([a, b, c].getD 1 d) := by
  show P b
  exact h

/-! ### R21. `show G'` (and `exact`) work up to definitional unfolding · goal: `G` → an equal-by-computation `G'`
A recursive function applied to a concrete constructor tree unfolds to its value. -/
def Tree.sum (ρ : Nat → Nat) : Tree → Nat
  | .leaf n => ρ n
  | .node l r => l.sum ρ + r.sum ρ

example (ρ : Nat → Nat) (P : Nat → Prop) (h : P (ρ 0 + ρ 1)) :
    P ((Tree.node (.leaf 0) (.leaf 1)).sum ρ) := by
  show P (ρ 0 + ρ 1)
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Swap the last two factors: `rw [hassoc]`, R9, then R8 -/
example {α : Type} (f : α → α → α) (a b c : α)
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c)) (hc : ∀ a b : α, f a b = f b a) :
    f (f a b) c = f (f a c) b := by
  rw [hassoc]
  rw [hc b c]
  rw [← hassoc]

/-! ### W2. A permutation from the constructors: R16, then R14 twice, joined by R15 -/
example {α : Type} (x y : α) {l l' : List α} (h : l.Perm l') : (y :: x :: l).Perm (x :: y :: l') := by
  exact (List.Perm.swap x y l).trans ((h.cons y).cons x)

/-! ### W3. `congrArg` up to unfolding: `twice l` is `l ++ l` by definition (R18, R21) -/
def twice (l : List Nat) : List Nat := l ++ l

example (l1 l2 : List Nat) (h : twice l1 = twice l2) : (l1 ++ l1).length = (l2 ++ l2).length := by
  exact congrArg List.length h

/-! ### W4. Reflection in miniature: a soundness fact `sound` (here a hypothesis), two concrete trees,
`(by decide)` for the computed check, and an assignment `ρ` built with `List.getD` (R19–R21).
`exact` accepts it because `t.sum ρ` unfolds to `a + b` and `b + a`. -/
example (a b : Nat)
    (sound : ∀ t1 t2 : Tree, t1.leaves.reverse = t2.leaves → ∀ ρ : Nat → Nat, t1.sum ρ = t2.sum ρ) :
    a + b = b + a := by
  exact sound (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)) (by decide)
    (fun i => [a, b].getD i 0)

end H008Guide
