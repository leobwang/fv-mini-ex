/- Guide for H005 (NNF rewriting terminates).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about inductive types use the toy type `T` and the toy relation `Step` below, which are
NOT the exercise's `F` and `Rw`.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace H005Guide

/-! # Toy objects used by the entries -/

/-- A toy tree: leaves carry a number, `flip` has one child, `join` has two. -/
inductive T where
  | leaf (n : Nat)
  | flip (t : T)
  | join (s t : T)

/-- A toy one-step relation on `T`: cancel a double `flip`, or step inside a child. -/
inductive Step : T → T → Prop
  | flipFlip {t : T} : Step (.flip (.flip t)) t
  | flipC {t t' : T} : Step t t' → Step (.flip t) (.flip t')
  | joinL {s s' t : T} : Step s s' → Step (.join s t) (.join s' t)
  | joinR {s t t' : T} : Step t t' → Step (.join s t) (.join s t')

/-- A toy function into `Nat`, defined by pattern matching (structural recursion). -/
def size : T → Nat
  | .leaf _ => 1
  | .flip t => size t + 1
  | .join s t => size s + size t + 1

/-- A toy predicate defined by pattern matching: it reduces to `True` or `False`. -/
def IsLeaf : T → Prop
  | .leaf _ => True
  | _ => False

/-! # Part R · Reference entries -/

/-! ## Induction on a step, unfolding, Bool lemmas -/

/-! ### R1. `induction h` (with `h : Step a b`) · goal list: one goal per constructor of `Step`
`a`, `b` are replaced by that constructor's pattern; a constructor with a premise `Step x y` gets
the induction hypothesis for it. Names Lean invents print with `✝` (inaccessible). -/
example (P : T → T → Prop) (a b : T) (h : Step a b)
    (h1 : ∀ t : T, P t.flip.flip t) (h2 : ∀ t t' : T, P t t' → P t.flip t'.flip)
    (h3 : ∀ s s' t : T, P s s' → P (s.join t) (s'.join t))
    (h4 : ∀ s t t' : T, P t t' → P (s.join t) (s.join t')) : P a b := by
  induction h
  · exact h1 _
  · exact h2 _ _ (by assumption)
  · exact h3 _ _ _ (by assumption)
  · exact h4 _ _ _ (by assumption)

/-! ### R2. `case c x y => tac` · goal list: work on the goal of constructor `c`, naming its `✝` variables
The names go to the inaccessible variables in order, implicit ones included (`flipC` has `t✝ t'✝ a✝ a_ih✝`).
`induction h with | c₁ => tac | c₂ h ih => tac` is the same in one block, but there `c₂ h ih` names
only the explicit premise and its hypothesis; `| c₂ _ ih | c₃ _ ih => tac` shares one `tac` (W1). -/
example (P : T → T → Prop) (a b : T) (h : Step a b) (hall : ∀ x y, P x y) : P a b := by
  induction h
  case flipFlip t => exact hall t.flip.flip t
  case flipC t t' h ih => exact hall t.flip t'.flip
  all_goals exact hall _ _

/-! ### R3. `simp only [size]` · goal: `size (constructor …)` → that constructor's right-hand side -/
example (P : Nat → Prop) (s t : T) (h : P (size s + size t + 1)) : P (size (s.join t)) := by
  simp only [size]
  exact h

/-! ### R4. `Bool.not_not` · `(!!b) = b` (`simp` applies it by itself) -/
example (b : Bool) (P : Bool → Prop) (h : P b) : P (!!b) := by
  rw [Bool.not_not]
  exact h

/-! ### R5. `Bool.not_and` · `(!(x && y)) = (!x || !y)` -/
example (x y : Bool) (P : Bool → Prop) (h : P (!x || !y)) : P (!(x && y)) := by
  rw [Bool.not_and]
  exact h

/-! ### R6. `Bool.not_or` · `(!(x || y)) = (!x && !y)` -/
example (x y : Bool) (P : Bool → Prop) (h : P (!x && !y)) : P (!(x || y)) := by
  rw [Bool.not_or]
  exact h

/-! ### R7. `simp [ih]` with `ih : f x = f y` · goal: every `f x` → `f y` -/
example (f : T → Bool) (x y : T) (ih : f x = f y) (P : Bool → Prop) (h : P (f y)) : P (f x) := by
  simp [ih]
  exact h

/-! ## A function into `Nat` -/

/-! ### R8. A `def` by pattern matching: `rfl` evaluates it on a concrete tree · goal closed -/
example : size (T.leaf 0).flip.flip = 3 := by
  rfl

/-! ## Powers of 2 and `omega` -/

/-! ### R9. `Nat.pow_le_pow_right` · `n > 0 → i ≤ j → n ^ i ≤ n ^ j` · context gains the bound
`(n := 2)` fixes the implicit argument `n` by name; `(by omega)` proves `2 > 0`. -/
example (x : Nat) (hx : 1 ≤ x) (P : Prop) (h : 2 ^ 1 ≤ 2 ^ x → P) : P := by
  have e := Nat.pow_le_pow_right (n := 2) (by omega) hx
  exact h e

/-! ### R10. `simpa using e` · simplifies the type of `e` and the goal (`2 ^ 1` → `2`), then closes -/
example (x : Nat) (e : 2 ^ 1 ≤ 2 ^ x) : 2 ≤ 2 ^ x := by
  simpa using e

/-! ### R11. `Nat.pow_succ` · `b ^ (m + 1) = b ^ m * b` -/
example (b m : Nat) (P : Nat → Prop) (h : P (b ^ m * b)) : P (b ^ (m + 1)) := by
  rw [Nat.pow_succ]
  exact h

/-! ### R12. `Nat.pow_add` · `b ^ (m + n) = b ^ m * b ^ n` -/
example (b m n : Nat) (P : Nat → Prop) (h : P (b ^ m * b ^ n)) : P (b ^ (m + n)) := by
  rw [Nat.pow_add]
  exact h

/-! ### R13. `Nat.mul_le_mul_right k` · `n ≤ m → n * k ≤ m * k` · context gains the product bound -/
example (n m k : Nat) (hnm : n ≤ m) (P : Prop) (h : n * k ≤ m * k → P) : P := by
  have h1 : n * k ≤ m * k := Nat.mul_le_mul_right k hnm
  exact h h1

/-! ### R14. `Nat.mul_le_mul_left k` · `n ≤ m → k * n ≤ k * m` · context gains the product bound -/
example (n m k : Nat) (hnm : n ≤ m) (P : Prop) (h : k * n ≤ k * m → P) : P := by
  have h2 : k * n ≤ k * m := Nat.mul_le_mul_left k hnm
  exact h h2

/-! ### R15. `omega` · closes linear (in)equalities over `Nat`; a product of variables or a power
`2 ^ x` is an opaque atom, so every fact about it must already be in the context. -/
example (p q : Nat) (hq : 1 ≤ q) (hpq : p ≤ p * q) : p < p * q + q := by
  omega

/-! ## Case analysis on a tree -/

/-! ### R16. `cases t` (with `t : T`) · goal list: one goal per constructor, no induction hypothesis -/
example (P : T → Prop) (t : T) (h1 : ∀ n, P (.leaf n)) (h2 : ∀ s : T, P s.flip)
    (h3 : ∀ s r : T, P (s.join r)) : P t := by
  cases t
  · exact h1 _
  · exact h2 _
  · exact h3 _ _

/-! ### R17. `Nat.one_le_two_pow` · `1 ≤ 2 ^ n` -/
example (n : Nat) : 1 ≤ 2 ^ n := by
  exact Nat.one_le_two_pow

/-! ## Strict bounds through powers -/

/-! ### R18. `Nat.lt_two_pow_self` · `n < 2 ^ n` -/
example (n : Nat) : n < 2 ^ n := by
  exact Nat.lt_two_pow_self

/-! ### R19. `apply Nat.lt_trans h` · `n < m → m < k → n < k` · goal `n < k` → `m < k` -/
example (n m k : Nat) (hnm : n < m) (hmk : m < k) : n < k := by
  apply Nat.lt_trans hnm
  exact hmk

/-! ### R20. `apply Nat.pow_lt_pow_right` · `1 < a → m < n → a ^ m < a ^ n` · goal list: two goals -/
example (a m n : Nat) (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n := by
  apply Nat.pow_lt_pow_right
  · exact ha
  · exact hmn

/-! ## Well-foundedness -/

/-! ### R21. `Nat.lt_wfRel.wf` · `<` on `Nat` is well-founded · context gains it -/
example (P : Prop) (h : WellFounded (fun a b : Nat => a < b) → P) : P := by
  have hlt : WellFounded (fun a b : Nat => a < b) := Nat.lt_wfRel.wf
  exact h hlt

/-! ### R22. `InvImage.wf f hr` · `WellFounded r → WellFounded (InvImage r f)` · context gains it
`InvImage r f x y` unfolds to `r (f x) (f y)`, so you may state the result with `f x < f y`. -/
example {α : Type} (f : α → Nat) (P : Prop) (h : WellFounded (fun x y => f x < f y) → P) : P := by
  have hw : WellFounded (fun x y => f x < f y) := InvImage.wf f Nat.lt_wfRel.wf
  exact h hw

/-! ### R23. `refine Subrelation.wf ?_ hr` · `Subrelation q r → WellFounded r → WellFounded q`
goal `WellFounded q` → `Subrelation q r`. -/
example {α : Type} (q r : α → α → Prop) (hr : WellFounded r) (hqr : Subrelation q r) :
    WellFounded q := by
  refine Subrelation.wf ?_ hr
  exact hqr

/-! ### R24. `intro x y hq` on `Subrelation q r` · it unfolds to `∀ {x y}, q x y → r x y`
In term mode, `fun hq => …` does the same (Lean adds `x y` itself, they are implicit). -/
example {α : Type} (q : α → α → Prop) (f : α → Nat) (hd : ∀ {x y}, q x y → f x < f y) :
    Subrelation q (fun x y => f x < f y) := by
  intro x y hq
  exact hd hq

/-! ## Normal forms: induction on a tree, impossible steps -/

/-! ### R25. `induction t` (with `t : T`) · goal list: one goal per constructor, with a hypothesis
for each child of type `T` -/
example (P : T → Prop) (t : T) (h1 : ∀ n, P (.leaf n)) (h2 : ∀ s : T, P s → P s.flip)
    (h3 : ∀ s r : T, P s → P r → P (s.join r)) : P t := by
  induction t
  · exact h1 _
  · exact h2 _ (by assumption)
  · exact h3 _ _ (by assumption) (by assumption)

/-! ### R26. `constructor` on `A ↔ B` · goal list: `A → B` and `B → A`
The term form is `⟨fun a => …, fun b => …⟩`. -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  · exact hab
  · exact hba

/-! ### R27. `trivial` · closes `True`, also a predicate that reduces to `True` by its definition -/
example (n : Nat) : IsLeaf (.leaf n) := by
  trivial

/-! ### R28. `nomatch h` · closes any goal when no constructor can produce `h`
(`h : Step (.leaf n) b`: no constructor of `Step` starts at a leaf), or when `h`'s type reduces to
`False` by a definition. -/
example (n : Nat) (b : T) (G : Prop) (h : Step (.leaf n) b) : G := by
  nomatch h

example (t : T) (G : Prop) (h : IsLeaf t.flip) : G := by
  nomatch h

/-! ### R29. `cases h` (with `h : Step x b`, `x` concrete) · goal list: only the constructors whose
left side can equal `x` remain; Lean substitutes `b` -/
example (n : Nat) (b : T) (G : Prop) (h : Step (T.leaf n).flip b) : G := by
  cases h
  case flipC t' h' => nomatch h'

/-! ### R30. `intro b hb` on `∀ b, ¬ Q b` · `¬ A` is `A → False`, so it introduces a proof of `Q b` -/
example (Q : T → Prop) (hQ : ∀ b, Q b → False) : ∀ b, ¬ Q b := by
  intro b hb
  exact hQ b hb

/-! ### R31. `absurd a hn` with a constructor `.c` · `absurd : A → ¬ A → B`; `.c` means the
constructor `c` of the expected type (here `Step.flipFlip`) -/
example (t : T) (G : Prop) (hn : ¬ Step t.flip.flip t) : G := by
  exact absurd .flipFlip hn

/-! ### R32. `apply h.mp` / `apply h.mpr` (with `h : A ↔ B`) · goal `B` → `A` / goal `A` → `B` -/
example (A B : Prop) (h : A ↔ B) (a : A) : B := by
  apply h.mp
  exact a

/-! ### R33. `intro ⟨ha, hb⟩ c hc` · context: split an `∧` while introducing it, then the rest -/
example (A B : Prop) (Q : T → Prop) (G : T → Prop) (hG : A → B → ∀ c, Q c → G c) :
    A ∧ B → ∀ c, Q c → G c := by
  intro ⟨ha, hb⟩ c hc
  exact hG ha hb c hc

/-! # Part W · Worked combinations (on the toy objects, not the exercise's) -/

/-! ### W1. Induction on a step with shared alternatives (R1, R2, R3, R15): every `Step` lowers `size` -/
example {a b : T} (h : Step a b) : size b < size a := by
  induction h with
    | flipFlip => simp only [size]; omega
    | flipC _ ih | joinL _ ih | joinR _ ih => simp only [size]; omega

/-! ### W2. Termination of `Step` from a decreasing measure: R23, R22, R21, R24 in term mode -/
example (hd : ∀ {a b : T}, Step a b → size b < size a) : WellFounded (fun b a => Step a b) :=
  Subrelation.wf (fun h => hd h) (InvImage.wf size Nat.lt_wfRel.wf)

/-! ### W3. Which trees are normal for `Step`: case split under `flip`, rule steps out with `nomatch` -/
example (n : Nat) : ∀ b, ¬ Step (T.leaf n).flip b := by
  intro b hb
  cases hb
  case flipC t' h' => nomatch h'

example (t : T) : ¬ ∀ b, ¬ Step t.flip.flip b := by
  intro h
  exact absurd .flipFlip (h t)

/-! ### W4. Two power atoms: `omega` alone fails here; the two product bounds (R13, R14) fix it (R15) -/
example (x y : Nat) (hx : 3 ≤ 3 ^ x) (hy : 3 ≤ 3 ^ y) : 3 ^ x + 3 ^ y < 3 ^ x * 3 ^ y := by
  have h1 : 3 * 3 ^ y ≤ 3 ^ x * 3 ^ y := Nat.mul_le_mul_right _ hx
  have h2 : 3 ^ x * 3 ≤ 3 ^ x * 3 ^ y := Nat.mul_le_mul_left _ hy
  omega

end H005Guide
