/- Guide for H004 (Well-founded relations: Acc, lex, descending chains).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`C`, `P`, `Q` stand for "the rest of your goal": the step changes only the part shown. A hypothesis
`h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a subrelation, a predecessor
function, concrete pairs of numbers).
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace H004Guide

/-! # Part R · Reference entries -/

/-! ## Well-founded induction and negation -/

/-! ### R1. `induction a using hw.induction with | _ x ih => …` · goal and context
Lemma `WellFounded.induction : WellFounded r → ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a`.
The goal becomes `C x` for a fresh `x`, and `ih` says `C` holds for every `r`-predecessor of `x`. -/
example {α : Type} (r : α → α → Prop) (C : α → Prop) (hw : WellFounded r) (a : α)
    (step : ∀ x, (∀ y, r y x → C y) → C x) : C a := by
  induction a using hw.induction with
    | _ x ih => ?_
  exact step x ih

/-! ### R2. `intro h` on `¬A` · context gains `h : A`; goal becomes `False`
`¬A` is by definition `A → False`. As a term: `fun h => …`. -/
example (A : Prop) (k : A → False) : ¬A := by
  intro h
  exact k h

/-! ### R3. `exact ih y hy hq` · closes the goal by applying the induction hypothesis
`ih y hy : ¬Q y` is itself a function `Q y → False`, so one more argument gives `False`. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (x y : α) (ih : ∀ y, r y x → ¬Q y)
    (hy : r y x) (hq : Q y) : False := by
  exact ih y hy hq

/-! ## Accessibility `Acc` -/

/-! ### R4. `induction ha with | intro x hx ih => …` (with `ha : Acc r a`) · goal and context
`Acc` has one constructor `Acc.intro x (h : ∀ y, r y x → Acc r y)`, so there is one goal; `ih`
is the induction hypothesis for every predecessor `y` of `x`. -/
example {α : Type} (r : α → α → Prop) (C : α → Prop) (a : α) (ha : Acc r a)
    (step : ∀ x, (∀ y, r y x → C y) → C x) : C a := by
  induction ha with
    | intro x hx ih => ?_
  exact step x ih

/-! ### R5. `induction ha generalizing b with …` · the IH quantifies over `b` too
Without `generalizing b`, `b` stays fixed and the IH only speaks about that one `b`. -/
example {α β : Type} (r : α → α → Prop) (C : α → β → Prop) (a : α) (ha : Acc r a) (b : β)
    (step : ∀ x b, (∀ y, r y x → ∀ b', C y b') → C x b) : C a b := by
  induction ha generalizing b with
    | intro x hx ih => ?_
  exact step x b ih

/-! ### R6. `constructor` on `Acc r a` · goal: `Acc r a` → `∀ y, r y a → Acc r y` (applies `Acc.intro`) -/
example {α : Type} (r : α → α → Prop) (a : α) (h : ∀ y, r y a → Acc r y) : Acc r a := by
  constructor
  exact h

/-! ### R7. `cases hp with | left _ _ h => … | right _ h => …` on `hp : Prod.Lex r s p (a, b)`
Goal list: one goal per way the lexicographic step can happen. `left`: the first component went
down (`h : r a₁ a`, second component arbitrary). `right`: the first stays `a`, the second went
down (`h : s b₁ b`). `p` is replaced by the pair each constructor builds. -/
example {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (P : α × β → Prop) (a : α) (b : β)
    (p : α × β) (hp : Prod.Lex r s p (a, b))
    (hl : ∀ a₁ b₁, r a₁ a → P (a₁, b₁)) (hr : ∀ b₁, s b₁ b → P (a, b₁)) : P p := by
  cases hp with
    | left _ _ h => ?_
    | right _ h => ?_
  exact hl _ _ h
  exact hr _ h

/-! ## `WellFounded` -/

/-! ### R8. `refine ⟨fun x => ?_⟩` on `WellFounded r` · goal: one `Acc r x` for a fresh `x`
`WellFounded r` is a structure with one field `∀ a, Acc r a` (constructor `WellFounded.intro`). -/
example {α : Type} (r : α → α → Prop) (h : ∀ x, Acc r x) : WellFounded r := by
  refine ⟨fun x => ?_⟩
  exact h x

/-! ### R9. `intro ⟨x, y⟩` on `∀ p : α × β, P p` · context gains the two components
As a term: `fun ⟨x, y⟩ => …`. -/
example {α β : Type} (P : α × β → Prop) (h : ∀ x y, P (x, y)) : ∀ p : α × β, P p := by
  intro ⟨x, y⟩
  exact h x y

/-! ### R10. `hw.apply x` · `WellFounded.apply : WellFounded r → ∀ a, Acc r a` · closes `Acc r x` -/
example {α : Type} (r : α → α → Prop) (hw : WellFounded r) (x : α) : Acc r x := by
  exact hw.apply x

/-! ## Equations, contradiction -/

/-! ### R11. `exact h ▸ hp` · closes `P b` from `h : a = b` and `hp : P a` (rewrite inside a term) -/
example {α : Type} (P : α → Prop) (a b : α) (h : a = b) (hp : P a) : P b := by
  exact h ▸ hp

/-! ### R12. `intro ⟨x, hx⟩` on `¬∃ x, P x` · context gains the witness and its proof; goal `False` -/
example {α : Type} (P : α → Prop) (k : ∀ x, P x → False) : ¬∃ x, P x := by
  intro ⟨x, hx⟩
  exact k x hx

/-! ### R13. `refine Classical.byContradiction fun hn => ?_` · goal `A` → `hn : ¬A ⊢ False`
`Classical.byContradiction : (¬p → False) → p` (classical logic: uses the axiom of choice). -/
example (A : Prop) (k : ¬A → False) : A := by
  refine Classical.byContradiction fun hn => ?_
  exact k hn

/-! ### R14. `refine .intro x fun y hy => ?_` on `Acc r x` · goal: one predecessor `y` at a time
The term form of R6, with the predecessor and the step already introduced. -/
example {α : Type} (r : α → α → Prop) (x : α) (h : ∀ y, r y x → Acc r y) : Acc r x := by
  refine .intro x fun y hy => ?_
  exact h y hy

/-! ### R15. `refine hn ?_` with `hn : ¬A` · goal `False` → `A` -/
example (A : Prop) (hn : ¬A) (ha : A) : False := by
  refine hn ?_
  exact ha

/-! ## Subtypes, choice, iteration -/

/-! ### R16. `⟨v, hv⟩ : {x // p x}` · closes a subtype goal: a value together with a proof about it -/
example {α : Type} (p : α → Prop) (v : α) (hv : p v) : {x // p x} := by
  exact ⟨v, hv⟩

/-! ### R17. `z.1`, `z.2` for `z : {x // p x}` · `z.1 : α` (printed `z.val`) and `z.2 : p z.val` -/
example {α : Type} (p : α → Prop) (z : {x // p x}) : p z.1 := by
  exact z.2

/-! ### R18. `Classical.choose h`, `Classical.choose_spec h` (with `h : ∃ x, Q x`) · context
`Classical.choose h : α` is some witness; `Classical.choose_spec h : Q (Classical.choose h)`. -/
example {α : Type} (Q : α → Prop) (h : ∃ x, Q x) (G : Prop) (k : ∀ x, Q x → G) : G := by
  have hc := Classical.choose_spec h
  exact k _ hc

/-! ### R19. `let t : T := e` · context gains the local definition `t : T := e`; goal unchanged
Lean unfolds `t` to `e` whenever it compares terms (`exact`, `show`). -/
example {α : Type} (P : α → Prop) (g : α → α) (a : α) (h : P (g a)) : P (g a) := by
  let t : α := g a
  exact (h : P t)

/-! ### R20. `Nat.rec x (fun _ y => g y) n` = `gⁿ x` · `show` unfolds one step definitionally
`Nat.rec x step 0` is `x` and `Nat.rec x step (n + 1)` is `step n (Nat.rec x step n)`, by computation:
`show`, `exact`, `rfl` see it without any lemma. -/
example {α : Type} (P : α → Prop) (g : α → α) (x : α) (n : Nat)
    (h : P (g (Nat.rec x (fun _ y => g y) n))) : P (Nat.rec x (fun _ y => g y) (n + 1)) := by
  show P (g (Nat.rec x (fun _ y => g y) n))
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A smaller relation keeps accessibility: R4, R6, R3 -/
example {α : Type} (r q : α → α → Prop) (hsub : ∀ x y, q x y → r x y) (a : α) (ha : Acc r a) :
    Acc q a := by
  induction ha with
    | intro x _ ih =>
      constructor
      intro y hy
      exact ih y (hsub y x hy)

/-! ### W2. A predecessor for every point gives a descending chain: R19, R18, R20 -/
example {α : Type} (s : α → α → Prop) (hs : ∀ x, ∃ y, s y x) (a : α) :
    ∃ c : Nat → α, ∀ k, s (c (k + 1)) (c k) := by
  let pred : α → α := fun x => Classical.choose (hs x)
  let c : Nat → α := fun k => Nat.rec a (fun _ x => pred x) k
  exact ⟨c, fun k => Classical.choose_spec (hs (c k))⟩

/-! ### W3. Building lexicographic steps on pairs of numbers (the two constructors of R7) -/
example : Prod.Lex (· < ·) (· < ·) ((1 : Nat), (9 : Nat)) (2, 0) := .left _ _ (by decide)
example : Prod.Lex (· < ·) (· < ·) ((2 : Nat), (3 : Nat)) (2, 7) := .right _ (by decide)

end H004Guide
