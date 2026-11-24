/- Guide for E052 (Pairs).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries use the guide's own functions `mapFst` and `mulPair` below, NOT the exercise's `swap`
and `addPair`.
Part W: worked combinations on `mapFst` and `mulPair` (W1–W4).
Assumed: Lean basics (E001–E033), in particular `rfl` (E001), `exact`/`apply` (E003), `unfold` (E012),
structures and projections (E017).
-/

namespace E052Guide

/-- Apply `f` to the first component, keep the second. Built from the projections `.1`, `.2`. -/
def mapFst {α β γ : Type} (f : α → γ) (p : α × β) : γ × β := (f p.1, p.2)

/-- Defined by a pattern-matching lambda: `fun (a, b) => …` is `fun x => match x with | (a, b) => …`. -/
def mulPair : Nat × Nat → Nat := fun (a, b) => a * b

/-! # Part R · Reference entries -/

/-! ## Projections and eta -/

/-! ### R1. `dsimp only` · goal: a projection of a literal pair → that component
`(a, b).1` is printed `(a, b).fst`; `dsimp only` reduces it to `a` (and `(a, b).snd` to `b`).
If both sides of an equation then agree, eta `(p.fst, p.snd) = p` included, it closes the goal (W4). -/
example {α β : Type} (a : α) (b : β) (P : α → Prop) (h : P a) : P (a, b).1 := by
  dsimp only
  exact h

/-! ### R2. `rfl` · closes `(p.1, p.2) = p` (eta for pairs: rebuilding a pair from its projections
gives it back, by definition). `rfl` also unfolds definitions and reduces projections first. -/
example {α β : Type} (p : α × β) : (p.1, p.2) = p := by
  rfl

/-! ### R3. `unfold D` · goal: the defined name `D` → its body -/
example {α β γ : Type} (f : α → γ) (p : α × β) (P : γ × β → Prop) (h : P (f p.1, p.2)) :
    P (mapFst f p) := by
  unfold mapFst
  exact h

/-! ## Extensionality -/

/-! ### R4. `apply Prod.ext` · goal `x = y` → two goals `x.fst = y.fst` and `x.snd = y.snd`
`Prod.ext : x.fst = y.fst → x.snd = y.snd → x = y` (`x y` implicit). In term mode:
`Prod.ext h₁ h₂`. -/
example {α β : Type} (a : α) (b : β) (p : α × β) (h1 : p.1 = a) (h2 : p.2 = b) :
    p = (a, b) := by
  apply Prod.ext
  exact h1
  exact h2

/-! ## Taking a pair apart -/

/-! ### R5. `obtain ⟨a, b⟩ := p` · context: `p : α × β` → `a : α`, `b : β`; goal `P p` → `P (a, b)` -/
example {α β : Type} (p : α × β) (P : α × β → Prop) (h : ∀ a b, P (a, b)) : P p := by
  obtain ⟨a, b⟩ := p
  exact h a b

/-! ### R6. `dsimp only` · goal: a `match` on a literal pair → the matching branch
Unfolding a pattern-lambda definition (R3) leaves `match (x, y) with | (a, b) => a * b`. -/
example (x y : Nat) (P : Nat → Prop) (h : P (x * y)) : P (mulPair (x, y)) := by
  unfold mulPair
  dsimp only
  exact h

/-! ## Arithmetic -/

/-! ### R7. `Nat.add_comm` · `∀ (n m : Nat), n + m = m + n` · `exact Nat.add_comm a b` closes the goal
`exact` accepts the term when the goal equals its type after unfolding (R3, R6 are optional). -/
example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

/-! # Part W · Worked combinations (on `mapFst` and `mulPair`, not the exercise's functions) -/

/-! ### W1. Unfold, then eta: R3 → R2 (`rfl` also unfolds `id`) -/
example {α β : Type} (p : α × β) : mapFst id p = p := by
  unfold mapFst
  rfl

/-! ### W2. Take the pair apart, unfold, reduce, close: R5 → R3 → R1, R6 → `Nat.mul_comm` -/
example (p : Nat × Nat) : mulPair p = mulPair (p.2, p.1) := by
  obtain ⟨a, b⟩ := p
  unfold mulPair
  dsimp only
  exact Nat.mul_comm a b

/-! ### W3. Extensionality in term mode (R4) -/
example {α β : Type} (a : α) (b : β) (p : α × β) (h1 : p.1 = a) (h2 : p.2 = b) : p = (a, b) :=
  Prod.ext h1 h2

/-! ### W4. `dsimp only` closes an eta goal by itself: R3 → R1 (no `rfl` afterwards) -/
example {α β : Type} (p : α × β) : mapFst (fun x => x) p = p := by
  unfold mapFst
  dsimp only

end E052Guide
