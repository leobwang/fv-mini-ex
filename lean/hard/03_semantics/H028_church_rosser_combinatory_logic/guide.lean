/- Guide for H028 (Church-Rosser for combinatory logic).
Part R: one reference entry per tactic or proof-building move the exercise needs, stated on toy objects
with typed placeholders. Put the cursor before and after the step to see the proof state change in the
infoview. `P` stands for "the rest of your goal". A hypothesis `hP` in an entry is only there to finish
the example; it shows what the goal became.
Part W: worked combinations on the toy objects below, which are NOT the exercise's `Tm`/`Step`/`Par`.
Assumed: Lean basics (E001–E033). No imports: everything here is core Lean.
-/

namespace H028Guide

/-! # Toy objects used by every entry -/

/-- A toy term language: two constants and a binary node. -/
inductive T where
  | a
  | b
  | node (l r : T)

/-- A toy reduction on `T`: reflexive, congruent under `node`, and `node a x` may drop to (a reduct of) `x`. -/
inductive R : T → T → Prop
  | refl (t : T) : R t t
  | node {l l' r r' : T} : R l l' → R r r' → R (.node l r) (.node l' r')
  | drop {x x' : T} : R x x' → R (.node .a x) x'

/-- Reflexive-transitive closure of any relation `r` on any type `α`: zero or more `r`-steps. -/
inductive RT {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (x : α) : RT r x x
  | step {x y z : α} : r x y → RT r y z → RT r x z

/-! # Part R · Reference entries -/

/-! ## Building proofs of an inductive relation -/

/-! ### R1. `exact .ctor h₁ h₂` · closes the goal with a constructor (rule) of the relation
`.node` means `R.node`: Lean reads the expected type `R _ _` to resolve the leading dot. The implicit
`{l l' r r'}` are found by unification; the explicit arguments are proofs of the premises. -/
example (l l' r r' : T) (hl : R l l') (hr : R r r') : R (.node l r) (.node l' r') := by
  exact .node hl hr

/-! ### R2. `exact ⟨w, rfl, h⟩` · closes `∃ y, t = f y ∧ Q y`
The anonymous constructor `⟨_, _, _⟩` builds `Exists.intro` and `And.intro` at once (∧ nests to the
right). `rfl` proves the equation once `w` is chosen; write `_` for `w` to let Lean infer it from `rfl`. -/
example (x x' : T) (hx : R x x') : ∃ y, T.node .b x' = .node .b y ∧ R x y := by
  exact ⟨_, rfl, hx⟩

/-! ## Taking a hypothesis apart: `cases` -/

/-! ### R3. `cases h` on `h : R .a t` · only the rules whose left side can be `.a` survive
`node` and `drop` need a `node` on the left, so only `refl` is left, and it forces `t := .a`:
`t` and `h` leave the context and the goal is rewritten. -/
example (P : T → Prop) (t : T) (h : R .a t) (hP : P .a) : P t := by
  cases h
  exact hP

/-! ### R4. `cases h with | rule names => ?_` on `h : R (.node l r) t` · goal list: one goal per rule
that can match. In each goal `t` is replaced by that rule's right side. In the `drop` goal Lean also
learns `l = .a` and substitutes it everywhere, including in other hypotheses. The names after a rule
go to its premises; a plain `cases h` leaves them unnamed (`a✝`, fix with `rename_i h1 h2`). -/
example (P : T → Prop) (l r t : T) (h : R (.node l r) t)
    (h1 : P (.node l r)) (h2 : ∀ l' r', R l l' → R r r' → P (.node l' r'))
    (h3 : ∀ x', l = .a → R r x' → P x') : P t := by
  cases h with
    | refl => ?_
    | node hl hr => ?_
    | drop hx => ?_
  · exact h1
  · exact h2 _ _ hl hr
  · exact h3 _ rfl hx

/-! ### R5. `obtain ⟨w, rfl, hw⟩ := e` · context: unpack `e : ∃ y, t = f y ∧ Q y`
The pattern `rfl` substitutes the equation `t = f w` away: `t` disappears and every occurrence of it,
in the goal and in other hypotheses, becomes `f w`. -/
example (P : T → Prop) (t x : T) (e : ∃ y, t = .node .b y ∧ R x y)
    (hP : ∀ y, R x y → P (.node .b y)) : P t := by
  obtain ⟨w, rfl, hw⟩ := e
  exact hP w hw

/-! ### R6. `cases he` on `he : T.node l r = T.node l' r'` · context: constructors are injective
Equal `node`s have equal children, so Lean substitutes `l' := l` and `r' := r`. (On `.a = .b`, `cases`
closes the goal instead: different constructors are never equal.) -/
example (P : T → T → Prop) (l r l' r' : T) (he : T.node l r = T.node l' r') (hP : P l r) :
    P l' r' := by
  cases he
  exact hP

/-! ## Induction on a derivation -/

/-! ### R7. `induction h with | refl x => ?_ | step s _ ih => ?_` · goal list: one goal per rule
`RT.step` has two premises, `r x y` (not an `RT`, so no IH) and `RT r y z` (so the IH `ih`).
The names after a rule's name go to its explicit premises first, then to the IHs; `_` drops a name.
`?_` leaves each goal open so you can see it; in a real proof write the tactics there. -/
example {α : Type} (r : α → α → Prop) (Q : α → α → Prop) (x z : α) (h : RT r x z)
    (h1 : ∀ x, Q x x) (h2 : ∀ x y z, r x y → Q y z → Q x z) : Q x z := by
  induction h with
    | refl x => ?_
    | step s _ ih => ?_
  · exact h1 x
  · exact h2 _ _ _ s ih

/-! ### R8. `induction h` on a rule with several recursive premises · one IH per premise, after them
`R.node` has premises `R l l'` and `R r r'`, so its case reads `| node hl hr ihl ihr`. -/
example (Q : T → T → Prop) (s t : T) (h : R s t) (h1 : ∀ t, Q t t)
    (h2 : ∀ l l' r r', Q l l' → Q r r' → Q (.node l r) (.node l' r'))
    (h3 : ∀ x x', Q x x' → Q (.node .a x) x') : Q s t := by
  induction h with
    | refl t => ?_
    | node hl hr ihl ihr => ?_
    | drop hx ihx => ?_
  · exact h1 t
  · exact h2 _ _ _ _ ihl ihr
  · exact h3 _ _ ihx

/-! ### R9. `induction h generalizing c` · the IH holds for every `c`, not just the one in context
Without `generalizing`, `c` and `hc` stay fixed and the IH is about that one `c`, useless when the next
step needs another. `generalizing c` also takes along `hc`, which mentions `c`: the IH becomes
`∀ {c}, Q y c → …`, a function you apply to any `hc' : Q y c'` as `ih hc'`. The IH's binder copies the
statement's: `{c}` gives `∀ {c}, …` (write `ih hc'`), `(c)` gives `∀ (c), …` (write `ih _ hc'`). -/
example {α : Type} (r : α → α → Prop) (Q G : α → α → Prop) {x y c : α} (h : RT r x y) (hc : Q x c)
    (h1 : ∀ x c, Q x c → G x c)
    (h2 : ∀ x y c, r x y → (∀ {c}, Q y c → G y c) → Q x c → G x c) : G x c := by
  induction h generalizing c with
    | refl x => ?_
    | step s _ ih => ?_
  · exact h1 _ _ hc
  · exact h2 _ _ _ s ih hc

/-! # Part W · Worked combinations (on the toy objects, not the exercise's) -/

/-! ### W1. An inversion lemma: R3 for the head, then R4, `rw`, R2 -/
theorem R_b {t : T} (h : R .b t) : t = .b := by
  cases h
  rfl

theorem R_bx {x t : T} (h : R (.node .b x) t) : ∃ x', t = .node .b x' ∧ R x x' := by
  cases h with
    | refl => exact ⟨x, rfl, .refl x⟩
    | node h1 h2 =>
      rw [R_b h1]
      exact ⟨_, rfl, h2⟩

/-! ### W2. Lifting a closure through a context (R7 + R1): `RT r` steps under `f` -/
example {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
    (hf : ∀ {x y}, r x y → s (f x) (f y)) {x y : α} (h : RT r x y) : RT s (f x) (f y) := by
  induction h with
    | refl x => exact .refl _
    | step st _ ih => exact .step (hf st) ih

/-! ### W3. A diamond for the toy `R`: induction on one derivation, `cases` on the other.
The overlap is `node` (left child to `l'`) against `drop` (which needs left child `.a`): invert the
left premise (R3 via `R_a`), then apply the IH of the right child. -/
theorem R_a {t : T} (h : R .a t) : t = .a := by
  cases h
  rfl

example {s t c : T} (ht : R s t) (hc : R s c) : ∃ d, R t d ∧ R c d := by
  induction ht generalizing c with
    | refl t => exact ⟨c, hc, .refl c⟩
    | node hl hr ihl ihr =>
      cases hc with
      | refl => exact ⟨_, .refl _, .node hl hr⟩
      | node hl2 hr2 =>
        obtain ⟨dl, hl1, hl2'⟩ := ihl hl2
        obtain ⟨dr, hr1, hr2'⟩ := ihr hr2
        exact ⟨_, .node hl1 hr1, .node hl2' hr2'⟩
      | drop hx2 =>
        rw [R_a hl]
        obtain ⟨d, h1, h2⟩ := ihr hx2
        exact ⟨d, .drop h1, h2⟩
    | drop hx ihx =>
      cases hc with
      | refl => exact ⟨_, .refl _, .drop hx⟩
      | node hl2 hr2 =>
        rw [R_a hl2]
        obtain ⟨d, h1, h2⟩ := ihx hr2
        exact ⟨d, h1, .drop h2⟩
      | drop hx2 => exact ihx hx2

end H028Guide
