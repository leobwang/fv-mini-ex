/- Guide for H006 (Newman's lemma).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q`, `C` stand for "the rest of your goal": the step changes only the part shown. A hypothesis
`h` in an entry is only there to finish the example; it shows what the goal became.
The entries about derivations use the toy relation `EvenPath` and the toy colour system `Col`/`Next`
below, which are NOT the exercise's `Star`, `P` and `R4`.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace H006Guide

/-! # Toy objects used by the entries -/

/-- A toy inductive relation: `EvenPath r a b` says `a` reaches `b` in an EVEN number of `r`-steps.
`nil` is the empty path; `two` prepends two steps to a path. -/
inductive EvenPath {α : Type} (r : α → α → Prop) : α → α → Prop
  | nil (a : α) : EvenPath r a a
  | two {a b c d : α} : r a b → r b c → EvenPath r c d → EvenPath r a d

/-- A toy definition whose body is a `∀`. -/
def Always {α : Type} (Q : α → Prop) : Prop := ∀ x, Q x

/-- A toy definition whose body is an `∃` of a pair. -/
def Both {α : Type} (Q Q' : α → Prop) : Prop := ∃ z, Q z ∧ Q' z

/-- A toy finite system: four colours and a step relation red → green, red → blue,
green → white, blue → white (a diamond). -/
inductive Col where
  | red | green | blue | white

inductive Next : Col → Col → Prop
  | rg : Next .red .green
  | rb : Next .red .blue
  | gw : Next .green .white
  | bw : Next .blue .white

/-! # Part R · Reference entries -/

/-! ## Derivations of an inductive relation -/

/-! ### R1. `induction p` (with `p : EvenPath r a b`) · goal list: one goal per constructor
The indices `a`, `b` are replaced by each constructor's pattern. A hypothesis that mentions an index
(here `hb : Q b`) is generalized automatically: it reappears in each goal AND becomes a premise of the
induction hypothesis `a_ih✝ : Q d✝ → Q c✝`. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)
    (back : ∀ x y, r x y → Q y → Q x) : Q a := by
  induction p
  exact hb
  next _ _ _ _ s t _ ih => exact back _ _ s (back _ _ t (ih hb))

/-! ### R2. `rename_i x y …` · context: names the most recent inaccessible (`✝`) variables
The names go to the LAST `k` inaccessible variables of the current goal, in order. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)
    (back : ∀ x y, r x y → Q y → Q x) : Q a := by
  induction p
  exact hb
  rename_i s t _ ih
  exact back _ _ s (back _ _ t (ih hb))

/-! ### R3. `induction p with | nil a => ?_ | two s t _ ih => ?_` · goal list, with names
`| c x y => …` names only the EXPLICIT arguments of constructor `c` (premises; not `{a b c d}`), then
the IH of each recursive premise. `?_` leaves the goal open; normally a tactic block follows `=>`. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)
    (back : ∀ x y, r x y → Q y → Q x) : Q a := by
  induction p with
    | nil a => ?_
    | two s t _ ih => ?_
  exact hb
  exact back _ _ s (back _ _ t (ih hb))

/-! ### R4. `exact .c args` · goal closed by building a derivation from constructors
`.two s t p` means `EvenPath.two s t p`: a leading `.` takes the constructor from the goal's type.
Implicit arguments (`{a b c d}`) are inferred; explicit ones (`nil a`) may be given as `_`. -/
example {α : Type} (r : α → α → Prop) (a b c : α) (s : r a b) (t : r b c) : EvenPath r a c := by
  exact .two s t (.nil _)

/-! ### R5. `cases p with | nil a => ?_ | two s t q => ?_` · goal list: one goal per constructor, no IH
In the `nil` goal the end index is unified with the start: `b` is replaced by `a` everywhere. -/
example {α : Type} (r : α → α → Prop) (P : α → α → Prop) (a b : α) (p : EvenPath r a b)
    (h0 : P a a) (h2 : ∀ x y z w, r x y → r y z → EvenPath r z w → P x w) : P a b := by
  cases p with
    | nil a => ?_
    | two s t q => ?_
  exact h0
  exact h2 _ _ _ _ s t q

/-! ## Definitions, `∃`, well-founded induction -/

/-! ### R6. `intro x` on a goal that is a definition with a `∀` body · context gains `x`
`intro` unfolds the definition (`Always Q` is `∀ x, Q x`) to find the binder. -/
example {α : Type} (Q : α → Prop) (h : ∀ x, Q x) : Always Q := by
  intro x
  exact h x

/-! ### R7. `induction a using hw.induction` · well-founded induction on `a`
`hw : WellFounded (fun b a => r a b)` says there is no infinite chain `a₀ r a₁ r a₂ …` (`r` terminates).
`WellFounded.induction` then lets you prove `C a` assuming `C y` for every `y` with `r a y`: the IH
covers everything ONE step after `a`. Write `with | _ a ih =>` to name `a` and the IH (W1). -/
example {α : Type} (r : α → α → Prop) (hw : WellFounded (fun b a => r a b)) (C : α → Prop)
    (step : ∀ a, (∀ y, r a y → C y) → C a) (a : α) : C a := by
  induction a using hw.induction
  rename_i a ih
  exact step a ih

/-! ### R8. `exact ⟨z, hq, hq'⟩` · goal `∃ z, Q z ∧ Q' z` closed (also through a definition)
The anonymous constructor `⟨…⟩` unfolds `Both Q Q'` to its `∃` body; `⟨z, hq, hq'⟩` is
`⟨z, ⟨hq, hq'⟩⟩` (it nests to the right). -/
example {α : Type} (Q Q' : α → Prop) (z : α) (hq : Q z) (hq' : Q' z) : Both Q Q' := by
  exact ⟨z, hq, hq'⟩

/-! ### R9. `obtain ⟨z, hq, hq'⟩ := e` · context: an `∃ z, Q z ∧ Q' z` → a witness and two facts
`e` may be an application such as `f _ hx`: `_` asks Lean to infer that argument from `hx`'s type. -/
example {α : Type} (Q Q' : α → Prop) (R : α → Prop) (G : Prop) (f : ∀ x, R x → Both Q Q')
    (x : α) (hx : R x) (h : ∀ z, Q z → Q' z → G) : G := by
  obtain ⟨z, hq, hq'⟩ := f _ hx
  exact h z hq hq'

/-! ## Concrete finite relations -/

/-! ### R10. `cases h` with `h : Next .red x` · goal list: one goal per constructor that FITS
Only constructors whose first index is `.red` survive (`rg`, `rb`); `x` is replaced by their target. -/
example (P : Col → Prop) (x : Col) (h : Next .red x) (hg : P .green) (hb : P .blue) : P x := by
  cases h
  exact hg
  exact hb

/-! ### R11. `first | tac₁ | tac₂ | …` · tries each tactic in order; keeps the first that succeeds
With `all_goals first | … | …` one list of candidate proofs is tried on every goal (W2). -/
example (A B : Prop) (hb : B) : A ∨ B := by
  first
    | exact Or.inl hb
    | exact Or.inr hb

/-! ### R12. `nomatch h` · closes any goal when no constructor fits `h`
`Next .white x` has no constructor (white has no outgoing step). As a term it proves
`∀ z, ¬ Next .white z`: `fun z h => nomatch h`. -/
example (G : Prop) (x : Col) (h : Next .white x) : G := by
  nomatch h

/-! ### R13. `absurd h hn` · closes any goal from `h : A` and `hn : ¬ A` (`absurd : a → ¬a → b`) -/
example (A G : Prop) (h : A) (hn : ¬ A) : G := by
  exact absurd h hn

/-! ### R14. `intro h` on `¬ A` · context gains `h : A`; goal becomes `False` (`¬ A` is `A → False`) -/
example (A : Prop) (hn : A → False) : ¬ A := by
  intro h
  exact hn h

/-! ### R15. `subst h` (with `h : y = e`, `y` a local variable) · context and goal: `y` → `e` everywhere
`h` disappears. Either side may be the variable; if both are variables, the right one goes. -/
example (P : Col → Prop) (y : Col) (h : y = .red) (hp : P .red) : P y := by
  subst h
  exact hp

/-! ### R16. `cases h` with `h : Col.red = Col.blue` · goal closed: different constructors are never equal -/
example (G : Prop) (h : Col.red = Col.blue) : G := by
  cases h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `intro` first, then well-founded induction with named IH: a terminating `r` is irreflexive -/
example {α : Type} (r : α → α → Prop) (hw : WellFounded (fun b a => r a b)) : ∀ a, ¬ r a a := by
  intro a
  induction a using hw.induction with
    | _ a ih =>
      intro h
      exact ih a h h

/-! ### W2. `cases h1 <;> cases h2`, then one `first` list for all goals: the diamond closes in one step -/
example : ∀ a b c, Next a b → Next a c → ∃ d, (d = b ∨ Next b d) ∧ (d = c ∨ Next c d) := by
  intro a b c h1 h2
  cases h1 <;> cases h2
  all_goals first
    | exact ⟨_, .inl rfl, .inl rfl⟩
    | exact ⟨.white, .inr .gw, .inr .bw⟩
    | exact ⟨.white, .inr .bw, .inr .gw⟩

/-! ### W3. Two equations with the same variable: `subst` one, then `cases` the clash -/
example (x : Col) (h1 : x = .red) (h2 : x = .blue) : False := by
  subst h1
  cases h2

/-! ### W4. A derivation out of a dead end: `cases` it; the `two` case has a step out of `white` -/
example (x : Col) (p : EvenPath Next .white x) : x = .white := by
  cases p with
    | nil => rfl
    | two s _ _ => nomatch s

end H006Guide
