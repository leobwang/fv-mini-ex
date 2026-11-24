/- Guide for H027 (Typed combinators are normalising (Tait)).
Part R: one reference entry per tactic or proof-building move the exercise needs, stated on toy objects
with typed placeholders. Put the cursor before and after the step to see the proof state change in the
infoview. `P`, `Q`, `G` stand for "the rest of your goal". A hypothesis such as `hP` in an entry is only
there to finish the example; it shows what the goal became.
Part W: worked combinations on the toy objects below, which are NOT the exercise's
`Ty`/`Tm`/`HasTy`/`Step`/`Star`/`Red`.
Assumed: Lean basics (E001–E033). No imports: everything here is core Lean.
-/

namespace H027Guide

/-! # Toy objects used by the entries -/

/-- Toy types: a base type `o` and function types `fn A B`. -/
inductive U where
  | o
  | fn (A B : U)

/-- Toy terms: two constants and a binary node. -/
inductive E where
  | a
  | b
  | node (l r : E)

/-- A toy one-step reduction: `node a x` drops to `x`, and a step may happen in either child. -/
inductive Stp : E → E → Prop
  | drop {x : E} : Stp (.node .a x) x
  | left {l l' r : E} : Stp l l' → Stp (.node l r) (.node l' r)
  | right {l r r' : E} : Stp r r' → Stp (.node l r) (.node l r')

/-- Zero or more `r`-steps, for any relation `r : α → α → Prop` on any type `α`. -/
inductive RT {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (x : α) : RT r x x
  | step {x y z : α} : r x y → RT r y z → RT r x z

/-- `t` is irreducible: no `Stp` leaves it. -/
def Nf (t : E) : Prop := ∀ t', ¬ Stp t t'

/-- `t` reduces to an irreducible term. -/
def Ends (t : E) : Prop := ∃ v, RT Stp t v ∧ Nf v

/-- A toy predicate defined by recursion on the toy type: `Q` at `o`; at `fn A B`, also maps
    `Good A` arguments to `Good B` results (for any predicate `Q : E → Prop`). -/
def Good (Q : E → Prop) : U → E → Prop
  | .o, t => Q t
  | .fn A B, t => Q t ∧ ∀ u, Good Q A u → Good Q B (.node t u)

/-- A toy typing judgement on `E`. -/
inductive Ok : E → U → Prop
  | a : Ok .a .o
  | b {A : U} : Ok .b (.fn A A)
  | node {l r : E} {A B : U} : Ok l (.fn A B) → Ok r A → Ok (.node l r) B

/-! # Part R · Reference entries -/

/-! ## Closures: induction and building derivations -/

/-! ### R1. `induction h with | refl x => ?_ | step s _ ih => ?_` · goal list: one goal per rule
`RT.step` has two premises: `r x y` (not an `RT`, so no IH) and `RT r y z` (so the IH `ih`). Names after
a rule go to its explicit premises first, then to the IHs; `_` drops a name. A hypothesis that mentions
the right end `y` of `h` (here `hy`) is taken along automatically: in the `step` case it is
`hy : Q z✝` and the IH is the implication `ih : Q z✝ → Q y✝`, so write `ih hy`. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (x y : α) (h : RT r x y) (hy : Q y)
    (hP : ∀ x y, r x y → Q y → Q x) : Q x := by
  induction h with
    | refl x => ?_
    | step s _ ih => ?_
  · exact hy
  · exact hP _ _ s (ih hy)

/-! ### R2. `exact .step s h` · closes the goal with a rule of the relation
`.step` means `RT.step`: Lean reads the expected type `RT r _ _` to resolve the leading dot. The
implicit `{x y z}` are found by unification; the explicit arguments are the premises' proofs. -/
example {α : Type} (r : α → α → Prop) (x y z : α) (s : r x y) (h : RT r y z) : RT r x z := by
  exact .step s h

/-! ### R3. `exact .step (.left s) h` · rules nest: a step in a child is a step of the node
The inner `.left` is resolved against the expected type of `.step`'s first premise, `Stp _ _`. -/
example (l l' r v : E) (s : Stp l l') (h : RT Stp (.node l' r) v) : RT Stp (.node l r) v := by
  exact .step (.left s) h

/-! ## Normal forms: `∀ t', ¬ Stp t t'` -/

/-! ### R4. `intro t' h` on `⊢ Nf t` · context gains `t'` and `h : Stp t t'`; goal becomes `False`
`intro` unfolds the definition `Nf` by itself, and `¬ A` is `A → False`, so it introduces `h : A`. -/
example (t : E) (hP : ∀ t', Stp t t' → False) : Nf t := by
  intro t' h
  exact hP t' h

/-! ### R5. `cases h` on `h : Stp .b t'` · closes the goal when no rule can produce `h`
Every rule of `Stp` has a `node` on the left, so no case is left. -/
example (t' : E) (h : Stp .b t') : False := by
  cases h

/-! ### R6. `cases h with | left h => ?_ | right h => ?_` · goal list: one goal per rule that fits
On `h : Stp (.node .b x) t'`, `drop` needs `.a` on the left and is dropped; `left` and `right` survive,
and in each `t'` is replaced by that rule's right side. The name after a rule goes to its premise. -/
example (P : Prop) (x t' : E) (h : Stp (.node .b x) t')
    (hl : ∀ l', Stp .b l' → P) (hr : ∀ x', Stp x x' → P) : P := by
  cases h with
    | left h => ?_
    | right h => ?_
  · exact hl _ h
  · exact hr _ h

/-! ### R7. `exact hx _ h` · use `hx : Nf x` as a function: `hx y : ¬ Stp x y`, and `hx y h : False` -/
example (x y : E) (hx : Nf x) (h : Stp x y) : False := by
  exact hx _ h

/-! ## A predicate defined by recursion on a type -/

/-! ### R8. `cases A with | o => ?_ | fn A B => ?_` · goal list: one goal per type former
After the split, `Good Q .o t` *is* `Q t` and `Good Q (.fn A B) t` *is* a conjunction, by definition
(the infoview still prints `Good Q U.o t`): `exact h` and `h.1` work with no `unfold`. -/
example (Q : E → Prop) (A : U) (t : E) (h : Good Q A t) : Q t := by
  cases A with
    | o => ?_
    | fn A B => ?_
  · exact h
  · exact h.1

/-! ### R9. `exact h.2 u hu` · use the arrow clause: `h.2 : ∀ u, Good Q A u → Good Q B (t.node u)`
`h.1` and `h.2` are the two halves of a conjunction; `h.2 u hu` applies the second one. -/
example (Q : E → Prop) (A B : U) (t u : E) (h : Good Q (.fn A B) t) (hu : Good Q A u) :
    Good Q B (.node t u) := by
  exact h.2 u hu

/-! ### R10. `induction A generalizing t with | o => ?_ | fn A B ihA ihB => ?_` · goal list
Induction on the type, with an IH for each of `A` and `B`. Without `generalizing t` the IH would be about
the one `t` in context; with it, `ihB : ∀ {t : E}, G B t → Good Q B t` holds for every `t` (here
`node t u` is needed). `h` mentions `t`, so it is taken along. The binder copies the statement's:
`{t}` gives `∀ {t}, …`. -/
example (Q : E → Prop) (G : U → E → Prop) (A : U) {t : E} (h : G A t)
    (h1 : ∀ t, G .o t → Good Q .o t)
    (h2 : ∀ A B t, (∀ {t}, G B t → Good Q B t) → G (.fn A B) t → Good Q (.fn A B) t) :
    Good Q A t := by
  induction A generalizing t with
    | o => ?_
    | fn A B ihA ihB => ?_
  · exact h1 t h
  · exact h2 A B t ihB h

/-! ## `∃ … ∧ …`: taking apart and building -/

/-! ### R11. `obtain ⟨v, hv, nv⟩ := h` on `h : Ends t` · context: `h` → a witness and two facts
`obtain` unfolds `Ends` to `∃ v, RT Stp t v ∧ Nf v` by itself; the pattern splits `∃` and `∧` at once. -/
example (P : Prop) (t : E) (h : Ends t) (hP : ∀ v, RT Stp t v → Nf v → P) : P := by
  obtain ⟨v, hv, nv⟩ := h
  exact hP v hv nv

/-! ### R12. `obtain ⟨⟨v, hv, nv⟩, hf⟩ := h` · nested pattern for `(∃ v, A v ∧ B v) ∧ F` -/
example {α : Type} (A B : α → Prop) (F P : Prop) (h : (∃ v, A v ∧ B v) ∧ F)
    (hP : ∀ v, A v → B v → F → P) : P := by
  obtain ⟨⟨v, hv, nv⟩, hf⟩ := h
  exact hP v hv nv hf

/-! ### R13. `exact ⟨v, .step s hv, nv⟩` · closes `⊢ Ends t` (an `∃ … ∧ …` behind a definition)
`⟨_, _, _⟩` builds the `∃` and the `∧` at once (`∧` nests to the right), and the middle part may itself
be a rule application (R2). -/
example (t t' v : E) (s : Stp t t') (hv : RT Stp t' v) (nv : Nf v) : Ends t := by
  exact ⟨v, .step s hv, nv⟩

/-! ### R14. `exact ⟨hq, fun u hu => e⟩` · closes `⊢ Q ∧ ∀ u, A u → B u`
A `∀ u, A u → B u` is proved by a function from `u` and `hu : A u` to a proof of `B u`. -/
example {α : Type} (Q : Prop) (A B : α → Prop) (hq : Q) (g : ∀ u, A u → B u) :
    Q ∧ ∀ u, A u → B u := by
  exact ⟨hq, fun u hu => g u hu⟩

/-! ### R15. `refine ⟨⟨_, .refl _, nt⟩, fun x hx => ?_⟩` · goal → only the hole under `fun`
Fill the first half now; `?_` under `fun x hx` leaves one goal whose context gains `x` and `hx`. The
witness `_` is read off from `.refl _` (zero steps: `v := t`). -/
example (A B : E → Prop) (t : E) (nt : Nf t) (g : ∀ x, A x → B x) :
    Ends t ∧ ∀ x, A x → B x := by
  refine ⟨⟨_, .refl _, nt⟩, fun x hx => ?_⟩
  exact g x hx

/-! ## Backward reasoning and induction on typing -/

/-! ### R16. `apply back .drop` · goal: `G (node a x)` → `G x`
`back : ∀ {t t'}, Stp t t' → G t' → G t` says `G` is closed under backward steps. Giving the step `.drop`
fixes `t := node a x`, `t' := x` by unification with the goal, and the premise `G t'` is the new goal. -/
example (G : E → Prop) (back : ∀ {t t'}, Stp t t' → G t' → G t) (x : E) (h : G x) :
    G (.node .a x) := by
  apply back .drop
  exact h

/-! ### R17. `induction h with | a => ?_ | b => ?_ | node _ _ ih1 ih2 => ?_` · one goal per rule
Induction on a typing derivation `h : Ok t A`. `Ok.node` has two `Ok` premises, so its case gets two
IHs, after the two premises (`_ _` drops their names). The goal's `t` and `A` become each rule's. -/
example (G : E → U → Prop) {t : E} {A : U} (h : Ok t A) (ha : G .a .o) (hb : ∀ A, G .b (.fn A A))
    (hn : ∀ l r A B, G l (.fn A B) → G r A → G (.node l r) B) : G t A := by
  induction h with
    | a => ?_
    | b => ?_
    | node _ _ ih1 ih2 => ?_
  · exact ha
  · exact hb _
  · exact hn _ _ _ _ ih1 ih2

/-! # Part W · Worked combinations (on the toy objects, not the exercise's) -/

/-! ### W1. A normal form one level deep: R4, R6, then R5 / R7 in the two cases -/
theorem nf_b : Nf .b := by
  intro t' h
  cases h

example {x : E} (hx : Nf x) : Nf (.node .b x) := by
  intro t' h
  cases h with
    | left h => exact nf_b _ h
    | right h => exact hx _ h

/-! ### W2. `Ends` is closed under backward steps: R11, then R13 -/
example {t t' : E} (s : Stp t t') (h : Ends t') : Ends t := by
  obtain ⟨v, hv, nv⟩ := h
  exact ⟨v, .step s hv, nv⟩

/-! ### W3. Induction on the type with a trivial predicate: R10, then R14 with the IH -/
example (A : U) {t : E} : Good (fun _ => True) A t := by
  induction A generalizing t with
    | o => trivial
    | fn A B _ ihB => exact ⟨trivial, fun u _ => ihB⟩

end H027Guide
