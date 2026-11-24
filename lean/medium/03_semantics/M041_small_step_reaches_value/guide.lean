/- Guide for M041 (Small-step arithmetic reaches its value).
Part R: one reference entry per tactic or proof move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis such as `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a toy language `Tm` that is NOT the exercise's `Expr`.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M041Guide

/-! ## Toy objects used by the entries (not the exercise's) -/

/-- Toy terms: a value, a one-hole wrapper, a pair. -/
inductive Tm where
  | val (n : Nat)
  | wrap (t : Tm)
  | pair (s t : Tm)

/-- The value of a toy term. -/
def ev : Tm → Nat
  | .val n => n
  | .wrap t => ev t
  | .pair s t => ev s + ev t

/-- Toy single step: unwrap a value, or step inside a wrapper. -/
inductive TStep : Tm → Tm → Prop
  | unwrap {n : Nat} : TStep (.wrap (.val n)) (.val n)
  | cong {t t' : Tm} : TStep t t' → TStep (.wrap t) (.wrap t')

/-- Zero or more toy steps. -/
inductive TStar : Tm → Tm → Prop
  | refl (t : Tm) : TStar t t
  | step {a b c : Tm} : TStep a b → TStar b c → TStar a c

/-! # Part R · Reference entries -/

/-! ## Facts about one step: induction on the step -/

/-! ### R1. `induction h` on `h : TStep a b` · goal list: one goal per rule of the relation
Each goal has the rule's `a` and `b` in place of yours; a rule with a premise `TStep t t'` also
gives its proof `a✝` and the induction hypothesis `a_ih✝` for it. `‹_›` is "a hypothesis of the
expected type", found by `assumption`: it passes the inaccessible `a_ih✝` without naming it. -/
example (P : Tm → Tm → Prop) (h1 : ∀ n, P (.wrap (.val n)) (.val n))
    (h2 : ∀ t t', P t t' → P (.wrap t) (.wrap t')) (a b : Tm) (h : TStep a b) : P a b := by
  induction h
  · exact h1 _
  · exact h2 _ _ ‹_›

/-! ### R2. `simp_all [f]` · closes the goal: simplify the goal and every hypothesis with each other,
unfolding the defining equations of `f`. A hypothesis `x = y` is used to rewrite the others. -/
example (n : Nat) : ev (.val n) = ev (.wrap (.val n)) := by
  simp_all [ev]

example (f : Tm → Nat) (s s' : Tm) (k : Nat) (ih : f s' = f s) : f s' + k = f s + k := by
  simp_all

/-! ## Facts about many steps: induction on the closure -/

/-! ### R3. `induction h with | refl t => … | step s hs ih => …` on `h : TStar a b` · goal list
`refl`: `a` and `b` are both `t`. `step`: `s : TStep a b'`, `hs : TStar b' b` (the rest of the run) and
`ih` (the claim for `hs`). -/
example (P : Tm → Tm → Prop) (hr : ∀ t, P t t)
    (hst : ∀ a b c, TStep a b → P b c → P a c) (a b : Tm) (h : TStar a b) : P a b := by
  induction h with
    | refl t => exact hr t
    | step s hs ih => exact hst _ _ _ s ih

/-! R3, one goal at a time: without `with`, names are inaccessible; `rename_i` names them. -/
example (P : Tm → Tm → Prop) (hr : ∀ t, P t t)
    (hst : ∀ a b c, TStep a b → P b c → P a c) (a b : Tm) (h : TStar a b) : P a b := by
  induction h
  · exact hr _
  rename_i s hs ih
  exact hst _ _ _ s ih

/-! ### R4. `induction h` with another hypothesis `k` about an index of `h` · the IH takes `k` as a premise
`k : Q b` mentions `b`, which the induction replaces, so Lean first moves `k` into the goal: the IH
becomes `ih : Q b → …` and `k` is re-introduced for the case's own `b`. -/
example (Q : Tm → Prop) (R : Tm → Tm → Prop) (hr : ∀ t, Q t → R t t)
    (hst : ∀ a b c, TStep a b → (Q c → R b c) → Q c → R a c) (a b : Tm) (h : TStar a b) (k : Q b) :
    R a b := by
  induction h
  · exact hr _ k
  rename_i s hs ih
  exact hst _ _ _ s ih k

/-! ### R5. `exact .ctor args` · closes the goal with a rule of the relation
`.refl _` means `TStar.refl _`: Lean reads the namespace off the goal's head `TStar`. `_` is an explicit
argument Lean can infer from the goal. Implicit `{a b c}` arguments are never written. -/
example (t : Tm) : TStar t t := by
  exact .refl _

example (a b c : Tm) (s : TStep a b) (r : TStar b c) : TStar a c := by
  exact .step s r

example (n : Nat) : TStar (.wrap (.val n)) (.val n) := by
  exact .step .unwrap (.refl _)

/-! ### R6. `rw [h₁]`, `rw [h₂]` · goal rewritten; once it is `x = x`, `rw` closes it with `rfl`
`rw [h₁, h₂]` does both in one step. -/
example (f : Tm → Nat) (a b c : Tm) (h₁ : f c = f b) (h₂ : f b = f a) : f c = f a := by
  rw [h₁]
  rw [h₂]

/-! ### R7. Definitional unfolding · `exact h` accepts `h` when its type unfolds to the goal
`ev (.val n)` is `n` by the first equation of `ev`, so `h : ev (.val n) = m` proves `n = m` as is;
the same goes for `rfl` on `ev t = ev t` (a `refl` case). -/
example (n m : Nat) (h : ev (.val n) = m) : n = m := by
  exact h

/-! ## Building many-step runs out of pieces -/

/-! ### R8. `induction t with | val n => … | wrap t ih => … | pair s t ihs iht => …` · goal list
Structural induction on a term: one goal per constructor, one IH per argument of type `Tm`. -/
example (P : Tm → Prop) (hv : ∀ n, P (.val n)) (hw : ∀ t, P t → P (.wrap t))
    (hp : ∀ s t, P s → P t → P (.pair s t)) (t : Tm) : P t := by
  induction t with
    | val n => exact hv n
    | wrap t ih => exact hw t ih
    | pair s t ihs iht => exact hp s t ihs iht

/-! R8, one goal at a time. -/
example (P : Tm → Prop) (hv : ∀ n, P (.val n)) (hw : ∀ t, P t → P (.wrap t))
    (hp : ∀ s t, P s → P t → P (.pair s t)) (t : Tm) : P t := by
  induction t
  · exact hv _
  · exact hw _ ‹_›
  rename_i s t ihs iht
  exact hp s t ihs iht

/-! ### R9. `refine lem x ?_` · goal → the goals for the `?_` holes
`lem x ?_` is the lemma applied to arguments; each `?_` is an argument you prove next, as a new goal.
Here `tr` is a transitivity fact: `refine tr hab ?_` keeps only the second half to prove. -/
example (r : Tm → Tm → Prop) (tr : ∀ {x y z : Tm}, r x y → r y z → r x z) (a b c : Tm)
    (hab : r a b) (hbc : r b c) : r a c := by
  refine tr hab ?_
  exact hbc

/-! ### R10. A rule is a function · `exact .cong` proves `∀ {a b}, TStep a b → TStep (g a) (g b)`
A rule with a premise is itself a proof of "premise → conclusion" for all its implicit arguments,
so it can be passed wherever such a function is expected. `(fun x => .wrap x) a` is `.wrap a` by
β-reduction (substituting `a` for `x`), which Lean does by itself. -/
example : ∀ {a b : Tm}, TStep a b → TStep ((fun x => Tm.wrap x) a) ((fun x => Tm.wrap x) b) := by
  exact .cong

/-! # Part W · Worked combinations on `Tm` (not the exercise's `Expr`) -/

/-! ### W1. A step never changes `ev`: R1 on every goal with R2 -/
example (t t' : Tm) (h : TStep t t') : ev t' = ev t := by
  induction h <;> simp_all [ev]

/-! ### W2. Lifting a run through `wrap`: R3, R5, R10 -/
example (a b : Tm) (h : TStar a b) : TStar (.wrap a) (.wrap b) := by
  induction h with
    | refl t => exact .refl _
    | step s _ ih => exact .step (.cong s) ih

/-! ### W3. `wrap (wrap (val n))` reaches `val n`: R9 with a transitivity fact, R5 -/
example (tr : ∀ {x y z : Tm}, TStar x y → TStar y z → TStar x z)
    (lift : ∀ {x y : Tm}, TStar x y → TStar (.wrap x) (.wrap y)) (n : Nat) :
    TStar (.wrap (.wrap (.val n))) (.val n) := by
  refine tr (lift (.step .unwrap (.refl _))) ?_
  exact .step .unwrap (.refl _)

end M041Guide
