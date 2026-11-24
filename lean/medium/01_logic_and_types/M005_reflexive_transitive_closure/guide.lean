/- Guide for M005 (Reflexive-transitive closure).
Part R: one reference entry per tactic or term-building move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q`, `G` stand for "the rest of your goal": the step changes only the part shown. A hypothesis
`h` in an entry is only there to finish the example; it shows what the goal became.
The entries about derivations use the toy relation `EvenPath` below, which is NOT the exercise's
`Star`: `EvenPath` takes steps two at a time.
Part W: worked combinations on `EvenPath`.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M005Guide

/-! # Toy object used by the entries (not the exercise's) -/

/-- `EvenPath r a d`: `d` is reached from `a` by an EVEN number of `r`-steps.
`nil a` is the empty path at `a`; `two s t p` puts two steps `s : r a b`, `t : r b c` in front of a
path `p : EvenPath r c d`. A proof of `EvenPath r a d` is a finite chain of rules (a derivation). -/
inductive EvenPath {α : Type} (r : α → α → Prop) : α → α → Prop
  | nil (a : α) : EvenPath r a a
  | two {a b c d : α} : r a b → r b c → EvenPath r c d → EvenPath r a d

/-! # Part R · Reference entries -/

/-! ## Building derivations: constructors are functions -/

/-! ### R1. `exact .nil a` · closes `EvenPath r a a` with the constructor that has no premise
`.nil a` is short for `EvenPath.nil a`: a leading `.` looks the name up in the namespace of the
expected type. `a` is an EXPLICIT argument of `nil` (written in `( )`), so it must be given, or
written `_` for Lean to infer. -/
example {α : Type} (r : α → α → Prop) (a : α) : EvenPath r a a := by
  exact .nil a

/-! ### R2. `exact .two s t p` · closes the goal with a constructor that has premises
`EvenPath.two : r a b → r b c → EvenPath r c d → EvenPath r a d`; its points `{a b c d}` are IMPLICIT
(in `{ }`): Lean reads them off `s`, `t`, `p` and the goal. Arguments nest: `.two s t (.nil c)` is a
path of exactly two steps. -/
example {α : Type} (r : α → α → Prop) (a b c d : α) (s : r a b) (t : r b c) (p : EvenPath r c d) :
    EvenPath r a d := by
  exact .two s t p

example {α : Type} (r : α → α → Prop) (a b c : α) (s : r a b) (t : r b c) : EvenPath r a c := by
  exact .two s t (.nil c)

/-! ## Induction on a derivation -/

/-! ### R3. `induction p` (`p : EvenPath r a b`) · goal list: one goal per constructor
The indices `a`, `b` of `p` are replaced by each constructor's pattern (`nil`: both become one point `a✝`).
A hypothesis that mentions an index (here `hb : Q b`) is generalized automatically: it reappears in
each goal AND becomes a premise of the induction hypothesis, `a_ih✝ : Q d✝ → Q c✝`. The IH is a
function: feed it a proof of its premise (R5). The `✝` names cannot be typed; `next x₁ … xₖ => tac`
works on the first goal and renames its last `k` inaccessible names to `x₁ … xₖ` (R4 is the usual way). -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)
    (back : ∀ x y, r x y → Q y → Q x) : Q a := by
  induction p
  exact hb
  next _ _ _ _ s t _ ih => exact back _ _ s (back _ _ t (ih hb))

/-! ### R4. `induction p with | nil x => ?_ | two s t q ih => ?_` · goal list, with names
`| c x y => …` names, in order, the EXPLICIT arguments of constructor `c` (`nil x`: the point;
`two s t q`: the three premises; the implicit `{a b c d}` keep `✝` names), then the IH of each premise
of the relation's own type (`q : EvenPath r c d` gets `ih`). `?_` leaves the goal open; normally a
tactic block follows `=>`, and `_` skips a name you do not need. -/
example {α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)
    (back : ∀ x y, r x y → Q y → Q x) : Q a := by
  induction p with
    | nil x => ?_
    | two s t q ih => ?_
  exact hb
  exact back _ _ s (back _ _ t (ih hb))

/-! ### R5. `ih h` · an induction hypothesis with a premise is a function
`ih : A → B` applied to `h : A` is a proof of `B`. Here `have` shows the result in the context. -/
example (A B G : Prop) (ih : A → B) (h : A) (g : B → G) : G := by
  have hb := ih h
  exact g hb

/-! ## `↔`, arithmetic, and a relation given by `fun` -/

/-! ### R6. `constructor` on `A ↔ B` · goal list: `A → B` (case `mp`) and `B → A` (case `mpr`) -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  exact f
  exact g

/-! ### R7. `omega` · closes linear arithmetic over `Nat`/`Int` from the context
A hypothesis stated as `s : (fun n m => m = n + 2) y z` is printed reduced, `s : z = y + 2` (R11),
and `omega` uses it like any equation. It handles `+`, `-`, `*` by a literal, `≤`, `<`, `=`, `≠`, `¬`,
`∧`, `∨`. -/
example (x y z : Nat) (s : (fun n m => m = n + 2) y z) (h : x ≤ y) : x ≤ z := by
  omega

/-! ### R8. `induction b` on a number, with `h : a ≤ b` in the context · `h` goes into the IH
As in R3, a hypothesis that mentions `b` is generalized: `zero` gets `h : a ≤ 0`; `succ` gets
`h : a ≤ n✝ + 1` and the IH `a✝ : a ≤ n✝ → Q n✝`, which needs `a ≤ n✝` before it gives `Q n✝`.
Name them with `induction b with | zero => … | succ n ih => …`. -/
example (Q : Nat → Prop) (a b : Nat) (h : a ≤ b) (h0 : a ≤ 0 → Q 0)
    (hs : ∀ n, (a ≤ n → Q n) → a ≤ n + 1 → Q (n + 1)) : Q b := by
  induction b
  exact h0 h
  next n ih => exact hs n ih h

/-! ### R9. `subst h` (`h : x = t`, `x` a local variable) · context: `x` and `h` disappear
Every `x` in the goal and the context is replaced by `t`. Also works for `h : t = x`. -/
example (P : Nat → Prop) (x : Nat) (h : x = 0) (h0 : P 0) : P x := by
  subst h
  exact h0

/-! ### R10. `by_cases h : A` · goal list: one goal with `h : A`, one with `h : ¬A` -/
example (A G : Prop) (f : A → G) (g : ¬A → G) : G := by
  by_cases h : A
  exact f h
  exact g h

/-! ### R11. `rfl` proves `(fun n m => m = n + 2) x (x + 2)`
A relation can be written as a function: `(fun n m => m = n + 2) x y` MEANS `y = x + 2`, by
substituting `x`, `y` into the body (β-reduction; Lean does it silently when checking a proof, and
usually prints hypotheses already reduced). Here the goal reduces to `x + 2 = x + 2`, which `rfl`
closes. So `rfl` is a proof of one step of such a relation, usable as an argument:
`.two rfl rfl (.nil (x + 4)) : EvenPath (fun n m => m = n + 2) x (x + 4)`. -/
example (x : Nat) : (fun n m => m = n + 2) x (x + 2) := by
  exact rfl

/-! ### R12. `f (by omega)` · prove a premise of `f` inline
`(by tac)` is a term: Lean elaborates `tac` against the premise's type. With `f : a ≤ n → B` this
proves `a ≤ n` from the context and yields `B`. Same idea as `rw [lemma (by norm_num)]`. -/
example (B : Prop) (a n : Nat) (h : a ≤ n + 1) (hne : ¬a = n + 1) (f : a ≤ n → B) : B := by
  exact f (by omega)

/-! # Part W · Worked combinations (on `EvenPath`, not the exercise's `Star`) -/

/-! ### W1. Composing paths: induct on the FIRST one; the second comes along (R4, R2, R5)
`q : EvenPath r b c` mentions the index `b` of `p`, so it is generalized into `ih`. -/
theorem evenPath_append {α : Type} {r : α → α → Prop} {a b c : α}
    (p : EvenPath r a b) (q : EvenPath r b c) : EvenPath r a c := by
  induction p with
    | nil _ => exact q
    | two s t _ ih => exact .two s t (ih q)

/-! ### W2. A path of `+ 1` steps only goes up: R4, then R7 in both cases -/
example (a b : Nat) (p : EvenPath (fun n m => m = n + 1) a b) : a ≤ b := by
  induction p with
    | nil _ => omega
    | two s t _ ih => omega

/-! ### W3. A concrete path `0 → 1 → 2`, as a term: R2, R11, R1 -/
example : EvenPath (fun n m => m = n + 1) 0 2 := .two rfl rfl (.nil 2)

/-! ### W4. Reusing an earlier theorem as a function (W1), one argument built by R2, R11, R1 -/
example (a : Nat) (p : EvenPath (fun n m => m = n + 1) 0 a) :
    EvenPath (fun n m => m = n + 1) 0 (a + 2) := by
  exact evenPath_append p (.two rfl rfl (.nil (a + 2)))

end M005Guide
