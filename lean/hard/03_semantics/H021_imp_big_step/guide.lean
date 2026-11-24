/- Guide for H021 (IMP big-step semantics).
Part R: one reference entry per tactic or library feature the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `H` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a toy language `Op` with a big-step relation `Run`, NOT on the exercise's `Com`
and `BigStep`; every tactic behaves the same way on both.
Part W: worked combinations on `Op` and `Run`.
Assumed: Lean basics (E001–E033).
-/

namespace H021Guide

/-! ## The toy language used by every entry

`Run p x y`: running the program `p` on the counter value `x` terminates with value `y`.
One constructor of `Run` per evaluation rule, exactly like `BigStep`. -/

inductive Op where
  | done
  | bump (n : Nat)
  | then_ (p q : Op)
  | spin (p : Op)

inductive Run : Op → Nat → Nat → Prop
  | done {x : Nat} : Run .done x x
  | bump {n x : Nat} : Run (.bump n) x (x + n)
  | then_ {p q : Op} {x y z : Nat} : Run p x y → Run q y z → Run (.then_ p q) x z
  | spin {p : Op} {x y z : Nat} : Run p x y → Run (.spin p) y z → Run (.spin p) x z

/-! # Part R · Reference entries -/

/-! ## Induction and inversion on a derivation -/

/-! ### R1. `induction h` (`h : Run p x y`) · goal list: one goal per rule, one IH per recursive premise
The goal must be about the indices `p x y` of `h`, and they must be variables. -/
example (P : Op → Nat → Nat → Prop) {p : Op} {x y : Nat} (h : Run p x y)
    (H : ∀ p x y, P p x y) : P p x y := by
  induction h
  all_goals exact H _ _ _

/-! ### R2. `induction h generalizing z` · every IH becomes `∀ {z}, …`
`h2` mentions `z`, so it is generalized too: each IH takes a fresh `Run … z` for ANY `z`. -/
example (P : Nat → Nat → Prop) {p : Op} {x y z : Nat} (h : Run p x y) (h2 : Run p x z)
    (H : ∀ a b, P a b) : P y z := by
  induction h generalizing z
  all_goals exact H _ _

/-! ### R3. `cases h` on a derivation of a fixed program (inversion) · goal list and goal
Only the rules whose conclusion can be `Run (.bump n) x y` survive (here one), and the indices are
unified: `y` is replaced by `x + n` everywhere. -/
example (P : Nat → Prop) {n x y : Nat} (h : Run (.bump n) x y) (H : P (x + n)) : P y := by
  cases h
  exact H

/-! ### R4. `cases h` on a rule with premises · context gains the premises and the middle value
`cases h with | then_ h1 h2 => …` gives the two premises the names `h1 h2`. -/
example (P : Nat → Prop) {p q : Op} {x z : Nat} (h : Run (.then_ p q) x z)
    (H : ∀ y, Run p x y → Run q y z → P z) : P z := by
  cases h
  exact H _ (by assumption) (by assumption)

/-! ### R5. `h ▸ e` (`h : a = b`, `e : P a`) · a term of type `P b`
`▸` rewrites the type of `e` with `h`, in whichever direction makes it fit the goal. -/
example (P : Nat → Prop) {a b : Nat} (h : a = b) (e : P a) : P b := by
  exact h ▸ e

/-! ### R6. `simp_all` · closes the goal when two hypotheses say `f x = true` and `f x = false` -/
example (P : Prop) (f : Nat → Bool) (x : Nat) (h1 : f x = true) (h2 : f x = false) : P := by
  simp_all

/-! ## A derivation of a fixed program: `generalize`, then induction -/

/-! ### R7. `generalize hw : e = w at h` · context: `e` in `h` becomes a new variable `w`, plus `hw : e = w`
Needed because `induction h` refuses `h : Run (.spin p) x y` ("Index in target's type is not a
variable"). -/
example (p : Op) {x y : Nat} (h : Run (.spin p) x y) (H : ∀ w, Run w x y → False) : False := by
  generalize hw : Op.spin p = w at h
  exact H w h

/-! ### R8. `induction h` with `hw : e = w` in the context · `hw` enters every case and every IH
Each IH now has the premise `e = …`; `hw` in each case says `e` equals that rule's program. -/
example (P : Prop) (p w : Op) {x y : Nat} (h : Run w x y) (hw : Op.spin p = w) (H : P) : P := by
  induction h
  all_goals exact H

/-! ### R9. `injection hw with h1 h2` · context: equal constructors → equal arguments (E029) -/
example (P : Prop) (p q p' q' : Op) (hw : Op.then_ p q = Op.then_ p' q') (H : p = p' → q = q' → P) :
    P := by
  injection hw with h1 h2
  exact H h1 h2

/-! ### R10. `subst h1` (`h1 : a = b`, `b` a variable) · context: `b` replaced by `a` everywhere, `b` gone -/
example (P : Op → Prop) (a b : Op) (h1 : a = b) (hb : P b) : P a := by
  subst h1
  exact hb

/-! ### R11. `simp [f] at hb` · `hb` simplifies to `False`, which closes the goal -/
def isDone : Op → Bool
  | .done => true
  | _ => false

example (P : Prop) (hb : isDone Op.done = false) : P := by
  simp [isDone] at hb

/-! ### R12. `cases hw` with `hw` an equation between different constructors · closes the goal -/
example (P : Prop) (p : Op) (n : Nat) (hw : Op.spin p = Op.bump n) : P := by
  cases hw

/-! ## A derivation of a named program -/

/-! ### R13. `cases h` with `h : Run d x y` for a defined name `d` · `cases` unfolds `d` itself -/
def twoBumps : Op := .then_ (.bump 1) (.bump 1)

example (P : Nat → Prop) {x y : Nat} (h : Run twoBumps x y)
    (H : ∀ m, Run (.bump 1) x m → Run (.bump 1) m y → P y) : P y := by
  cases h
  exact H _ (by assumption) (by assumption)

/-! ### R14. `simp` on `(fun y => if y = k then v else f y) n` with numerals `k n` · goal
`simp` β-reduces the application and decides `n = k`. `simp [d]` first unfolds a definition `d`
whose body is such a `fun`. -/
example (P : Int → Prop) (f : Nat → Int) (v : Int) (H : P (f 1)) :
    P ((fun y => if y = 0 then v else f y) 1) := by
  simp
  exact H

/-! # Part W · Worked combinations (on `Op` and `Run`, not the exercise's objects) -/

/-! ### W1. Rule induction with named IHs: running never decreases the counter (R1) -/
example {p : Op} {x y : Nat} (h : Run p x y) : x ≤ y := by
  induction h with
    | done => exact Nat.le_refl _
    | bump => omega
    | then_ _ _ ih1 ih2 => omega
    | spin _ _ ih1 ih2 => omega

/-! ### W2. Two runs of `.then_` from the same start meet in the middle (R4, R5)
`hp` and `hq` play the role that generalized IHs (R2) play inside an induction:
`hp a1 b1 : m = m'` identifies the two middle values, then `▸` moves `b2` to the right start. -/
example {p q : Op} {x y z : Nat} (h1 : Run (.then_ p q) x y) (h2 : Run (.then_ p q) x z)
    (hp : ∀ {a b c}, Run p a b → Run p a c → b = c)
    (hq : ∀ {a b c}, Run q a b → Run q a c → b = c) : y = z := by
  cases h1 with
    | then_ a1 a2 =>
      cases h2 with
      | then_ b1 b2 => exact hq a2 (hp a1 b1 ▸ b2)

/-! ### W3. `.spin p` never stops (R7, R8, R12) -/
example (p : Op) {x y : Nat} (h : Run (.spin p) x y) : False := by
  generalize hw : Op.spin p = w at h
  induction h with
    | spin _ _ _ ih2 => exact ih2 hw
    | _ => cases hw

/-! ### W4. Computing a named program's result by inversion (R13, R3) -/
example {x y : Nat} (h : Run twoBumps x y) : y = x + 2 := by
  cases h with
    | then_ h1 h2 =>
      cases h1
      cases h2
      rfl

end H021Guide
