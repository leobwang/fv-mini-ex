/- Guide for M045 (Hoare rules are sound).
Part R: one reference entry per tactic or term form the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries run on a toy language `Op` with a big-step relation `Run`, NOT the exercise's IMP:
`Run o n k` means "running `o` from the number `n` can end at `k`".
Part W: worked combinations on the toy language.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M045Guide

/-! ## The toy objects (not the exercise's) -/

/-- Toy programs over one natural-number register. `rep o` runs `o` zero or more times. -/
inductive Op where
  | inc
  | dbl
  | both (o1 o2 : Op)
  | rep (o : Op)

/-- `Run o n k`: running `o` from `n` can end at `k` (an inductive relation, one rule per line). -/
inductive Run : Op → Nat → Nat → Prop
  | inc {n : Nat} : Run .inc n (n + 1)
  | dbl {n : Nat} : Run .dbl n (2 * n)
  | both {o1 o2 : Op} {n m k : Nat} : Run o1 n m → Run o2 m k → Run (.both o1 o2) n k
  | stop {o : Op} {n : Nat} : Run (.rep o) n n
  | more {o : Op} {n m k : Nat} : Run o n m → Run (.rep o) m k → Run (.rep o) n k

/-- A definition whose body is a `∀ … → …` statement, like `Hoare`. -/
def Keeps {α : Type} (r : α → α → Prop) (P : α → Prop) : Prop := ∀ x y, P x → r x y → P y

/-- A function defined by pattern matching, like `aeval`. -/
inductive Tm where
  | lit (n : Int)
  | neg (t : Tm)
  | add (t u : Tm)

def ev : Tm → Int
  | .lit n => n
  | .neg t => -ev t
  | .add t u => ev t + ev u

/-! # Part R · Reference entries -/

/-! ## Opening a definition and inverting a derivation -/

/-! ### R1. `intro x y hx hr` through a definition · goal `Keeps r P` → context gains `x y hx hr`
`intro` unfolds the definition by itself when its body is a `∀` or `→`. -/
example {α : Type} (r : α → α → Prop) (P : α → Prop) (h : ∀ x y, P x → r x y → P y) :
    Keeps r P := by
  intro x y hx hr
  exact h x y hx hr

/-! ### R2. `cases h` on a derivation of a fixed constructor · context loses `h`; goal: the end
state replaced by what the only matching rule produces -/
example (n m : Nat) (P : Nat → Prop) (hp : P (n + 1)) (h : Run .inc n m) : P m := by
  cases h
  exact hp

/-! ### R3. `cases h with | both h1 h2 => tac` · context: `h` → its premises, named `h1 h2`
The middle state is not named in the pattern, so it prints as `m✝`. Alternatives are indented
under `cases`. -/
example (o1 o2 : Op) (n k : Nat) (P : Nat → Prop) (h : Run (.both o1 o2) n k)
    (hp : ∀ m, Run o1 n m → Run o2 m k → P k) : P k := by
  cases h with
    | both h1 h2 => exact hp _ h1 h2

/-! The same state as inside the alternative of R3, reached at top level: plain `cases h` names the
premises `a✝¹ a✝`, and `rename_i h1 h2` names the last two inaccessible hypotheses. -/
example (o1 o2 : Op) (n k : Nat) (P : Nat → Prop) (h : Run (.both o1 o2) n k)
    (hp : ∀ m, Run o1 n m → Run o2 m k → P k) : P k := by
  cases h
  rename_i h1 h2
  exact hp _ h1 h2

/-! ### R4. `h _ _ hx hr` · a hypothesis `h : ∀ x y, P x → r x y → Q y` is a function
Apply it to arguments; `_` lets Lean infer `x` and `y` from the types of `hx` and `hr`. -/
example {α : Type} (r : α → α → Prop) (P Q : α → Prop) (x y : α)
    (h : ∀ x y, P x → r x y → Q y) (hx : P x) (hr : r x y) : Q y := by
  exact h _ _ hx hr

/-! ### R5. `fun x y hx hr => e` · a term proof of a `∀ … → …` definition (the term form of R1)
The proof is the function itself; after `:=` you may drop `by exact` (here it only shows the goal). -/
example {α : Type} (r : α → α → Prop) (P : α → Prop) (h : ∀ x y, r x y → P y) :
    Keeps r P := by
  exact fun x y _ hr => h x y hr

/-! ## Induction on a derivation whose command is not a variable -/

/-! ### R6. `generalize hw : e = w at h` · context: `e` in `h` → a new variable `w`, plus `hw : e = w` -/
example (o : Op) (n k : Nat) (P : Nat → Prop) (h : Run (.rep o) n k)
    (hp : ∀ w, Op.rep o = w → Run w n k → P k) : P k := by
  generalize hw : Op.rep o = w at h
  exact hp w hw h

/-! ### R7. `induction h` on a derivation · goal list: one goal per rule of `Run`, with an
induction hypothesis `a_ih✝` for each premise that is itself a `Run`.
`induction h with | more h1 h2 ih1 ih2 => tac | …` names them instead. -/
example (o : Op) (n k : Nat) (h : Run o n k) : n ≤ k := by
  induction h
  all_goals omega

/-! ### R8. `cases hw` on `hw : c a = c b` (same constructor `c`) · context: `b` replaced by `a`,
`hw` gone -/
example (o o' : Op) (P : Op → Prop) (hp : P o) (hw : Op.rep o = Op.rep o') : P o' := by
  cases hw
  exact hp

/-! ### R9. `cases hw` on `hw : c₁ … = c₂ …` (different constructors) · closes the goal
Constructors of an inductive type are distinct, so there is no case left. -/
example (o : Op) (G : Prop) (hw : Op.rep o = Op.inc) : G := by
  cases hw

/-! ### R10. `exact ⟨ha, hb⟩` · closes `A ∧ B` from proofs of both sides -/
example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  exact ⟨ha, hb⟩

/-! ### R11. `ih ha rfl` · an induction hypothesis whose premise is an equation `e = e`
After `generalize` (R6) every IH carries the equation as a premise; `rfl` proves it. -/
example {α : Type} (e : α) (A B : Prop) (ih : A → e = e → B) (ha : A) : B := by
  exact ih ha rfl

/-! ## Chaining rules and side conditions -/

/-! ### R12. `refine f (g ?_) ?_` · goal list: one goal per `?_`, in order, wherever it sits -/
example (A B C D : Prop) (f : B → C → D) (g : A → B) (ha : A) (hc : C) : D := by
  refine f (g ?_) ?_
  exact ha
  exact hc

/-! ### R13. `(m := e)` · set an implicit argument by name
`Nat.le_trans : n ≤ m → m ≤ k → n ≤ k` has `{n m k : Nat}`; the goal fixes `n` and `k`, never `m`. -/
example (n m k : Nat) (h1 : n ≤ m) (h2 : m ≤ k) : n ≤ k := by
  refine Nat.le_trans (m := m) ?_ ?_
  exact h1
  exact h2

/-! ### R14. `fun _ h => h` · proves `∀ x, P x → P x` (a side condition that is trivial) -/
example {α : Type} (P : α → Prop) : ∀ x, P x → P x := by
  exact fun _ h => h

/-! ### R15. `simp [f] at h` · unfolds a pattern-matching function `f` one constructor at a time
In the exercise `simp [beval, aeval, update] at *` does this in every hypothesis and the goal. -/
example (a b : Int) (h : ev (.add (.lit a) (.neg (.lit b))) = 0) : a = b := by
  simp [ev] at h
  omega

/-! ### R16. `simp at h` on a `Bool` test · `(!decide (a ≤ b)) = true` → `b < a`
`decide p : Bool` is the truth value of the proposition `p`; `!` is Boolean negation. -/
example (a b : Int) (P : Prop) (hp : b < a → P) (h : (!decide (a ≤ b)) = true) : P := by
  simp at h
  exact hp h

/-! ### R17. `simp at h` on a false `Bool` test · `(!decide (a ≤ b)) = false` → `a ≤ b` -/
example (a b : Int) (P : Prop) (hp : a ≤ b → P) (h : (!decide (a ≤ b)) = false) : P := by
  simp at h
  exact hp h

/-! ### R18. `simp` on a point update · `(fun j => if j = i then v else f j) i` → `v` -/
example (f : Nat → Int) (v : Int) (P : Int → Prop) (h : P v) :
    P ((fun j => if j = 3 then v else f j) 3) := by
  simp
  exact h

/-! ### R19. `omega` · closes linear arithmetic over `Int`/`Nat`, using the hypotheses
`+`, `-`, `≤`, `<`, `=`, `∧`, `¬` and multiplication by numerals; not `x * y`. -/
example (x y : Int) (h : x ≤ y ∧ y < x + 2) : y = x ∨ y = x + 1 := by
  omega

/-! # Part W · Worked combinations (toy language, not the exercise's) -/

/-! ### W1. `generalize` + `induction` + `cases hw`: from 0, doubling any number of times stays 0
R6, R7 with named alternatives, R9 for the rules whose command is not `rep`, R8, then R11.
`h0 : n = 0` mentions the start state, so `induction` carries it along: every IH gets a premise
`m = 0` for its own start state `m`, before the equation from `hw`. -/
example (n k : Nat) (h : Run (.rep .dbl) n k) (h0 : n = 0) : k = 0 := by
  generalize hw : Op.rep Op.dbl = w at h
  induction h with
    | stop => exact h0
    | more h1 _ _ ih2 =>
      cases hw
      cases h1
      exact ih2 (by omega) rfl
    | _ => cases hw

/-! ### W2. The same induction, states shown at top level: plain `induction h`, then one goal at a time -/
example (n k : Nat) (h : Run (.rep .dbl) n k) (h0 : n = 0) : k = 0 := by
  generalize hw : Op.rep Op.dbl = w at h
  induction h
  all_goals try (cases hw; done)
  · exact h0
  rename_i h1 _ _ ih2
  cases hw
  cases h1
  exact ih2 (by omega) rfl

/-! ### W3. `refine` with a named argument, then `simp … at *` and `omega` on each side goal -/
example (a b : Int) (h : ev (.add (.lit a) (.lit 1)) ≤ b) : a ≤ b := by
  refine Int.le_trans (b := a + 1) ?_ ?_
  · omega
  · simp [ev] at *
    exact h

end M045Guide
