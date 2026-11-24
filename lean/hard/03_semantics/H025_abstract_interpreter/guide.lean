/- Guide for H025 (An abstract interpreter for IMP).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (traffic lights, a toy loop
language `Prog` with its run relation `Run`).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace H025Guide

/-! ## Objects used by the entries (not the exercise's) -/

/-- A three-valued enumeration. -/
inductive Light where
  | red
  | amber
  | green
  deriving DecidableEq

/-- Which integers each light "allows". -/
def Light.code : Light → Int → Prop
  | .red, v => v < 0
  | .amber, v => v = 0
  | .green, v => 0 < v

/-- A function defined by a nested `if`. -/
def Light.byAge (n : Nat) : Light := if n = 0 then .red else if n < 10 then .amber else .green

/-- Binary trees: an inductive type with two constructors. -/
inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)

/-- Read position `n` of a list, with default `d` past the end. -/
def pick {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: as, n + 1 => pick d as n

/-- A definition that wraps a `∀`. -/
def Every {α : Type} (Q : α → Prop) : Prop := ∀ x, Q x

/-- Fuelled descent: apply `g` while the value strictly decreases. -/
def descend (g : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x =>
    let y := g x
    if y < x then descend g k y else x

/-- A toy loop language and its big-step run relation `Run p n m` (start counter `n`, end `m`). -/
inductive Prog where
  | halt
  | tick (p : Prog)
  | rep (p : Prog)

inductive Run : Prog → Nat → Nat → Prop
  | halt {n : Nat} : Run .halt n n
  | tick {p : Prog} {n m : Nat} : Run p (n + 1) m → Run (.tick p) n m
  | repDone {p : Prog} {n : Nat} : Run (.rep p) n n
  | repMore {p : Prog} {n m k : Nat} : Run p n m → Run (.rep p) m k → Run (.rep p) n k

/-! # Part R · Reference entries -/

/-! ## Case analysis on finite data and sign arithmetic -/

/-! ### R1. `cases a` on an enumeration · goal list: one goal per constructor -/
example (P : Light → Prop) (hr : P .red) (ha : P .amber) (hg : P .green) (a : Light) : P a := by
  cases a
  · exact hr
  · exact ha
  · exact hg

/-! ### R2. `simp_all [d]` · context and goal: unfold `d` everywhere, simplify hypotheses with each other -/
example (x y : Int) (hx : Light.code .green x) (hy : Light.code .green y) :
    Light.code .green (x + y) := by
  simp_all [Light.code]
  omega

/-! ### R3. `omega` · closes linear arithmetic over `Int` and `Nat` (uses the hypotheses) -/
example (x y : Int) (hx : 0 < x) (hy : y < 0) : 0 < x - y := by
  omega

/-! ### R4. `Int.mul_pos` · `0 < a → 0 < b → 0 < a * b` (closes; `omega` cannot multiply variables) -/
example (a b : Int) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact Int.mul_pos ha hb

/-! ### R5. `Int.mul_pos_of_neg_of_neg` · `a < 0 → b < 0 → 0 < a * b` -/
example (a b : Int) (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  exact Int.mul_pos_of_neg_of_neg ha hb

/-! ### R6. `Int.mul_neg_of_pos_of_neg` · `0 < a → b < 0 → a * b < 0` -/
example (a b : Int) (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  exact Int.mul_neg_of_pos_of_neg ha hb

/-! ### R7. `Int.mul_neg_of_neg_of_pos` · `a < 0 → 0 < b → a * b < 0` -/
example (a b : Int) (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  exact Int.mul_neg_of_neg_of_pos ha hb

/-! ## Definitions with `if` -/

/-! ### R8. `unfold f` · goal: the name `f` → its body -/
example (P : Light → Prop) (n : Nat)
    (h : P (if n = 0 then .red else if n < 10 then .amber else .green)) : P (Light.byAge n) := by
  unfold Light.byAge
  exact h

/-! ### R9. `split` · goal list: an `if c then a else b` in the goal → a goal with `c`, a goal with `¬c` -/
example {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : c → P a)
    (hb : ¬c → P b) : P (if c then a else b) := by
  split
  next h => exact ha h
  next h => exact hb h

/-! ### R10. `next h => tac` · context: names the inaccessible `h✝` of the first goal, then runs `tac` -/
example (c : Prop) (G : Prop) (k : c → G) (k' : ¬c → G) (hc : c ∨ ¬c) : G := by
  cases hc
  next h => exact k h
  next h => exact k' h

/-! ## Induction and case splits on data -/

/-! ### R11. `induction t` on an inductive type · goal list: one goal per constructor, with an IH
per recursive argument. `induction t with | leaf n => … | node l r ihl ihr => …` names them. -/
example (P : Tree → Prop) (hl : ∀ n, P (.leaf n)) (hn : ∀ l r, P l → P r → P (.node l r))
    (t : Tree) : P t := by
  induction t
  next n => exact hl n
  next l r ihl ihr => exact hn l r ihl ihr

/-! ### R12. `induction l generalizing x` · goal list: the IH holds for every `x`, not just the current one -/
example {α : Type} (P : List α → Nat → Prop) (hnil : ∀ x, P [] x)
    (hcons : ∀ a as, (∀ x, P as x) → ∀ x, P (a :: as) x) (l : List α) (x : Nat) : P l x := by
  induction l generalizing x
  next => exact hnil x
  next a as ih => exact hcons a as ih x

/-! ### R13. `cases q` on a list · goal list: `q = []` and `q = head :: tail` -/
example {α : Type} (P : List α → Prop) (h0 : P []) (h1 : ∀ b bs, P (b :: bs)) (q : List α) : P q := by
  cases q
  next => exact h0
  next b bs => exact h1 b bs

/-! ### R14. `cases n` on a natural number · goal list: `n = 0` and `n = m + 1` -/
example (P : Nat → Prop) (h0 : P 0) (h1 : ∀ m, P (m + 1)) (n : Nat) : P n := by
  cases n
  next => exact h0
  next m => exact h1 m

/-! ### R15. `simp only [f]` · goal: `f` applied to constructors is computed by its equations -/
example {α : Type} (d a : α) (as : List α) (n : Nat) (P : α → Prop) (h : P d ∧ P (pick d as n)) :
    P (pick d [] n) ∧ P (pick d (a :: as) (n + 1)) := by
  simp only [pick]
  exact h

/-! ## Unfolding, instantiating, simplifying -/

/-! ### R16. `intro y` on a definition that is a `∀` · context gains `y` (Lean unfolds the definition) -/
example {α : Type} (Q : α → Prop) (h : ∀ x, Q x) : Every Q := by
  intro y
  exact h y

/-! ### R17. `have := ih t ht` · context gains `this`: the IH at a new argument, here a shifted function -/
example {α : Type} (Q : Nat → α → Prop) (P : (Nat → α) → Prop) (s : Nat → α) (h : ∀ x, Q x (s x))
    (ih : ∀ t : Nat → α, (∀ x, Q (x + 1) (t x)) → P t) : P (fun k => s (k + 1)) := by
  have := ih (fun k => s (k + 1)) (fun k => h (k + 1))
  exact this

/-! ### R18. `simpa using h` · closes: simplifies `h` and the goal, then matches them.
`simp` knows `m + 1 = n + 1 ↔ m = n`. -/
example {α : Type} (v : α) (f : Nat → α) (m n : Nat) (P : α → Prop)
    (h : P (if m = n then v else f (m + 1))) : P (if m + 1 = n + 1 then v else f (m + 1)) := by
  simpa using h

/-! ### R19. `simp only [f]` on a `let` · goal: one equation of `f`, with the `let` substituted -/
example (g : Nat → Nat) (k x : Nat) (P : Nat → Prop)
    (h : P (if g x < x then descend g k (g x) else x)) : P (descend g (k + 1) x) := by
  simp only [descend]
  exact h

/-! ### R20. `refine ⟨h, fun y => ?_⟩` · goal: one part given, a hole under a binder → context gains `y` -/
example {α : Type} (A : Prop) (Q : α → Prop) (ha : A) (hq : ∀ x, Q x) : A ∧ ∀ x, Q x := by
  refine ⟨ha, fun y => ?_⟩
  exact hq y

/-! ## Induction on a derivation (an inductive `Prop`) -/

/-! ### R21. `generalize hw : e = w at h` · context: `e` in `h` replaced by a variable `w`, plus `hw : e = w` -/
example (p : Prog) (n m : Nat) (Q : Prop) (h : Run (.rep p) n m)
    (k : ∀ w, Prog.rep p = w → Run w n m → Q) : Q := by
  generalize hw : Prog.rep p = w at h
  exact k w hw h

/-! ### R22. `induction h` on a derivation · goal list: one goal per rule, an IH per premise -/
example (p : Prog) (n m : Nat) (h : Run p n m) : n ≤ m := by
  induction h
  all_goals omega

/-! ### R23. `cases hw` with `hw : C₁ … = C₂ …` (different constructors) · closes the goal -/
example (p : Prog) (Q : Prop) (hw : Prog.rep p = Prog.halt) : Q := by
  cases hw

/-! ### R24. `cases hw` with `hw : C a = C b` (same constructor) · context: `b` replaced by `a` -/
example (p q : Prog) (P : Prog → Prop) (h : P p) (hw : Prog.rep p = Prog.rep q) : P q := by
  cases hw
  exact h

/-! ### R25. `cases h` on a derivation (inversion) · goal list: one goal per rule that can conclude `h` -/
example (p : Prog) (n m : Nat) (P : Nat → Nat → Prop) (h : Run (.rep p) n m) (h0 : ∀ n, P n n)
    (h1 : ∀ n k m, Run p n k → Run (.rep p) k m → P n m) : P n m := by
  cases h
  next => exact h0 n
  next k h₁ h₂ => exact h1 n k m h₁ h₂

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Case bash on two enumerations: R1, R2, R3 -/
example (a b : Light) (x y : Int) (ha : a.code x) (hb : b.code y) (hab : a = b) :
    a.code (x + y) := by
  cases a <;> cases b <;> simp_all [Light.code] <;> omega

/-! ### W2. Structural recursion on two lists at once: R12, R13, R14, R15 -/
def zipMin : List Nat → List Nat → List Nat
  | a :: as, b :: bs => min a b :: zipMin as bs
  | _, _ => []

example (p q : List Nat) (x : Nat) : pick 0 (zipMin p q) x ≤ pick 0 p x := by
  induction p generalizing q x with
    | nil => simp [zipMin, pick]
    | cons a as ih =>
      cases q with
      | nil => simp [zipMin, pick]
      | cons b bs =>
        cases x with
        | zero => simp only [zipMin, pick]; omega
        | succ n => exact ih bs n

/-! ### W3. An invariant of every run of `rep p`: R21, R22, R23, R24 -/
example (p : Prog) (Q : Nat → Prop) (hp : ∀ n m, Run p n m → Q n → Q m) {n m : Nat}
    (h : Run (.rep p) n m) (hn : Q n) : Q m := by
  generalize hw : Prog.rep p = w at h
  induction h with
    | repDone => exact hn
    | repMore h1 _ _ ih2 =>
      cases hw
      exact ih2 (hp _ _ h1 hn) rfl
    | _ => cases hw

end H025Guide
