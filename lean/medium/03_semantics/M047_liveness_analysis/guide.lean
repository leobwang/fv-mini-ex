/- Guide for M047 (Liveness analysis for straight-line code).
Part R: one reference entry per tactic or lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries run on toy objects (NOT the exercise's): environments `Env := Nat → Int`, toy
expressions `Tm` = `lit n | var x | neg t | add t u` with value `ev` and variable list `vars`, a
point update `set`, and toy programs `List (Nat × Int)` of constant assignments run by `runAll`.
Part W: worked combinations on the toy objects.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M047Guide

/-! ## The toy objects (not the exercise's) -/

/-- An environment: variable `x` has value `s x`. -/
abbrev Env := Nat → Int

/-- Toy expressions. -/
inductive Tm where
  | lit (n : Int)
  | var (x : Nat)
  | neg (t : Tm)
  | add (t u : Tm)

/-- The value of a toy expression in environment `s`. -/
def ev (s : Env) : Tm → Int
  | .lit n => n
  | .var x => s x
  | .neg t => -ev s t
  | .add t u => ev s t + ev s u

/-- The variables of a toy expression. -/
def vars : Tm → List Nat
  | .lit _ => []
  | .var x => [x]
  | .neg t => vars t
  | .add t u => vars t ++ vars u

/-- Point update: `set s x v` is `s` with `x` now holding `v`. -/
def set (s : Env) (x : Nat) (v : Int) : Env := fun z => if z = x then v else s z

/-- Toy programs: constant assignments `x := v`, run front to back. -/
def runAll : List (Nat × Int) → Env → Env
  | [], s => s
  | (x, v) :: q, s => runAll q (set s x v)

/-! # Part R · Reference entries -/

/-! ## Milestone: an expression only reads its own variables -/

/-! ### R1. `induction t` on an expression type · goal list: one goal per constructor, an IH for
every argument of type `Tm`. Write `induction t with | lit n => … | var x => … | neg t ih => …
| add t u iht ihu => …` to name the arguments and IHs yourself (W1). In the example, `‹_›` means
"the hypothesis in the context whose type is the one expected here" (the unnamed IH). -/
example (P : Tm → Prop) (hl : ∀ n, P (.lit n)) (hv : ∀ x, P (.var x))
    (hn : ∀ t, P t → P (.neg t)) (ha : ∀ t u, P t → P u → P (.add t u)) (t : Tm) : P t := by
  induction t
  · exact hl _
  · exact hv _
  · exact hn _ ‹_›
  · exact ha _ _ ‹_› ‹_›

/-! ### R2. `rfl` up to unfolding · closes an equation whose two sides compute to the same term
`ev s1 (.lit n)` and `ev s2 (.lit n)` both unfold to `n`: no `simp` needed. -/
example (s1 s2 : Env) (n : Int) : ev s1 (.lit n) = ev s2 (.lit n) := by
  rfl

/-! ### R3. `simp [vars]` (uses `List.mem_singleton : a ∈ [b] ↔ a = b`) · closes `x ∈ vars (.var x)` -/
example (x : Nat) : x ∈ vars (.var x) := by
  simp [vars]

/-! ### R4. `simp only [ev]` on a constructor · goal: `ev s (c …)` → the right side of `ev`'s equation -/
example (s : Env) (t u : Tm) (P : Int → Prop) (h : P (ev s t + ev s u)) : P (ev s (.add t u)) := by
  simp only [ev]
  exact h

/-! ### R5. `List.mem_append` · `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` · goal: membership in `++` → `∨` -/
example (y : Nat) (l₁ l₂ : List Nat) (h : y ∈ l₁ ∨ y ∈ l₂) : y ∈ l₁ ++ l₂ := by
  rw [List.mem_append]
  exact h

/-! ### R6. `exact fun y hy => h y (by simp [hy])` · closes `∀ y ∈ l₁, Q y` from `∀ y ∈ l₁ ++ l₂, Q y`
A bounded `∀` is a function: take `y` and `hy : y ∈ l₁`, feed `h` a proof of `y ∈ l₁ ++ l₂`
(here `simp [hy]`, which uses R5). -/
example (Q : Nat → Prop) (l₁ l₂ : List Nat) (h : ∀ y ∈ l₁ ++ l₂, Q y) : ∀ y ∈ l₁, Q y := by
  exact fun y hy => h y (by simp [hy])

/-! ### R7. `rw [ih hq]` with an IH that has a premise · goal: `f s1` → `f s2`
`ih : Q → f s1 = f s2` is not an equation yet; `ih hq` is. Build `hq` in place with R6. -/
example {σ β : Type} (f : σ → β) (s1 s2 : σ) (Q : Prop) (ih : Q → f s1 = f s2) (hq : Q)
    (P : β → Prop) (h : P (f s2)) : P (f s1) := by
  rw [ih hq]
  exact h

/-! ## The main induction: over the program, backwards -/

/-! ### R8. `induction l generalizing b` · goal list; the IH is `∀ b, …`, so it can be used at ANY `b`
Without `generalizing`, the IH is about the original `b` only. In the cons goal the names are
inaccessible (`head✝ tail✝ tail_ih✝`); write `induction l generalizing b with | nil => … |
cons hd tl ih => …` to name them. Several variables: `generalizing s1 s2`. -/
example {α β : Type} (P : List α → β → Prop) (hnil : ∀ b, P [] b)
    (hcons : ∀ x l, (∀ b, P l b) → ∀ b, P (x :: l) b) (l : List α) (b : β) : P l b := by
  induction l generalizing b
  · exact hnil b
  · exact hcons _ _ ‹_› b

/-! ### R9. `exact h` up to unfolding · closes `P (runAll [] s)` with `h : P s`
`runAll [] s` computes to `s`, so `h` already has the goal's type. -/
example (s : Env) (P : Env → Prop) (h : P s) : P (runAll [] s) := by
  exact h

/-! ### R10. `obtain ⟨x, a⟩ := xa` · context: a pair `xa : α × β` → its components `x a` -/
example {α β : Type} (P : α × β → Prop) (h : ∀ x a, P (x, a)) (xa : α × β) : P xa := by
  obtain ⟨x, a⟩ := xa
  exact h x a

/-! ### R11. `apply ih` up to unfolding · goal: `ih`'s conclusion → `ih`'s premise
`runAll ((x, v) :: q) s` computes to `runAll q (set s x v)`, which matches the conclusion of `ih` with
its `∀ s` instantiated to `set s x v` (that is why R8 needs `generalizing`). -/
example (q : List (Nat × Int)) (x : Nat) (v : Int) (s : Env) (P Q : Env → Prop)
    (ih : ∀ s, Q s → P (runAll q s)) (h : Q (set s x v)) : P (runAll ((x, v) :: q) s) := by
  apply ih
  exact h

/-! ### R12. `intro y hy` on a bounded `∀` · context gains `y` and `hy : y ∈ l` -/
example (Q : Nat → Prop) (l : List Nat) (h : ∀ y, Q y) : ∀ y ∈ l, Q y := by
  intro y hy
  exact h y

/-! ### R13. `by_cases hyx : y = x` · goal list: one goal with `hyx : y = x`, one with `hyx : ¬y = x` -/
example (P : Nat → Nat → Prop) (heq : ∀ y, P y y) (hne : ∀ x y, ¬y = x → P x y) (x y : Nat) :
    P x y := by
  by_cases hyx : y = x
  · rw [hyx]
    exact heq x
  · exact hne x y hyx

/-! ### R14. `subst hyx` · context: `hyx : y = x` is used up and `x` is replaced by `y` everywhere -/
example (P : Nat → Nat → Prop) (h : ∀ y, P y y) (x y : Nat) (hyx : y = x) : P x y := by
  subst hyx
  exact h y

/-! ### R15. `simp only [set, if_pos]` (`if_pos : c → (if c then t else e) = t`) · goal:
`set s y v y` → `v`. `set` unfolds to `if y = y then v else s y`, `simp only` turns `y = y` into
`True` by itself, and `if_pos` (its premise `True` is proved by `simp`) keeps the `then` branch.
`simp only [set]` alone stops at `if True then v else s y`. -/
example (s : Env) (y : Nat) (v : Int) (P : Int → Prop) (h : P v) : P (set s y v y) := by
  simp only [set, if_pos]
  exact h

/-! ### R16. `simp only [set, if_neg hyx]` (`if_neg : ¬c → (if c then t else e) = e`) · goal:
`set s x v y` → `s y` when `hyx : ¬y = x` -/
example (s : Env) (x y : Nat) (v : Int) (hyx : ¬y = x) (P : Int → Prop) (h : P (s y)) :
    P (set s x v y) := by
  simp only [set, if_neg hyx]
  exact h

/-! ### R17. `List.mem_filter` · `a ∈ l.filter p ↔ a ∈ l ∧ p a = true` · goal: filter membership → `∧`
`l.filter (· ≠ x)` prints as `List.filter (fun x_1 => decide (x_1 ≠ x)) l`: `filter` needs a `Bool`
test, and `decide (c)` is the `Bool` of a decidable `Prop` `c`. `simp` turns `decide c = true` back
into `c` (lemma `decide_eq_true_eq`). -/
example (x y : Nat) (l : List Nat) (h : y ∈ l ∧ decide (y ≠ x) = true) :
    y ∈ l.filter (· ≠ x) := by
  rw [List.mem_filter]
  exact h

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. Expressions read only their variables: R1 with named alternatives, R2, R3, R4, R7 with R6 -/
theorem ev_agree (t : Tm) (s1 s2 : Env) (h : ∀ y ∈ vars t, s1 y = s2 y) : ev s1 t = ev s2 t := by
  induction t with
    | lit n => rfl
    | var x => exact h x (by simp [vars])
    | neg t ih =>
      simp only [ev]
      rw [ih h]
    | add t u iht ihu =>
      simp only [ev]
      rw [iht fun y hy => h y (by simp [vars, hy]), ihu fun y hy => h y (by simp [vars, hy])]

/-! ### W2. Two updates of `x` by the same value agree wherever the old states agree off `x`:
R12, R13, then R14 + R15 on one side and R16 on the other -/
example (s1 s2 : Env) (x : Nat) (v : Int) (h : ∀ y, y ≠ x → s1 y = s2 y) :
    ∀ y ∈ [x, x + 1], set s1 x v y = set s2 x v y := by
  intro y _
  by_cases hyx : y = x
  · subst hyx
    simp only [set, if_pos]
  · simp only [set, if_neg hyx]
    exact h y hyx

/-! ### W3. Membership in `filter … ++ …` in one `simp`: R5 and R17, with the facts that decide it -/
example (x y : Nat) (l m : List Nat) (hy : y ∈ l) (hyx : ¬y = x) :
    y ∈ l.filter (· ≠ x) ++ m := by
  simp [List.mem_filter, hy, hyx]

/-! ### W4. Induction over a program with the state generalized: R8 with named alternatives, R10, R7
`runAll` never changes a variable that no assignment writes. -/
example (q : List (Nat × Int)) (z : Nat) (hz : ∀ xv ∈ q, xv.1 ≠ z) (s : Env) :
    runAll q s z = s z := by
  induction q generalizing s with
    | nil => rfl
    | cons xv q ih =>
      obtain ⟨x, v⟩ := xv
      have hzx : ¬z = x := fun e => hz (x, v) (by simp) e.symm
      show runAll q (set s x v) z = s z
      rw [ih (fun xv hxv => hz xv (by simp [hxv]))]
      simp only [set, if_neg hzx]

end M047Guide
