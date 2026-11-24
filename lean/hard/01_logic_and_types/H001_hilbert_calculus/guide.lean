/- Guide for H001 (Hilbert calculus: deduction theorem and soundness).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a reachability system `Reach`,
Boolean expressions `BExp`).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace H001Guide

/-! ## Objects the entries use (unrelated to the exercise) -/

/-- A toy derivation system: `Reach E x y` says `y` is reachable from `x` along the edge list `E`.
In `trans` the middle point `y` occurs in the premises but not in the conclusion `Reach E x z`. -/
inductive Reach : List (Nat × Nat) → Nat → Nat → Prop
  | edge {E : List (Nat × Nat)} {x y : Nat} : (x, y) ∈ E → Reach E x y
  | refl {E : List (Nat × Nat)} {x : Nat} : Reach E x x
  | trans {E : List (Nat × Nat)} {x y z : Nat} : Reach E x y → Reach E y z → Reach E x z

/-- Boolean expressions over variables `var n`. -/
inductive BExp where
  | var (n : Nat)
  | tt
  | neg (a : BExp)
  | and (a b : BExp)

/-- Boolean semantics by pattern matching: `v` gives each variable a truth value. -/
def beval (v : Nat → Bool) : BExp → Bool
  | .var n => v n
  | .tt => true
  | .neg a => !beval v a
  | .and a b => beval v a && beval v b

/-! # Part R · Reference entries -/

/-! ## Building a derivation from constructors -/

/-! ### R1. `exact .c h₁ h₂` (leading-dot constructor) · goal closed
`.trans` means `Reach.trans`: Lean reads the constructor's name off the expected type. Its implicit
arguments `{E x y z}` are found by unification; a nullary `.refl` fills itself in the same way. -/
example {E : List (Nat × Nat)} {x y : Nat} (h : Reach E x y) : Reach E x y := by
  exact .trans .refl h

/-! ## Boolean semantics -/

/-! ### R2. `cases h : e` · goal list: one goal per value of the `Bool` term `e`; context gains `h`
Every `e` in the goal becomes `false` (first goal) or `true` (second); `h : e = false` / `h : e = true`
records which. Plain `cases e` does the same but forgets `h`. -/
example (f : Nat → Bool) (x : Nat) (P : Bool → Prop) (h0 : P false) (h1 : P true) : P (f x) := by
  cases h : f x
  exact h0
  exact h1

/-! ### R3. `simp only [D]` (D defined by pattern matching) · goal: `D … (.c …)` → that clause -/
example (v : Nat → Bool) (a b : BExp) (P : Bool → Prop) (h : P (beval v a && beval v b)) :
    P (beval v (.and a b)) := by
  simp only [beval]
  exact h

/-! ### R4. `simp [h]` with `h : e = false` · goal: `e` → `false`, then Bool laws close it -/
example (x y : Bool) (h : x = false) : (x && y) = false := by
  simp [h]

/-! ## Naming what unification cannot find -/

/-! ### R5. `refine .c (y := t) ?_ ?_` (named implicit argument) · goal → one goal per premise
A variable that occurs only in the premises (here `y`) is not fixed by the goal. Name it with
`(y := t)`; each `?_` becomes a new goal. Without `(y := t)`: "don't know how to synthesize
implicit argument `y`". -/
example {E : List (Nat × Nat)} (x y z : Nat) (h1 : Reach E x y) (h2 : Reach E y z) :
    Reach E x z := by
  refine .trans (y := y) ?_ ?_
  exact h1
  exact h2

/-! ## Induction on a derivation -/

/-! ### R6. `induction h` (h : an inductive predicate) · goal list: one goal per rule, IHs added
The list argument is the same in every rule, so Lean treats it as a parameter: `induction h` works
even though it is `e :: E` rather than a variable. Each recursive premise gets an IH (`a_ih✝`).
`induction h with | edge hm => … | refl => … | trans h₁ h₂ ih₁ ih₂ => …` names the explicit
premises, then the IHs; implicit fields such as `{x y}` stay inaccessible (`x✝`). -/
example (P : Nat → Nat → Prop) (e : Nat × Nat) (E : List (Nat × Nat))
    (he : ∀ x y, (x, y) ∈ e :: E → P x y) (hr : ∀ x, P x x)
    (ht : ∀ x y z, P x y → P y z → P x z) {x y : Nat} (h : Reach (e :: E) x y) : P x y := by
  induction h
  case edge x y hm => exact he x y hm
  case refl x => exact hr x
  case trans x y z _ _ ih1 ih2 => exact ht x y z ih1 ih2

/-! ### R7. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l`; `.mp` turns it into a function
`List.mem_cons.mp hm` is the left-to-right direction applied to `hm`. -/
example {α : Type} (a b : α) (l : List α) (hm : a ∈ b :: l) (P : Prop) (h : a = b ∨ a ∈ l → P) :
    P := by
  have hm' := List.mem_cons.mp hm
  exact h hm'

/-! ### R8. `rcases h with rfl | h` · goal list: one goal per side of `∨`; `rfl` substitutes
In the left goal the equation `x = a` is used up: `a` is replaced by `x` everywhere. -/
example (Q : Nat → Prop) (a x : Nat) (S : List Nat) (h : x = a ∨ x ∈ S) (ha : Q a)
    (hS : x ∈ S → Q x) : Q x := by
  rcases h with rfl | h
  exact ha
  exact hS h

/-! ## Backward steps and list membership -/

/-! ### R9. `apply lem` · goal: `lem`'s conclusion → `lem`'s premise
`lem`'s implicit arguments are read off the goal. -/
example (Q R : Nat → Prop) (lem : ∀ {n : Nat}, Q n → R n) (n : Nat) (h : Q n) : R n := by
  apply lem
  exact h

/-! ### R10. `by simp` · closes `x ∈ [explicit list]` when `x` is one of the listed terms
It fails when `x` is still a metavariable `?a`: name the implicit first (R5). -/
example (a b c : Nat) (S : List Nat) : b ∈ a :: b :: c :: S := by simp

/-! ### R11. `hS x hx` with `hS : ∀ g ∈ S, Q g` · goal closed
Lean prints `∀ g ∈ S, Q g` as `∀ (g : Nat), g ∈ S → Q g`: a function of `g` and a membership proof. -/
example (Q : Nat → Prop) (S : List Nat) (hS : ∀ g ∈ S, Q g) (x : Nat) (hx : x ∈ S) : Q x := by
  exact hS x hx

/-! ## Rewriting with an `↔` and closing Bool goals -/

/-! ### R12. `simp only [hQR]` with `hQR : ∀ n, Q n ↔ R n` · goal: every `Q _` → `R _`
`simp` and `rw` use an `↔` like an `=` between propositions. -/
example (Q R : Nat → Prop) (hQR : ∀ n, Q n ↔ R n) (x y : Nat) (h : R x → R y) : Q x → Q y := by
  simp only [hQR]
  exact h

/-! ### R13. `simp` · closes a Bool identity that the Bool laws reduce to `true = true`
Here `x || false` → `x` and `!x || x` → `true`. A tautology with no such reduction is left as a
disjunction of cases; then use `cases x <;> simp` (R2). -/
example (x : Bool) : (!(x || false) || x) = true := by simp

/-! ### R14. `hiff.mp hq` · context gains the right side of the `↔`
Here the right side is itself an implication, so `hiff.mp hq ha` would apply it at once. -/
example (Q A B : Prop) (hiff : Q ↔ (A → B)) (hq : Q) (ha : A) : B := by
  have hab := hiff.mp hq
  exact hab ha

/-! ### R15. `simpa [D] using e` · closes the goal: simplify `e`'s type and the goal, then match
Here `e := hf (.neg .tt)` has type `beval v (.neg .tt) = true`, which simplifies to `false = true`,
i.e. `False`, and `False` closes any goal. (When `e` is just a hypothesis `h`, write `simp [D] at h`.) -/
example (v : Nat → Bool) (hf : ∀ a, beval v a = true) : False := by
  simpa [beval] using hf (.neg .tt)

/-! ### R16. `by simp` · closes `∀ g ∈ [], Q g` (nothing is in the empty list) -/
example (Q : Nat → Prop) : ∀ g ∈ ([] : List Nat), Q g := by simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A derivation in term mode, cut point named, membership by `simp`: R1, R5, R10 -/
example : Reach [(1, 2), (2, 3)] 1 3 :=
  .trans (y := 2) (.edge (by simp)) (.edge (by simp))

/-! ### W2. Membership in `a :: S`, split into "it is `a`" and "it is in `S`": R7, R8, R11 -/
example (Q : Nat → Prop) (a : Nat) (S : List Nat) (ha : Q a) (hS : ∀ g ∈ S, Q g) (g : Nat)
    (hg : g ∈ a :: S) : Q g := by
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ha
  · exact hS g hg

/-! ### W3. A soundness proof by induction on the derivation: R6, R11
If every edge goes upward, everything reachable is above. -/
example (E : List (Nat × Nat)) (hE : ∀ p ∈ E, p.1 ≤ p.2) {x y : Nat} (h : Reach E x y) :
    x ≤ y := by
  induction h with
    | edge hm => exact hE _ hm
    | refl => exact Nat.le_refl _
    | trans _ _ ih1 ih2 => exact Nat.le_trans ih1 ih2

/-! ### W4. A Bool `↔` by cases on one subterm, then unfolding: R2, R3, R4 -/
example (v : Nat → Bool) (a b : BExp) :
    beval v (.and a b) = true ↔ (beval v a = true ∧ beval v b = true) := by
  cases h : beval v a <;> simp [beval, h]

end H001Guide
