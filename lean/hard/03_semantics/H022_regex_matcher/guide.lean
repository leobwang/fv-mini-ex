/- Guide for H022 (Regex matcher).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).

The entries run on a toy pattern language `Sh` with a word relation `Gen`, built like the exercise's
`Re` and `Matches` but different: `atom n` produces the word `[n, n]`, `two a b` concatenates, `many a`
repeats. `hasMany` is a Bool-valued function on it.
-/

namespace H022Guide

/-- Toy patterns (not the exercise's regexes). -/
inductive Sh where
  | atom (n : Nat)
  | two (a b : Sh)
  | many (a : Sh)

/-- `Gen s w`: pattern `s` produces word `w`. An inductive *predicate*: its constructors are the rules. -/
inductive Gen : Sh → List Nat → Prop
  | atom (n : Nat) : Gen (.atom n) [n, n]
  | two {a b : Sh} {u v : List Nat} : Gen a u → Gen b v → Gen (.two a b) (u ++ v)
  | manyNil {a : Sh} : Gen (.many a) []
  | manyCons {a : Sh} {u v : List Nat} : Gen a u → Gen (.many a) v → Gen (.many a) (u ++ v)

/-- A Bool-valued function by pattern matching on `Sh`. -/
def hasMany : Sh → Bool
  | .atom _ => false
  | .two a b => hasMany a || hasMany b
  | .many _ => true

/-- A structurally recursive function on the word, for R28. -/
def countOf (n : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x = n then 1 else 0) + countOf n xs

/-! # Part R · Reference entries -/

/-! ## Part 1 · Inverting a derivation -/

/-! ### R1. `cases h` on `h : Gen (.two a b) w` (inversion) · context: `h` → its premises; goal: `w` → `u ++ v`
Only the constructor whose conclusion fits `Gen (.two _ _) _` survives. It works because the word `w` is a
variable: with `x :: w` in its place, `x :: w = u ++ v` cannot be solved and `cases` fails. -/
example (a b : Sh) (w : List Nat) (P : List Nat → Prop)
    (h : Gen (.two a b) w) (k : ∀ u v, Gen a u → Gen b v → P (u ++ v)) : P w := by
  cases h
  exact k _ _ ‹_› ‹_›

/-! ### R2. `rename_i u v hu hv` · context: names the newest inaccessible (`✝`) hypotheses, in order -/
example (a b : Sh) (w : List Nat) (P : List Nat → Prop)
    (h : Gen (.two a b) w) (k : ∀ u v, Gen a u → Gen b v → P (u ++ v)) : P w := by
  cases h
  rename_i u v hu hv
  exact k u v hu hv

/-! ### R3. `exact ⟨_, _, rfl, hu, hv⟩` · closes `∃ x y, e = … ∧ …`: `_` is found by unification -/
example (a b : Sh) (u v : List Nat) (hu : Gen a u) (hv : Gen b v) :
    ∃ x y, u ++ v = x ++ y ∧ Gen a x ∧ Gen b y := by
  exact ⟨_, _, rfl, hu, hv⟩

/-! ## Part 2 · Induction on a syntax tree, Bool facts -/

/-! ### R4. `induction t with` on an inductive type · goal list: one goal per constructor, with an IH
for each argument of type `Sh`. -/
example (P : Sh → Prop) (h1 : ∀ n, P (.atom n)) (h2 : ∀ a b, P a → P b → P (.two a b))
    (h3 : ∀ a, P a → P (.many a)) (t : Sh) : P t := by
  induction t
  case atom n => exact h1 n
  case two a b iha ihb => exact h2 a b iha ihb
  case many a iha => exact h3 a iha

/-! ### R5. `simp [f]` on `f (constructor …) = true ↔ Q` · goal: unfolds `f`, then `false = true ↔ Q` → `¬Q` -/
example (n : Nat) (Q : Prop) (h : ¬Q) : hasMany (.atom n) = true ↔ Q := by
  simp [hasMany]
  exact h

example (a : Sh) (Q : Prop) (h : Q) : hasMany (.many a) = true ↔ Q := by
  simp [hasMany]
  exact h

/-! ### R6. `cases h` when no constructor fits · closes the goal (`[n, n]` is never `[]`) -/
example (n : Nat) (P : Prop) (h : Gen (.atom n) []) : P := by
  cases h

/-! ### R7. `Bool.or_eq_true` · `((a || b) = true) = (a = true ∨ b = true)` · goal -/
example (a b : Bool) (P : Prop → Prop) (h : P (a = true ∨ b = true)) : P ((a || b) = true) := by
  simp only [Bool.or_eq_true]
  exact h

/-! ### R8. `Bool.and_eq_true` · `((a && b) = true) = (a = true ∧ b = true)` · goal -/
example (a b : Bool) (P : Prop → Prop) (h : P (a = true ∧ b = true)) : P ((a && b) = true) := by
  simp only [Bool.and_eq_true]
  exact h

/-! ### R9. `simp only [ih]` with `ih : ∀ x, f x = true ↔ Q x` · goal: every `f e = true` → `Q e` -/
example {α : Type} (f : α → Bool) (Q : α → Prop) (ih : ∀ x, f x = true ↔ Q x) (e : α)
    (P : Prop → Prop) (h : P (Q e)) : P (f e = true) := by
  simp only [ih]
  exact h

/-! ### R10. `exact .two (u := x) (v := y) h₁ h₂` · closes: a constructor, named implicit arguments
`.two` means `Gen.two`, read off the goal. `(u := x)` fixes the implicit argument `u`. -/
example (a b : Sh) (h₁ : Gen a []) (h₂ : Gen b []) : Gen (.two a b) [] := by
  exact .two (u := []) (v := []) h₁ h₂

example (a b : Sh) (x : Nat) (u v : List Nat) (h₁ : Gen a (x :: u)) (h₂ : Gen b v) :
    Gen (.two a b) (x :: (u ++ v)) := by
  exact .two (u := x :: u) h₁ h₂

/-! ### R11. `obtain ⟨rfl, rfl⟩ := h` with `h : u = e ∧ v = e'` · context: the variables `u v` are replaced -/
example {α : Type} (u v : List α) (P : List α → List α → Prop) (h : u = [] ∧ v = [])
    (k : P [] []) : P u v := by
  obtain ⟨rfl, rfl⟩ := h
  exact k

/-! ### R12. `List.append_eq_nil_iff` · `p ++ q = [] ↔ p = [] ∧ q = []`; `h.symm` flips `[] = p ++ q` -/
example {α : Type} (p q : List α) (h : [] = p ++ q) (P : List α → List α → Prop)
    (k : P [] []) : P p q := by
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm
  exact k

/-! ## Part 3 · Rule induction with a non-variable index -/

/-! ### R13. `generalize hy : e = y at h` · context: `e` in `h` → a fresh variable `y`, plus `hy : e = y`
Needed before `cases`/`induction` on `h` when an index of `h` is not a variable (`x :: w`, `.many a`). -/
example (a : Sh) (x : Nat) (w : List Nat) (h : Gen (.many a) (x :: w)) (P : Prop)
    (k : ∀ y, Gen (.many a) y → x :: w = y → P) : P := by
  generalize hy : x :: w = y at h
  exact k y h hy

/-! ### R14. `induction h generalizing w` (rule induction) · goal list: one goal per rule of `Gen`
The equations `hs`, `hy` mention the indices `s y`, so each case restates them for that rule, and each IH
gets them as premises. `generalizing w` makes the IH hold for every `w`. -/
example (a : Sh) (x : Nat) (w y : List Nat) (s : Sh) (h : Gen s y) (hs : Sh.many a = s)
    (hy : x :: w = y) (P : Prop) (k : P) : P := by
  induction h generalizing w
  case manyCons b u v hu hv ihu ihv => exact k
  all_goals exact k

/-! ### R15. `cases h` on `h : C a = C b` (same constructor) · context: `b` replaced by `a`
(Constructors are injective.) -/
example (a b : Sh) (h : Sh.many a = Sh.many b) (P : Sh → Prop) (k : P a) : P b := by
  cases h
  exact k

/-! ### R16. `cases h` on `h : C₁ … = C₂ …` (different constructors) · closes the goal -/
example (a b c : Sh) (h : Sh.many a = Sh.two b c) (P : Prop) : P := by
  cases h

example (x : Nat) (w : List Nat) (h : x :: w = []) (P : Prop) : P := by
  cases h

/-! ### R17. `| _ => tac` · goal list: runs `tac` on every case not named above it -/
example (t : Sh) (P : Sh → Prop) (h1 : ∀ n, P (.atom n)) (h : ∀ a, P a) : P t := by
  induction t with
    | atom n => exact h1 n
    | _ => exact h _

/-! ### R18. `List.cons_append` · `a :: as ++ bs = a :: (as ++ bs)` · goal
`a :: as ++ bs` parses as `(a :: as) ++ bs`. -/
example {α : Type} (a : α) (as bs : List α) (P : List α → Prop) (h : P (a :: (as ++ bs))) :
    P (a :: as ++ bs) := by
  rw [List.cons_append]
  exact h

/-! ### R19. `List.cons.injEq` · `(a :: as = b :: bs) = (a = b ∧ as = bs)` · context with `at h` -/
example {α : Type} (a b : α) (as bs : List α) (h : a :: as = b :: bs) (P : Prop)
    (k : a = b ∧ as = bs → P) : P := by
  simp only [List.cons.injEq] at h
  exact k h

/-! ## Part 4 · Derivatives: `if`, substitution, splitting a word -/

/-! ### R20. `induction t generalizing w` · goal list as R4, and each IH is `∀ w, …` -/
example (t : Sh) (w : List Nat) (P : Sh → List Nat → Prop) (h : ∀ s v, P s v) : P t w := by
  induction t generalizing w
  all_goals exact h _ _

/-! ### R21. `split` · goal list: `P (if c then t else e)` → `P t` with `h✝ : c`, and `P e` with `h✝ : ¬c` -/
example (c : Prop) [Decidable c] {α : Type} (t e : α) (P : α → Prop) (ht : c → P t)
    (he : ¬c → P e) : P (if c then t else e) := by
  split
  · rename_i hc
    exact ht hc
  · rename_i hc
    exact he hc

/-! ### R22. `split at h` · goal list: the same split for an `if` inside hypothesis `h` -/
example (c : Prop) [Decidable c] {α : Type} (t e : α) (P : α → Prop) (Q : Prop)
    (h : P (if c then t else e)) (kt : c → P t → Q) (ke : ¬c → P e → Q) : Q := by
  split at h
  · rename_i hc
    exact kt hc h
  · rename_i hc
    exact ke hc h

/-! ### R23. `subst h` with `h : a = b`, `b` a variable · context: `b` replaced by `a` everywhere -/
example (a b : Char) (h : a = b) (P : Char → Char → Prop) (k : P a a) : P a b := by
  subst h
  exact k

/-! ### R24. `absurd` · `absurd : a → ¬a → b` · closes any goal from `h : ¬(x = x)` -/
example (x : Char) (h : ¬x = x) (P : Prop) : P := by
  exact absurd rfl h

/-! ### R25. `(ih x).mp`, `(ih x).mpr` · use an IH `ih : ∀ x, A x ↔ B x` at the word you need -/
example (A B : List Nat → Prop) (ih : ∀ x, A x ↔ B x) (w : List Nat) (h : A w) : B w := by
  exact (ih w).mp h

example (A B : List Nat → Prop) (ih : ∀ x, A x ↔ B x) (w : List Nat) (h : B w) : A w := by
  exact (ih w).mpr h

/-! ### R26. `List.append_eq_cons_iff` · `as ++ bs = x :: c ↔ (as = [] ∧ bs = x :: c) ∨ ∃ as', as = x :: as' ∧ c = as' ++ bs`
With `rcases … with ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩`: goal list, `u` is `[]` or `x :: u'`. -/
example {α : Type} (u v w : List α) (x : α) (h : x :: w = u ++ v) (P : List α → List α → Prop)
    (k1 : P [] (x :: w)) (k2 : ∀ u', P (x :: u') v) : P u v := by
  rcases List.append_eq_cons_iff.mp h.symm with ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩
  · exact k1
  · exact k2 u'

/-! ### R27. `simp only [hb, if_true]` with `hb : b = true` · goal: `if b = true then t else e` → `t`
`if_true : (if True then t else e) = t`. -/
example (b : Bool) (hb : b = true) {α : Type} (t e : α) (P : α → Prop) (h : P t) :
    P (if b then t else e) := by
  simp only [hb, if_true]
  exact h

/-! ## Part 5 · The main theorem -/

/-! ### R28. `simp only [f]` on `f (x :: xs)` · goal: one step of a structurally recursive function -/
example (n x : Nat) (xs : List Nat) (P : Nat → Prop) (h : P ((if x = n then 1 else 0) + countOf n xs)) :
    P (countOf n (x :: xs)) := by
  simp only [countOf]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R13 → R14 → R15/R16 → R17: every letter of a word of `many (atom n)` is `n`
The index `.many (.atom n)` is not a variable, so generalize it first; the impossible rules die by `cases hs`. -/
example (n : Nat) (w : List Nat) (h : Gen (.many (.atom n)) w) : ∀ x ∈ w, x = n := by
  generalize hs : Sh.many (.atom n) = s at h
  induction h with
    | manyNil => intro x hx; cases hx
    | @manyCons a u v hu _ _ ihv =>
      cases hs
      cases hu
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl) | hx
      · rfl
      · rfl
      · exact ihv rfl x hx
    | _ => cases hs

/-! ### W2. R20-style list induction, then R28 → R9 → R8: a Bool test agrees with a Prop -/
def allEq (n : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => (x == n) && allEq n xs

example (n : Nat) (xs : List Nat) : allEq n xs = true ↔ ∀ x ∈ xs, x = n := by
  induction xs with
    | nil => simp [allEq]
    | cons x xs ih => simp only [allEq, Bool.and_eq_true, ih, beq_iff_eq, List.forall_mem_cons]

end H022Guide
