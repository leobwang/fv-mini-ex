/- Guide for H016 (Prefix codes from a code tree).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a tree that stores numbers, a
depth function, a two-symbol reader).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace H016Guide

/-- A binary tree with labels at the leaves (the guide's own tree type). -/
inductive Tr (α : Type) where
  | leaf (a : α)
  | node (l r : Tr α)

/-- Depth of the leftmost leaf `a` in the LEFT spine only (a toy search with an `if` and a `match`). -/
def leftDepth {α : Type} [DecidableEq α] : Tr α → α → Option Nat
  | .leaf b, a => if a = b then some 0 else none
  | .node l _, a =>
    match leftDepth l a with
    | some n => some (n + 1)
    | none => none

/-- Read one bit and pick `l` (bit `false`) or `r` (bit `true`); return the pick and the unread bits. -/
def pick {α : Type} (l r : α) : List Bool → Option (α × List Bool)
  | [] => none
  | b :: bs => some (if b then r else l, bs)

/-! # Part R · Reference entries -/

/-! ## Part 1 · Induction on a tree, opening `if` and `match` in a hypothesis -/

/-! ### R1. `induction t generalizing c` · goal list: one goal per constructor; `c` stays universally
quantified in each induction hypothesis
Without `with`, the new names are inaccessible (`a✝`, `l✝`, `a_ih✝`). Write
`induction t generalizing c with | leaf a => … | node l r ihl ihr => …` to name them. -/
example {α : Type} (P : Tr α → List Bool → Prop) (hl : ∀ a c, P (.leaf a) c)
    (hn : ∀ l r, (∀ c, P l c) → (∀ c, P r c) → ∀ c, P (.node l r) c) (t : Tr α) (c : List Bool) :
    P t c := by
  induction t generalizing c
  case leaf a => exact hl a c
  case node l r ihl ihr => exact hn l r ihl ihr c

/-! ### R2. `simp only [f] at h` · context: `h` with `f` applied to a constructor → `f`'s body for
that constructor -/
example {α : Type} [DecidableEq α] (a b : α) (n : Nat) (Q : Prop)
    (h : leftDepth (.leaf b) a = some n) (k : (if a = b then some 0 else none) = some n → Q) : Q := by
  simp only [leftDepth] at h
  exact k h

/-! ### R3. `split at h` (an `if`) · goal list: two goals; context gains the condition `h✝ : c` or
`h✝ : ¬c`, and `h` becomes that branch -/
example {α : Type} [DecidableEq α] (a b : α) (n : Nat) (Q : Prop)
    (h : (if a = b then some 0 else none) = some n)
    (k1 : some 0 = some n → Q) (k2 : none = some n → Q) : Q := by
  split at h
  · exact k1 h
  · exact k2 h

/-! ### R4. `subst_vars` · context: every hypothesis `x = e` (or `e = x`) with `x` a variable is used to
replace `x` by `e` everywhere, then dropped -/
example {α : Type} (a b : α) (P : α → α → Prop) (hab : a = b) (h : P b b) : P a b := by
  subst_vars
  exact h

/-! ### R5. `cases h` with `h : some e = some c`, `c` a variable · context: `h` gone, `c` replaced by `e`
`Option.some` is a constructor, so the two sides must have equal arguments; Lean substitutes. -/
example (e c : List Bool) (P : List Bool → Prop) (h : some e = some c) (k : P e) : P c := by
  cases h
  exact k

/-! ### R6. `simp [f]` · goal: unfold `f` at a constructor argument and reduce `if false = true` / `if
true = true`
`if b then x else y` with `b : Bool` means `if b = true then x else y`; `simp` knows
`(false = true) = False` (`Bool.false_eq_true`) and then picks the branch (`↓reduceIte`). -/
example {α : Type} (l r : α) (bs : List Bool) (P : Option (α × List Bool) → Prop)
    (h : P (some (l, bs))) : P (pick l r (false :: bs)) := by
  simp [pick]
  exact h

/-! ### R7. `cases h` with `h : none = some c` · goal list: the goal is closed
`none` and `some` are different constructors, so the equation is impossible. -/
example (c : List Bool) (Q : Prop) (h : (none : Option (List Bool)) = some c) : Q := by
  cases h

/-! ### R8. `split at h` (a `match` on `f x`) · goal list: one goal per `match` arm; context gains the
equation of the arm (`heq✝ : f x = some n✝`) and `h` becomes that arm -/
example (f : Nat → Option Nat) (x m : Nat) (Q : Prop)
    (h : (match f x with
          | some n => some (n + 1)
          | none => none) = some m) (q : Q) : Q := by
  split at h
  all_goals exact q

/-! ### R9. `rename_i x hx` · context: the LAST inaccessible names (`n✝`, `heq✝`) get the names `x hx`,
in order -/
example (f : Nat → Option Nat) (x : Nat) (Q : Nat → Prop) (k : ∀ n, f x = some n → Q n) :
    ∀ n, f x = some n → Q n := by
  intro _ _
  rename_i n hn
  exact k n hn

/-! ### R10. `simp [ih _ hc]` · goal: use an instantiated hypothesis as a rewrite rule
`ih : ∀ c, Q c → g (c ++ rest) = some y`; `ih _ hc` is the equation for the `c` that `hc` mentions
(`_` lets Lean read `c` off `hc`). -/
example (Q : List Bool → Prop) (g : List Bool → Option Nat) (rest : List Bool) (y : Nat)
    (ih : ∀ c, Q c → g (c ++ rest) = some y) (c : List Bool) (hc : Q c) (P : Option Nat → Prop)
    (h : P (some y)) : P (g (c ++ rest)) := by
  simp [ih _ hc]
  exact h

/-! ## Part 2 · Induction on the message, a `match` on two values -/

/-! ### R11. `simp [f] at h` · context: unfold `f` in `h`, then simplify; `some x = some y` becomes
`x = y` (lemma `Option.some.injEq`), and `[] = bs` is turned around to `bs = []` (`List.nil_eq`) -/
def code0 : List Nat → Option (List Bool)
  | [] => some []
  | _ :: _ => none

example (bs : List Bool) (Q : Prop) (h : code0 [] = some bs) (k : bs = [] → Q) : Q := by
  simp [code0] at h
  exact k h

/-! ### R12. `subst h` with `h : x = e` (or `e = x`), `x` a variable · context: `x` replaced by `e`
everywhere, `h` dropped -/
example (bs : List Bool) (P : List Bool → Prop) (h : bs = []) (k : P []) : P bs := by
  subst h
  exact k

/-! ### R13. `split at h` (a `match` on TWO values with a fall-through arm `| _, _ => …`) · goal list:
two goals. The first gets `heq✝¹ : f a = some m✝`, `heq✝ : f b = some n✝`. The fall-through goal gets
`x✝ : ∀ (m n : Nat), f a = some m → f b = some n → False`: "not the first arm". -/
example (f : Nat → Option Nat) (a b k : Nat) (Q : Prop)
    (h : (match f a, f b with
          | some m, some n => some (m + n)
          | _, _ => none) = some k) (q : Q) : Q := by
  split at h
  all_goals exact q

/-! ### R14. `List.length_cons` · `(a :: as).length = as.length + 1` · goal -/
example {α : Type} (a : α) (as : List α) (P : Nat → Prop) (h : P (as.length + 1)) :
    P (a :: as).length := by
  rw [List.length_cons]
  exact h

/-! ### R15. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal
`++` groups to the left: `as ++ bs ++ cs` is `(as ++ bs) ++ cs`. -/
example {α : Type} (as bs cs : List α) (P : List α → Prop) (h : P (as ++ (bs ++ cs))) :
    P (as ++ bs ++ cs) := by
  rw [List.append_assoc]
  exact h

/-! ### R16. `simp [hx]` with `hx : g x = some y` · goal: a `match g x with …` → the `some` arm at `y` -/
example (g : Nat → Option Nat) (x y : Nat) (hx : g x = some y) (P : Option Nat → Prop)
    (h : P (some (y + 1))) :
    P (match g x with
       | none => none
       | some z => some (z + 1)) := by
  simp [hx]
  exact h

/-! ## Part 3 · Prefixes -/

/-! ### R17. `obtain ⟨rest, rfl⟩ := hpre` with `hpre : xs <+: ys` · context: `hpre` gone, new
`rest`, and `ys` replaced by `xs ++ rest` everywhere
`xs <+: ys` is `List.IsPrefix xs ys`, defined as `∃ t, xs ++ t = ys`. The pattern `rfl` substitutes. -/
example {α : Type} (xs ys : List α) (P : List α → List α → Prop) (hpre : xs <+: ys)
    (k : ∀ rest, P xs (xs ++ rest)) : P xs ys := by
  obtain ⟨rest, rfl⟩ := hpre
  exact k rest

/-! ### R18. `have h1 := lem x c hq` · context gains `h1` = the statement of `lem` at those arguments
No type is written: Lean computes it by substituting the arguments. -/
example {α : Type} (Q R : α → List Bool → Prop) (lem : ∀ (x : α) (c : List Bool), Q x c → R x c)
    (x : α) (c : List Bool) (hq : Q x c) (G : Prop) (k : R x c → G) : G := by
  have h1 := lem x c hq
  exact k h1

/-! ### R19. `rw [List.append_nil] at h` · `as ++ [] = as` · context: `h` rewritten -/
example {α : Type} (xs : List α) (Q : List α → Prop) (h : Q (xs ++ [])) (G : Prop) (k : Q xs → G) :
    G := by
  rw [List.append_nil] at h
  exact k h

/-! ### R20. `rw [e] at h` with `e : u = v` · context: every `u` in `h` replaced by `v` -/
example {β : Type} (u v w : β) (e : u = v) (h : u = w) (G : Prop) (k : v = w → G) : G := by
  rw [e] at h
  exact k h

/-! ### R21. `cases h` with `h : some (x, xs) = some (y, [])`, `x y xs` variables · context: `h`
gone; the pairs are matched componentwise, so `y` becomes `x` and `xs` becomes `[]` everywhere -/
example {α : Type} (x y : α) (xs : List Bool) (P : α → α → List Bool → Prop)
    (h : some (x, xs) = some (y, [])) (k : ∀ z, P z z []) : P x y xs := by
  cases h
  exact k _

/-! ## Part 4 · Specializing a strengthened statement -/

/-! ### R22. `simpa using e` · goal closed: simplify both the type of `e` and the goal, then match them
Here `simp` removes the `++ []` in `e`'s type (lemma `List.append_nil`). -/
example {α : Type} (xs : List α) (P : List α → Prop) (e : P (xs ++ [])) : P xs := by
  simpa using e

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction on a tree + opening `if` and `match` in a hypothesis (R1, R2, R3, R5, R7, R8,
R9): a depth found by `leftDepth` is at most the tree's height. -/
def height {α : Type} : Tr α → Nat
  | .leaf _ => 0
  | .node l r => Nat.max (height l) (height r) + 1

example {α : Type} [DecidableEq α] (t : Tr α) (a : α) (n : Nat) (h : leftDepth t a = some n) :
    n ≤ height t := by
  induction t generalizing n with
    | leaf b =>
      simp only [leftDepth] at h
      split at h
      · cases h; exact Nat.le_refl 0
      · cases h
    | node l r ihl ihr =>
      simp only [leftDepth] at h
      split at h
      · rename_i m hm
        cases h
        simp only [height]
        exact Nat.succ_le_succ (Nat.le_trans (ihl m hm) (Nat.le_max_left _ _))
      · cases h

/-! ### W2. Reading two bits in a row (R6, R16): `simp` unfolds `pick` and reduces both `match`es -/
def pick2 {α : Type} (l r : α) (bs : List Bool) : Option (α × α × List Bool) :=
  match pick l r bs with
  | none => none
  | some (x, bs') =>
    match pick l r bs' with
    | none => none
    | some (y, rest) => some (x, y, rest)

example {α : Type} (l r : α) (rest : List Bool) :
    pick2 l r (true :: false :: rest) = some (r, l, rest) := by
  simp [pick2, pick]

/-! ### W3. Strengthen with `rest`, then specialize to `[]` (R18, R22) -/
example {α : Type} (l r : α) (bs : List Bool) (hall : ∀ rest, pick l r (false :: bs ++ rest) = some (l, bs ++ rest)) :
    pick l r (false :: bs) = some (l, bs) := by
  simpa using hall []

end H016Guide
