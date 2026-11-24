/- Guide for M034 (Two-stack queue).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is a
goal the step does not touch. A hypothesis `h`/`g` in an entry is only there to finish the example.
Part W: worked combinations on objects that are NOT the exercise's (a `Buf` structure, a reset counter).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M034Guide

/-- A two-field structure the examples use (not the exercise's queue). -/
structure Buf (α : Type) where
  inp : List α
  out : List α

def Buf.swap {α : Type} (p : Buf α) : Buf α := ⟨p.out, p.inp⟩

def Buf.all {α : Type} (p : Buf α) : List α := p.inp ++ p.out

/-! # Part R · Reference entries -/

/-! ## Unfolding definitions; list algebra -/

/-! ### R1. `simp only [d₁, d₂]` · goal: names → bodies; a field of `⟨a, b⟩` → `a` or `b`
`⟨p.out, p.inp⟩ : Buf α` prints as `{ inp := p.out, out := p.inp }`; `simp` reduces
`{ inp := p.out, out := p.inp }.inp` to `p.out` by itself. -/
example {α : Type} (p : Buf α) (P : List α → Prop) (h : P (p.out ++ p.inp)) : P p.swap.all := by
  simp only [Buf.all, Buf.swap]
  exact h

/-! ### R2. `List.reverse_cons` · `(a :: as).reverse = as.reverse ++ [a]` · goal -/
example {α : Type} (a : α) (as : List α) (P : List α → Prop) (h : P (as.reverse ++ [a])) :
    P (a :: as).reverse := by
  rw [List.reverse_cons]
  exact h

/-! ### R3. `List.append_assoc` · `as ++ bs ++ cs = as ++ (bs ++ cs)` · goal
`++` groups to the left: `as ++ bs ++ cs` is `(as ++ bs) ++ cs`. -/
example {α : Type} (as bs cs : List α) (P : List α → Prop) (h : P (as ++ (bs ++ cs))) :
    P (as ++ bs ++ cs) := by
  rw [List.append_assoc]
  exact h

/-! ## Case splits on data -/

/-! ### R4. `obtain ⟨a, b⟩ := p` · context: `p : Buf α` → its two fields `a b`; goal shows `{ inp := a, out := b }` -/
example {α : Type} (p : Buf α) (P : Buf α → Prop) (h : ∀ a b, P ⟨a, b⟩) : P p := by
  obtain ⟨a, b⟩ := p
  exact h a b

/-! ### R5. `cases l with | nil => _ | cons y f => _` · goal list: one goal per constructor
Works on any inductive type: `List` (`nil`, `cons`), `Option` (`none`, `some`), your own `inductive`.
`?_` in an arm leaves that goal open for the next tactics (here, so the infoview shows both). -/
example {α : Type} (l : List α) (P : List α → Prop) (h0 : P []) (h1 : ∀ y f, P (y :: f)) : P l := by
  cases l with
    | nil => ?_
    | cons y f => ?_
  exact h0
  exact h1 y f

/-! ## Pattern-matching definitions inside hypotheses -/

/-- A pattern-matching function with a nested `match` (not the exercise's). -/
def Buf.peek {α : Type} : Buf α → Option α
  | ⟨x :: _, _⟩ => some x
  | ⟨[], o⟩ =>
    match o.reverse with
    | [] => none
    | x :: _ => some x

/-! ### R6. `simp only [d] at h` · context: `h` with `d` unfolded; the arm that matches is chosen
When the argument's shape is known (`y :: f`), the outer match disappears. When it is `[]`, the
inner `match o.reverse with …` stays: Lean cannot know the shape of `o.reverse`. -/
example {α : Type} (y a : α) (f o : List α) (G : Prop) (h : (Buf.peek ⟨y :: f, o⟩) = some a)
    (g : some y = some a → G) : G := by
  simp only [Buf.peek] at h
  exact g h

example {α : Type} (o : List α) (a : α) (G : Prop) (h : (Buf.peek ⟨[], o⟩) = some a)
    (g : (match o.reverse with | [] => none | x :: _ => some x) = some a → G) : G := by
  simp only [Buf.peek] at h
  exact g h

/-! ### R7. `Option.some.injEq` · `(some a = some b) = (a = b)` · context (with `simp only … at h`) -/
example {α : Type} (a b : α) (G : Prop) (h : some a = some b) (g : a = b → G) : G := by
  simp only [Option.some.injEq] at h
  exact g h

/-! ### R8. `Prod.mk.injEq` · `((a, b) = (c, d)) = (a = c ∧ b = d)` · context -/
example {α β : Type} (a c : α) (b d : β) (G : Prop) (h : (a, b) = (c, d))
    (g : a = c ∧ b = d → G) : G := by
  simp only [Prod.mk.injEq] at h
  exact g h

/-! ### R9. `obtain ⟨rfl, rfl⟩ := h` · context: `h : a = x ∧ s = y` (x, y local variables) is used up;
`x` and `y` are replaced everywhere by `a` and `s` -/
example {α : Type} (a x : α) (s y : List α) (P : α → List α → Prop) (hp : P a s)
    (h : a = x ∧ s = y) : P x y := by
  obtain ⟨rfl, rfl⟩ := h
  exact hp

/-! ### R10. `split at h` · goal list: one goal per arm of the `match` inside `h`
Each goal gets `heq✝ : (the matched expression) = (the arm's pattern)`, and `h` shows that arm. -/
example {α : Type} (l : List α) (a : α) (G : Prop)
    (h : (match l.reverse with | [] => none | x :: _ => some x) = some a)
    (g : ∀ y, some y = some a → G) : G := by
  split at h
  · contradiction
  · exact g _ h

/-! ### R11. `contradiction` · closes the goal: a hypothesis equates two different constructors -/
example {α : Type} (a : α) (G : Prop) (h : none = some a) : G := by
  contradiction

/-! ### R12. `rename_i y t hb` · context: names the most recent inaccessible hypotheses (`x✝`, `t✝`, `heq✝`)
Names are given to the LAST inaccessible hypotheses, in order; earlier ones (`x✝¹`) keep their `✝`. -/
example {α : Type} (l : List α) (a : α) (G : Prop)
    (h : (match l.reverse with | [] => none | x :: _ => some x) = some a)
    (g : ∀ y t, l.reverse = y :: t → some y = some a → G) : G := by
  split at h
  contradiction
  rename_i y t hb
  exact g y t hb h

/-! ## Using equations between data -/

/-! ### R13. `match hd : e with | none => _ | some (y, z) => _` · goal list, context gains `hd`
Splits on the value of `e`; `hd` records it; occurrences of `e` in the goal become the pattern. -/
example {α β : Type} (e : Option (α × β)) (P : Option (α × β) → Prop) (h0 : P none)
    (h1 : ∀ y z, P (some (y, z))) : P e := by
  match hd : e with
    | none => ?_
    | some (y, z) => ?_
  exact h0
  exact h1 y z

/-! ### R14. `simp [hb] at h` · closes the goal when `h` simplifies to `False`
`[] = x :: l`, `some a = none` are `False` (different constructors); `simp` then closes any goal. -/
example {α : Type} (e l : List α) (x : α) (G : Prop) (hb : e = []) (h : e = x :: l) : G := by
  simp [hb] at h

/-! ### R15. `rw [h] at h'` · context: rewrites inside hypothesis `h'` instead of the goal -/
example {α : Type} (a b : α) (P : α → Prop) (h : a = b) (h' : P a) : P b := by
  rw [h] at h'
  exact h'

/-! ### R16. `injection h with h1 h2` · context: `h : a :: as = b :: bs` → `h1 : a = b`, `h2 : as = bs` -/
example {α : Type} (a b : α) (as bs : List α) (G : Prop) (h : a :: as = b :: bs)
    (g : a = b → as = bs → G) : G := by
  injection h with h1 h2
  exact g h1 h2

/-! ### R17. `subst h1` · context: `h1 : x = y` (y a local variable) used up; `y` replaced by `x` everywhere -/
example {α : Type} (x y : α) (P : α → α → Prop) (hp : P x x) (h1 : x = y) : P x y := by
  subst h1
  exact hp

/-! ### R18. `exact ⟨w, rfl, h.symm⟩` · closes `∃ v, A v ∧ B v`; `h.symm : b = a` from `h : a = b`
`⟨w, p, q⟩` is `⟨w, ⟨p, q⟩⟩` (the anonymous constructor flattens). `rfl` proves `t = t`. -/
example {α : Type} (w : α) (f : α → Nat) (c : Nat) (h : c = f w) :
    ∃ v, some w = some v ∧ f v = c := by
  exact ⟨w, rfl, h.symm⟩

example {α : Type} (a b : α) (h : a = b) : b = a := by
  exact h.symm

/-! ## Case split on an expression -/

/-! ### R19. `cases hb : e with | nil => _ | cons y f => _` · goal list, context gains `hb`
Like R5, but on an expression `e` that is not a variable. Here `e` is not in the goal, so the goal
stays `G`; use `hb` afterwards (`simp [hb]`, R20). -/
example {α : Type} (l : List α) (G : Prop) (h0 : l.reverse = [] → G)
    (h1 : ∀ y f, l.reverse = y :: f → G) : G := by
  cases hb : l.reverse with
    | nil => ?_
    | cons y f => ?_
  exact h0 hb
  exact h1 y f hb

/-! ### R20. `List.reverse_eq_nil_iff` · `xs.reverse = [] ↔ xs = []`; `.mp` reads it left to right
`(h : A ↔ B).mp : A → B`, `.mpr : B → A`. Pass `List.reverse_eq_nil_iff.mp hb` to `simp` as the
rewrite rule `xs = []`. -/
example {α : Type} (xs : List α) (P : List α → Prop) (hb : xs.reverse = []) (hp : P []) : P xs := by
  have hx := List.reverse_eq_nil_iff.mp hb
  rw [hx]
  exact hp

/-! ## Arithmetic over `Nat` -/

/-! ### R21. `List.length_cons` · `(a :: as).length = as.length + 1` · goal -/
example {α : Type} (a : α) (as : List α) (P : Nat → Prop) (h : P (as.length + 1)) :
    P (a :: as).length := by
  rw [List.length_cons]
  exact h

/-! ### R22. `omega` · closes linear (in)equalities over `Nat`/`Int`, using the hypotheses
Any other subterm (`b.length`, `f n`, `c q op`) is an opaque variable to it (an "atom"). -/
example (n : Nat) : 1 + (n + 1) ≤ 2 + n := by
  omega

example (f : Nat → Nat) (n c r k : Nat) (h1 : c + f n ≤ 2 + n) (h2 : r ≤ 2 * k + f n) :
    c + r ≤ 2 * (k + 1) + n := by
  omega

/-! ## Induction with a changing argument -/

/-! ### R23. `induction l generalizing n with | nil => _ | cons a l ih => _` · goal list
`generalizing n` puts `∀ n` into `ih`, so `ih` applies to any `n` (the next state), not only the current one. -/
example {α : Type} (P : Nat → List α → Prop) (n : Nat) (l : List α) (h0 : ∀ n, P n [])
    (hs : ∀ a l, (∀ m, P m l) → ∀ m, P m (a :: l)) : P n l := by
  induction l generalizing n with
    | nil => ?_
    | cons a l ih => ?_
  exact h0 n
  exact hs a l ih n

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R2 then R3: moving a reversed head across `++` -/
example {α : Type} (a : α) (as bs : List α) : (a :: as).reverse ++ bs = as.reverse ++ (a :: bs) := by
  rw [List.reverse_cons]
  rw [List.append_assoc]
  rfl

/-! ### W2. R4, R5, R6, R10, R11, R12, R20: when does `peek` fail? -/
example {α : Type} (p : Buf α) (h : p.peek = none) : p.out = [] := by
  obtain ⟨i, o⟩ := p
  cases i with
    | cons y i => simp [Buf.peek] at h
    | nil =>
      simp only [Buf.peek] at h
      split at h
      · rename_i hb
        exact List.reverse_eq_nil_iff.mp hb
      · contradiction

/-! ### W3. R5 + `simp` + R22, then R23: an amortized bound for a counter that resets
`true` adds one (cost 1); `false` resets to 0 (cost `n + 1`). Potential: the counter value. -/
def tick (n : Nat) : Bool → Nat
  | true => n + 1
  | false => 0

def tcost (n : Nat) : Bool → Nat
  | true => 1
  | false => n + 1

def trun (n : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs => tcost n b + trun (tick n b) bs

theorem tstep (n : Nat) (b : Bool) : tcost n b + tick n b ≤ 2 + n := by
  cases b with
    | true => simp [tcost, tick]; omega
    | false => simp [tcost, tick]; omega

example (n : Nat) (bs : List Bool) : trun n bs ≤ 2 * bs.length + n := by
  induction bs generalizing n with
    | nil => simp [trun]
    | cons b bs ih =>
      have h1 := tstep n b
      have h2 := ih (tick n b)
      simp only [trun, List.length_cons]
      omega

end M034Guide
