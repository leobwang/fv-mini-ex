/- Guide for H014 (BST delete).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
The entries work on this guide's own tree type `Bin α` and predicate `Good`, NOT the exercise's.
Part W: worked combinations on those objects.
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace H014Guide

/-- The guide's tree: `tip` is empty, `fork l a r` has left subtree `l`, value `a`, right `r`. -/
inductive Bin (α : Type) where
  | tip
  | fork (l : Bin α) (a : α) (r : Bin α)

/-- Number of values in the tree (a structurally recursive function, like `mem` or `All`). -/
def size {α : Type} : Bin α → Nat
  | .tip => 0
  | .fork l _ r => size l + 1 + size r

/-- `Good Q t`: `Q` holds at every value. An inductive predicate (like `BST`): a proof of
`Good Q (.fork l a r)` can only be built by `Good.fork` from its three premises. -/
inductive Good {α : Type} (Q : α → Prop) : Bin α → Prop
  | tip : Good Q .tip
  | fork {l : Bin α} {a : α} {r : Bin α} : Q a → Good Q l → Good Q r → Good Q (.fork l a r)

/-! # Part R · Reference entries -/

/-! ## Part 1 · `all_iff`: induction, unfolding, rewriting with an IH -/

/-! ### R1. `induction t with` · goal → one goal per constructor; context gains the subtrees and
one induction hypothesis per recursive argument. `=> ?_` leaves that case open as a goal. -/
example {α : Type} (P : Bin α → Prop) (h0 : P .tip)
    (h1 : ∀ l a r, P l → P r → P (.fork l a r)) (t : Bin α) : P t := by
  induction t with
    | tip => ?_
    | fork l a r ihl ihr => ?_
  · exact h0
  · exact h1 l a r ihl ihr

/-! ### R2. `simp only [f]` · goal (or `at h`: hypothesis): `f` applied to a constructor → that
equation of `f`'s definition. `simp only [f]` uses only `f`'s defining equations. -/
example {α : Type} (l r : Bin α) (a : α) (P : Nat → Prop) (h : P (size l + 1 + size r)) :
    P (size (.fork l a r)) := by
  simp only [size]
  exact h

example {α : Type} (l r : Bin α) (a : α) (P : Nat → Prop) (h : P (size (.fork l a r))) :
    P (size l + 1 + size r) := by
  simp only [size] at h
  exact h

/-! ### R3. `simp only [e q]` with `e : Q → (A ↔ B)` · goal: every `A` → `B`
An induction hypothesis with a premise (`ihl : BST l → (… ↔ …)`) must get that premise first. -/
example (Q A B : Prop) (P : Prop → Prop) (e : Q → (A ↔ B)) (q : Q) (h : P B) : P A := by
  simp only [e q]
  exact h

/-! ### R4. `grind` · closes a goal that follows from the context by propositional logic,
equalities, and linear arithmetic over `Nat`, while treating other predicates as opaque atoms.
`omega` does only the arithmetic: it fails as soon as an atom such as `A y` matters. -/
example (A : Nat → Prop) (k x y : Nat) (hA : A y → k < y) (hx : x < k) : A y → y ≠ x := by
  grind

/-! ## Part 2 · `popMin_none`: case split without induction, `match` inside a hypothesis -/

/-! ### R5. `cases t with` · goal → one goal per constructor; no induction hypotheses -/
example {α : Type} (P : Bin α → Prop) (h0 : P .tip) (h1 : ∀ l a r, P (.fork l a r)) (t : Bin α) :
    P t := by
  cases t with
    | tip => ?_
    | fork l a r => ?_
  · exact h0
  · exact h1 l a r

/-! ### R6. `split at h` · `h : (match g z with …) = c` → one goal per `match` arm; each gets
`heq✝ : g z = <pattern>` and `h` with that arm's value. `x✝` is the matched value, unused.
(When the matched term is a plain variable `o`, `split` substitutes it instead: no `heq✝`.)
`‹_›` (E012) is the hypothesis of the type the slot expects: here the inaccessible `heq✝`. -/
example {γ α β : Type} (g : γ → Option α) (z : γ) (b c : β) (f : α → β) (G : Prop)
    (h : (match g z with | none => b | some a => f a) = c)
    (k0 : g z = none → b = c → G) (k1 : ∀ a, g z = some a → f a = c → G) : G := by
  split at h
  · exact k0 ‹_› h
  · exact k1 _ ‹_› h

/-! ### R7. `simp at h` with `h : none = some x` · closes the goal: `h` is `False` -/
example {α : Type} (x : α) (G : Prop) (h : none = some x) : G := by
  simp at h

/-! ## Part 3 · `popMin_spec`: generalized induction, inverting `BST`, destructuring -/

/-! ### R8. `induction t generalizing b with` · as R1, but `b` (and hypotheses about it) leave the
context first, so each IH is `∀ b, …`: usable at a different `b` than the goal's.
Hypotheses that mention `t` (here `hb`) are generalized automatically. -/
example {α β : Type} (f : Bin α → Option β) (Q : Bin α → β → Prop)
    (H0 : ∀ b, f .tip = some b → Q .tip b)
    (H1 : ∀ l a r, (∀ b, f l = some b → Q l b) → (∀ b, f r = some b → Q r b) →
      ∀ b, f (.fork l a r) = some b → Q (.fork l a r) b)
    (t : Bin α) (b : β) (hb : f t = some b) : Q t b := by
  induction t generalizing b with
    | tip => ?_
    | fork l a r ihl ihr => ?_
  · exact H0 b hb
  · exact H1 l a r ihl ihr b hb

/-! ### R9. `cases h with | fork hq gl gr => ?_` · context: a proof `h` of an inductive predicate
→ the premises of the only constructor that can have built it (impossible constructors vanish) -/
example {α : Type} (Q : α → Prop) (l r : Bin α) (a : α) (G : Prop)
    (h : Good Q (.fork l a r)) (k : Q a → Good Q l → Good Q r → G) : G := by
  cases h with
    | fork hq gl gr => ?_
  exact k hq gl gr

/-! ### R10. `rw [e] at h₁ h₂` / `rw [e] at h ⊢` with `e : ∀ x, A x ↔ B x` · context (and goal):
`A …` → `B …` in each listed place; `e`'s arguments are found separately in each place -/
example {α : Type} (A B : α → Prop) (e : ∀ x, A x ↔ B x) (a b : α) (h1 : A a) (h2 : A b) (G : Prop)
    (k : B a → B b → G) : G := by
  rw [e] at h1 h2
  exact k h1 h2

example {α : Type} (A B : α → Prop) (e : ∀ x, A x ↔ B x) (a b : α) (h : A a) (k : B a → B b) :
    A b := by
  rw [e] at h ⊢
  exact k h

/-! ### R11. `rename_i x y` · context: the LAST inaccessible names (`a✝`, `heq✝`) get names -/
example (A B G : Prop) (k : A → B → G) : A → B → G := by
  intro _ _
  rename_i ha hb
  exact k ha hb

/-! ### R12. `obtain rfl := h` with `h : t = c` (`t` a local variable) · context: `t` is replaced
by `c` everywhere and disappears. `h` may be a lemma application (`lemma t hn`). -/
example {α : Type} (t : Bin α) (P : Bin α → Prop) (h : t = .tip) (h0 : P .tip) : P t := by
  obtain rfl := h
  exact h0

/-! ### R13. `simp at h` with `h : some (a, b) = some (c, d)` · context: `h` → `a = c ∧ b = d`
(`some` and `(·, ·)` are injective) -/
example {α β : Type} (a c : α) (b d : β) (G : Prop) (h : some (a, b) = some (c, d))
    (k : a = c ∧ b = d → G) : G := by
  simp at h
  exact k h

/-! ### R14. `obtain ⟨rfl, rfl⟩ := h` with `h : a = c ∧ e = t` · context: both equations are
substituted (`c := a`, then `t := e`): the variables `c`, `t` disappear -/
example {α : Type} (a c : α) (s t : Bin α) (P : α → Bin α → Prop)
    (h : a = c ∧ Bin.fork s a s = t) (hp : P a (Bin.fork s a s)) : P c t := by
  obtain ⟨rfl, rfl⟩ := h
  exact hp

/-! ### R15. `e.1`, `e.2` and `.inl`, `.inr` · `e.2 : B → A` for `e : A ↔ B` (`e.1 : A → B`);
for `e : A ∧ B`, `e.1 : A`. `.inl ha : A ∨ B`, `.inr hb : A ∨ B`. -/
example {α : Type} (A B C : α → Prop) (e : ∀ x, A x ↔ B x ∨ C x) (x : α) (hc : C x) : A x := by
  refine (e x).2 ?_
  exact .inr hc

/-! ### R16. `obtain ⟨h₁, h₂, h₃⟩ := e` with `e : A ∧ B ∧ C` · context gains three facts.
`e` may be a lemma application; `_` drops a piece. -/
example (Q A B C G : Prop) (e : Q → A ∧ B ∧ C) (q : Q) (k : A → B → C → G) : G := by
  obtain ⟨ha, hb, hc⟩ := e q
  exact k ha hb hc

/-! ### R17. `refine .fork ?_ gl gr` · goal: an inductive predicate → the premises of one
constructor; each `?_` becomes a goal, the others are given now -/
example {α : Type} (Q : α → Prop) (l r : Bin α) (a : α) (gl : Good Q l) (gr : Good Q r) (hq : Q a) :
    Good Q (.fork l a r) := by
  refine .fork ?_ gl gr
  exact hq

/-! ### R18. `intro y hy` · goal `∀ y, A y → B y` → context gains `y`, `hy : A y`; goal `B y` -/
example {α : Type} (A B : α → Prop) (k : ∀ y, A y → B y) : ∀ y, A y → B y := by
  intro y hy
  exact k y hy

/-! ### R19. `rcases h with h | rfl | h` with `h : A ∨ y = c ∨ B` · goal list: three goals; in
the middle one `y` is replaced by `c` -/
example {α : Type} (A B Q : α → Prop) (c y : α) (h : A y ∨ y = c ∨ B y)
    (ka : A y → Q y) (kc : Q c) (kb : B y → Q y) : Q y := by
  rcases h with h | rfl | h
  · exact ka h
  · exact kc
  · exact kb h

/-! ### R20. `Nat.lt_trans` · `n < m → m < k → n < k` · closes `⊢ n < k` -/
example (n m k : Nat) (h₁ : n < m) (h₂ : m < k) : n < k := by
  exact Nat.lt_trans h₁ h₂

/-! ## Part 4 · `mem_delete`: `if` and `match` in the goal (Part 5 adds no new entry) -/

/-! ### R21. `have := e` · context gains `this : T` (an older `this` becomes `this✝`).
`grind` instantiates `∀` facts by itself when a matching term occurs in the goal; an explicit
instance (`have := hl y`) shows in the infoview what it gets, and helps when it gives up. -/
example (A B : Nat → Prop) (hA : ∀ y, A y → B y) (y : Nat) (k : (A y → B y) → B 0) : B 0 := by
  have := hA y
  exact k this

/-! ### R22. `split` on `if c then x else y` in the goal · goal list: `h✝ : c ⊢ P x` and
`h✝ : ¬c ⊢ P y`. A nested `if` in the `else` branch needs a second `split`. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hx : P x) (hy : P y) :
    P (if c then x else y) := by
  split
  · exact hx
  · exact hy

/-! ### R23. `split` on `match g z with …` in the goal · goal list: one goal per arm, each with
`heq✝ : g z = <pattern>`; name the pattern variables and `heq✝` with `rename_i` (R11) -/
example {γ α β : Type} (g : γ → Option α) (z : γ) (b : β) (f : α → β) (P : β → Prop) (hb : P b)
    (hf : ∀ a, P (f a)) : P (match g z with | none => b | some a => f a) := by
  split
  · exact hb
  · exact hf _

/-! ### R24. `simp only [f, e] at *` · goal AND every hypothesis rewritten at once -/
example {α : Type} (l r : Bin α) (a : α) (n : Nat) (h : size (.fork l a r) = n) (P : Nat → Prop)
    (hp : P (size l + 1 + size r)) : P n := by
  simp only [size] at *
  rw [← h]
  exact hp

/-! # Part W · Worked combinations (the guide's `Bin`, `Good`, `size`; not the exercise's objects) -/

/-! ### W1. Induction + inversion + constructor: R1, R9, R17 -/
example {α : Type} (Q Q' : α → Prop) (hQ : ∀ a, Q a → Q' a) (t : Bin α) (h : Good Q t) :
    Good Q' t := by
  induction t with
    | tip => exact .tip
    | fork l a r ihl ihr =>
      cases h with
        | fork hq gl gr => exact .fork (hQ a hq) (ihl gl) (ihr gr)

/-! ### W2. A `match` in a hypothesis: R6, R11, then R7/R13-style `simp at h` -/
example (g : Nat → Option Nat) (z n : Nat)
    (h : (match g z with | none => 0 | some m => m + 1) = n + 1) : g z = some n := by
  split at h
  · simp at h
  · rename_i m hm
    simp at h
    rw [hm, h]

/-! ### W3. `∀` facts as `grind` input: the instances at `y` (R21), then R4. `R y` rules out
`y = x` only through `hR y` and `x < k`. -/
example (L R : Nat → Prop) (k x y : Nat) (hL : ∀ z, L z → z < k) (hR : ∀ z, R z → k < z)
    (hx : x < k) : (L y ∨ y = k ∨ R y) ∧ y ≠ x ↔ (L y ∧ y ≠ x) ∨ y = k ∨ R y := by
  have := hL y
  have := hR y
  grind

/-! ### W4. Distributing `∀` over `∨`: `grind` handles the quantifier bookkeeping -/
example (L R p : Nat → Prop) :
    ((∀ y, L y → p y) ∧ ∀ y, R y → p y) ↔ ∀ y, L y ∨ R y → p y := by
  grind

end H014Guide
