/- Guide for H002 (Kripke semantics: excluded middle is not intuitionistic).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a tree type, a toy derivation
system `Gen`, a graph structure).
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace H002Guide

/-! ## Objects the entries use (unrelated to the exercise) -/

/-- Binary trees with numbers at the leaves. -/
inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)

/-- Four tags, read by the pattern-matching definition `Sem` below. -/
inductive Tag where
  | none
  | both
  | either
  | later

/-- A definition by pattern matching: each clause is the meaning of `Sem le p q t n` for one tag. -/
def Sem (le : Nat → Nat → Prop) (p q : Nat → Prop) : Tag → Nat → Prop
  | .none, _ => False
  | .both, n => p n ∧ q n
  | .either, n => p n ∨ q n
  | .later, n => ∀ m, le n m → p m → q m

/-- A structure: a carrier type and a symmetric relation on it. -/
structure Graph where
  V : Type
  adj : V → V → Prop
  symm : ∀ {u v : V}, adj u v → adj v u

/-- A toy derivation system: `Gen S n` says `n` is generated from the seed list `S`.
`push` adds an intermediate number `m` to the seeds; `m` does not occur in its conclusion. -/
inductive Gen : List Nat → Nat → Prop
  | seed {S : List Nat} {n : Nat} : n ∈ S → Gen S n
  | dbl {S : List Nat} {n : Nat} : Gen S n → Gen S (2 * n)
  | push {S : List Nat} {m n : Nat} : Gen (m :: S) n → Gen S m → Gen S n

/-! # Part R · Reference entries -/

/-! ## Induction on an inductive type, and definitions by pattern matching -/

/-! ### R1. `induction t generalizing k` · goal list: one goal per constructor, with IHs
`generalizing k` puts `∀ k` into each induction hypothesis, so the IH works for every `k`, not only
the one in the context. With `induction t generalizing k with | leaf n => … | node l r ihl ihr => …`
you name the fields and IHs; `case leaf n => …` does the same after a bare `induction`. -/
example (P : Tree → Nat → Prop) (hl : ∀ n k, P (.leaf n) k)
    (hn : ∀ l r, (∀ k, P l k) → (∀ k, P r k) → ∀ k, P (.node l r) k) (t : Tree) (k : Nat) :
    P t k := by
  induction t generalizing k
  case leaf n => exact hl n k
  case node l r ihl ihr => exact hn l r ihl ihr k

/-! ### R2. `show G'` · goal: a definition applied to a constructor → its defining clause
Lean unfolds `Sem … .both n` by itself (it is definitionally `p n ∧ q n`), so `exact`, `intro`,
`h.1`, `h.elim` and function application all work without `show`; `show` only makes it visible. -/
example (le : Nat → Nat → Prop) (p q : Nat → Prop) (n : Nat) (h : p n ∧ q n) :
    Sem le p q .both n := by
  show p n ∧ q n
  exact h

/-! ### R3. A structure field used as a lemma: `G.symm h` · closes the goal
`G.symm` has type `∀ {u v : G.V}, G.adj u v → G.adj v u`; the implicit `u v` are read off `h`. -/
example (G : Graph) (u v : G.V) (h : G.adj u v) : G.adj v u := by
  exact G.symm h

/-! ### R4. `h.elim (fun a => …) (fun b => …)` (`Or.elim`) · goal list: one goal per side of `h : A ∨ B`
`.inl x : A ∨ B` from `x : A`, and `.inr y : A ∨ B` from `y : B`. -/
example (A B C D : Prop) (f : A → C) (g : B → D) (h : A ∨ B) : C ∨ D := by
  refine h.elim (fun a => ?_) (fun b => ?_)
  exact .inl (f a)
  exact .inr (g b)

/-! ### R5. `intro m hm hp` on a definition that unfolds to `∀` · context gains `m hm hp` -/
example (le : Nat → Nat → Prop) (p q : Nat → Prop) (n : Nat) (h : ∀ m, p m → q m) :
    Sem le p q .later n := by
  intro m hm hp
  exact h m hp

/-! ## Lists -/

/-! ### R6. `intro x hx` on `∀ x ∈ l, Q x` · context gains `x` and `hx : x ∈ l`
`∀ x ∈ l, Q x` is notation for `∀ x, x ∈ l → Q x`. -/
example {α : Type} (l : List α) (Q : α → Prop) (h : ∀ x, x ∈ l → Q x) : ∀ x ∈ l, Q x := by
  intro x hx
  exact h x hx

/-! ### R7. `List.mem_cons` · `a ∈ b :: l ↔ a = b ∨ a ∈ l`; `.mp` uses it left to right -/
example {α : Type} (a b : α) (l : List α) (h : a ∈ b :: l) (G : Prop) (k : a = b ∨ a ∈ l → G) :
    G := by
  have h' := List.mem_cons.mp h
  exact k h'

/-! ### R8. `rcases h with rfl | h` · goal list: one goal per side; `rfl` substitutes the equation
`rcases h with h | h` splits `h : A ∨ B` the same way (both sides named `h`). In the `rfl` branch
`a = b` is used to replace one variable by the other everywhere. -/
example {α : Type} (a b : α) (l : List α) (P : α → Prop) (h : a = b ∨ a ∈ l) (hb : P b)
    (hl : ∀ x ∈ l, P x) : P a := by
  rcases h with rfl | h
  · exact hb
  · exact hl a h

/-! ## Building a structure value; negations -/

/-! ### R9. `let G : Graph := { V := …, adj := …, symm := … }` · context gains `G` with its value
A field of type `∀ {u v}, adj u v → …` is given as `fun h => …`: Lean adds the implicit `u v` itself. -/
example (P : Graph → Prop) (h : P { V := Bool, adj := fun a b => a = b, symm := fun h => h.symm }) :
    ∃ G : Graph, P G := by
  let G : Graph := { V := Bool, adj := fun a b => a = b, symm := fun h => h.symm }
  exact ⟨G, h⟩

/-! ### R10. `rintro (h | h)` on `¬(A ∨ B)` · goal list: two goals `False`, each with one side as `h`
`¬X` is `X → False`, so `rintro` introduces `X` and splits it at once. -/
example (A B : Prop) (na : ¬A) (nb : ¬B) : ¬(A ∨ B) := by
  rintro (h | h)
  · exact na h
  · exact nb h

/-! ### R11. `Bool.false_ne_true` · `false ≠ true`, i.e. `false = true → False` -/
example (h : false = true) : False := by
  exact Bool.false_ne_true h

/-! ### R12. Apply a hypothesis that unfolds to `∀`: `h m hm hp` · closes the goal
`h : Sem le p q .later n` is definitionally `∀ m, le n m → p m → q m`, so it is a function. -/
example (le : Nat → Nat → Prop) (p q : Nat → Prop) (n m : Nat) (h : Sem le p q .later n)
    (hm : le n m) (hp : p m) : q m := by
  exact h m hm hp

/-! ## Derivations: constructors of an inductive predicate -/

/-! ### R13. `refine .dbl ?_` · goal: a conclusion of the rule → its premise
`.dbl` is `Gen.dbl`: a leading dot looks the name up in the namespace of the goal's type. -/
example (S : List Nat) (n : Nat) (h : Gen S n) : Gen S (2 * n) := by
  refine .dbl ?_
  exact h

/-! ### R14. `refine .push (m := 3) ?_ ?_` · goal → two premises; `(m := …)` fixes the cut
`m` occurs only in the premises, so Lean cannot infer it from the goal; name it, or the premises
contain a metavariable `?m` that `by simp` cannot handle. -/
example (S : List Nat) (n : Nat) (h1 : Gen (3 :: S) n) (h2 : Gen S 3) : Gen S n := by
  refine .push (m := 3) ?_ ?_
  exact h1
  exact h2

/-! ### R15. `by simp` proves list membership `c ∈ [a, b, c]` (`List.mem_cons`, `List.mem_singleton`) -/
example {α : Type} (a b c : α) : c ∈ [a, b, c] := by simp

/-! ## Induction on a derivation -/

/-! ### R16. `induction h generalizing k` on `h : Gen S n` · goal list: one goal per rule
Each goal replaces `S n` by the rule's conclusion and has one IH per premise. Implicit fields
(`{S} {n} {m}`) are not named in `| seed hn => …`; only explicit premises and IHs are, in that order:
`| push h1 h2 ih1 ih2 => …`. -/
example (P : List Nat → Nat → Nat → Prop) (hs : ∀ S n k, n ∈ S → P S n k)
    (hd : ∀ S n, (∀ k, P S n k) → ∀ k, P S (2 * n) k)
    (hp : ∀ S m n, (∀ k, P (m :: S) n k) → (∀ k, P S m k) → ∀ k, P S n k)
    (S : List Nat) (n : Nat) (h : Gen S n) (k : Nat) : P S n k := by
  induction h generalizing k
  case seed hn => exact hs _ _ k hn
  case dbl ih => exact hd _ _ ih k
  case push ih1 ih2 => exact hp _ _ _ ih1 ih2 k

/-! ### R17. `h.elim` (`False.elim`) · closes any goal from `h : False`
It also works on `h : Sem le p q .none n`, which unfolds to `False`. -/
example (le : Nat → Nat → Prop) (p q : Nat → Prop) (n : Nat) (G : Prop) (h : Sem le p q .none n) :
    G := by
  exact h.elim

/-! ## Using an existence statement -/

/-! ### R18. `obtain ⟨x, y, hxy⟩ := h` · context: `h : ∃ x y, R x y` → `x`, `y`, `hxy : R x y` -/
example {α : Type} (R : α → α → Prop) (h : ∃ x y, R x y) (G : Prop) (k : ∀ x y, R x y → G) :
    G := by
  obtain ⟨x, y, hxy⟩ := h
  exact k x y hxy

/-! ### R19. `by simp` proves `∀ x ∈ [], Q x` (`List.not_mem_nil`: nothing is in `[]`) -/
example {α : Type} (Q : α → Prop) : ∀ x ∈ ([] : List α), Q x := by simp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A derivation as one term: R13, R14, R15
The goal says `2 * 2`, not `4`: `.dbl` concludes `Gen S (2 * n)`, and Lean does not solve `2 * ?n = 4`. -/
example : Gen [1] (2 * 2) :=
  .push (m := 2 * 1) (.dbl (.seed (by simp))) (.dbl (.seed (by simp)))

/-! ### W2. Induction on a derivation, carrying a property of the seeds: R16, R6, R7, R8
The `with` form names only explicit premises and IHs. `omega` (core) proves linear facts over `Nat`. -/
example (S : List Nat) (n : Nat) (h : Gen S n) : (∀ x ∈ S, 0 < x) → 0 < n := by
  induction h with
    | seed hn => exact fun hS => hS _ hn
    | dbl _ ih => exact fun hS => by have := ih hS; omega
    | push _ _ ih1 ih2 =>
      intro hS
      apply ih1
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ih2 hS
      · exact hS x hx

/-! ### W3. A concrete structure as a counterexample: R9, R10, R11 -/
example : ∃ (G : Graph) (u v : G.V), ¬(G.adj u v ∨ G.adj v u) := by
  let G : Graph := { V := Bool, adj := fun a b => a = b, symm := fun h => h.symm }
  refine ⟨G, false, true, ?_⟩
  rintro (h | h)
  · exact Bool.false_ne_true h
  · exact Bool.false_ne_true h.symm

end H002Guide
