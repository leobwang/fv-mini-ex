/- Guide for H009 (Intrinsically typed terms and a type checker).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G` is a
goal the step does not touch. A hypothesis `h` in an entry is only there to finish the example.
The objects here are NOT the exercise's: a two-kind family `Tm : K → Type`, a partial function
`step : Nat → Option Nat` with a `match` on a recursive call, and an arbitrary family `F : ι → Type`.
Part W: worked combinations on those objects.
Assumed: Lean basics (E001–E033). Core Lean only: no imports.
-/

namespace H009Guide

/-! # Guide-local objects -/

/-- Two kinds. -/
inductive K where
  | a
  | b
  deriving DecidableEq

/-- An indexed family: `Tm k` holds only trees of kind `k` (`pair` keeps the kind). -/
inductive Tm : K → Type where
  | atom (n : Nat) : Tm .a
  | flag : Tm .b
  | pair {k : K} (l r : Tm k) : Tm k

/-- Number of leaves. -/
def Tm.leaves : {k : K} → Tm k → Nat
  | _, .atom _ => 1
  | _, .flag => 1
  | _, .pair l r => l.leaves + r.leaves

/-- A partial function whose second clause matches on a recursive call (like a checker). -/
def step : Nat → Option Nat
  | 0 => some 0
  | n + 1 =>
    match step n with
    | some m => some (m + 1)
    | none => none

/-! # Part R · Reference entries -/

/-! ## Induction on an indexed family -/

/-! ### R1. `induction e with | c x ih => …` · goal list: one goal per constructor, index specialised
Each `| c x y ihx ihy => ?_` names the constructor's fields and their induction hypotheses. `?_` leaves
the case open here so you can see it; in a proof you write the case's tactics after `=>`. -/
example (P : {k : K} → Tm k → Prop) (h1 : ∀ n, P (Tm.atom n)) (h2 : P Tm.flag)
    (h3 : ∀ {k : K} (l r : Tm k), P l → P r → P (Tm.pair l r)) {k : K} (e : Tm k) : P e := by
  induction e with | atom n => ?_ | flag => ?_ | pair l r ihl ihr => ?_
  · exact h1 n
  · exact h2
  · exact h3 l r ihl ihr

/-! ## Unfolding a definition and splitting its `match` -/

/-! ### R2. `simp only [f]` (equation lemmas of `f`) · goal: `f (constructor …)` → that clause's body -/
example (n : Nat) (P : Option Nat → Prop)
    (h : P (match step n with | some m => some (m + 1) | none => none)) : P (step (n + 1)) := by
  simp only [step]
  exact h

/-! ### R3. `split` · goal list: one goal per arm of the first `match` in the goal
Each arm's goal gets `heq✝ : discriminant = pattern` (inaccessible: name it with R9). -/
example (n : Nat) (P : Option Nat → Prop) (h1 : ∀ m, P (some (m + 1))) (h2 : P none) :
    P (match step n with | some m => some (m + 1) | none => none) := by
  split
  · exact h1 _
  · exact h2

/-! ### R4. `simp_all [d]` · simplifies every hypothesis with the others and the goal with all of them -/
example {α β : Type} (f : α → β) (g : α → α) (a c : α) (P : β → Prop)
    (ih : f (g a) = f a) (heq : g a = c) (hP : P (f c)) : P (f a) := by
  simp_all

/-! ### R5. `simp only [ih]` with `ih : x = some a` · goal: `match x with …` → the `some` arm
Once the discriminant is a constructor, `simp` picks the arm by itself. -/
example (n m : Nat) (ih : step n = some m) (P : Option Nat → Prop) (h : P (some (m + 1))) :
    P (match step n with | some m => some (m + 1) | none => none) := by
  simp only [ih]
  exact h

/-! ### R6. `simp` on `if h : t = t then x else y` · goal: the condition is proved by `rfl`, `x` stays -/
example {α β : Type} [DecidableEq α] (t : α) (x y : β) (P : β → Prop) (h : P x) :
    P (if _h : t = t then x else y) := by
  simp
  exact h

/-! ## Inverting a hypothesis `f u = some r` -/

/-! ### R7. `simp only [f] at h` · context: `h` is unfolded, goal unchanged -/
example (n k : Nat) (G : Prop) (hG : (match step n with | some m => some (m + 1) | none => none) = some k → G)
    (h : step (n + 1) = some k) : G := by
  simp only [step] at h
  exact hG h

/-! ### R8. `split at h` · goal list: one goal per arm of the first `match`/`if` in `h`
`next a b => tac` works on the first goal and names its inaccessible hypotheses `a b` (like R9). -/
example (n k : Nat) (G : Prop) (h1 : ∀ m, step n = some m → some (m + 1) = some k → G)
    (h2 : step n = none → none = some k → G)
    (h : (match step n with | some m => some (m + 1) | none => none) = some k) : G := by
  split at h
  next m hm => exact h1 m hm h
  next hm => exact h2 hm h

/-! The same on a dependent `if h : t₁ = t₂ then … else …` (`dite`): cases `isTrue` / `isFalse`. -/
example {α β : Type} [DecidableEq α] (t₁ t₂ : α) (x : t₁ = t₂ → β) (y z : β) (G : Prop)
    (k1 : ∀ e : t₁ = t₂, x e = z → G) (k2 : y = z → G)
    (h : (if e : t₁ = t₂ then x e else y) = z) : G := by
  split at h
  next e => exact k1 e h
  next => exact k2 h

/-! ### R9. `rename_i x hx` · context: the last inaccessible names (`a✝`, `heq✝`) become `x hx` -/
example (P : Nat → Prop) (hp : ∀ n, n = 0 → P n) : ∀ (n : Nat), n = 0 → P n := by
  intro _ _
  rename_i n hn
  exact hp n hn

/-! ### R10. `Option.some.inj` · `some a = some b → a = b`; `.symm` flips an equation -/
example {α : Type} (a b : α) (h : some a = some b) : b = a := by
  have h' := Option.some.inj h
  exact h'.symm

/-! ### R11. `simp at h` with `h : none = some a` · goal closed: `h` simplifies to `False` -/
example {α : Type} (a : α) (G : Prop) (h : none = some a) : G := by
  simp at h

/-! ## Σ-types, casts and `≍` -/

/-! ### R12. `subst h` with `h : i = j`, `j` a variable · context: `j` replaced by `i` everywhere -/
example {ι : Type} {F : ι → Type} (i j : ι) (y : F j) (h : i = j)
    (P : (k : ι) → F k → Prop) (hp : ∀ z : F i, P i z) : P j y := by
  subst h
  exact hp y

/-! ### R13. `h ▸ x` with `h : i = i` · goal: `simp` drops the cast (`⋯ ▸ x` → `x`) -/
example {ι : Type} {F : ι → Type} (i : ι) (h : i = i) (x : F i) (P : F i → Prop) (hp : P x) :
    P (h ▸ x) := by
  simp
  exact hp

/-! ### R14. `simp at h` on `some ⟨i, x⟩ = some ⟨j, y⟩` (`Option.some.injEq`, `Sigma.mk.inj_iff`)
· context: `h : i = j ∧ x ≍ y` -/
example {ι : Type} {F : ι → Type} (i j : ι) (x : F i) (y : F j) (G : Prop)
    (hk : i = j → HEq x y → G) (h : (some ⟨i, x⟩ : Option (Σ k, F k)) = some ⟨j, y⟩) : G := by
  simp at h
  exact hk h.1 h.2

/-! ### R15. `obtain ⟨rfl, h⟩ := h` · context: the `∧` is split and the equation `i = j` substituted -/
example {ι : Type} {F : ι → Type} (i j : ι) (x : F i) (y : F j) (P : (k : ι) → F k → Prop)
    (hp : ∀ z : F i, HEq x z → P i z) (h : i = j ∧ HEq x y) : P j y := by
  obtain ⟨rfl, h⟩ := h
  exact hp y h

/-! ### R16. `cases h` with `h : x ≍ y`, both in `F i`, `y` a variable · context: `y` replaced by `x` -/
example {ι : Type} {F : ι → Type} (i : ι) (x y : F i) (P : F i → Prop) (hp : P x)
    (h : HEq x y) : P y := by
  cases h
  exact hp

/-! ## Induction with a generalised hypothesis, and using an inversion lemma -/

/-! ### R17. `induction n generalizing m with …` · goal list; the IH is `∀ m, …` instead of one fixed `m` -/
example (Q R : Nat → Nat → Prop) (h0 : ∀ m, Q 0 m → R 0 m)
    (hs : ∀ n, (∀ m, Q n m → R n m) → ∀ m, Q (n + 1) m → R (n + 1) m)
    (n m : Nat) (h : Q n m) : R n m := by
  induction n generalizing m with | zero => ?_ | succ n ih => ?_
  · exact h0 m h
  · exact hs n ih m h

/-! ### R18. `obtain ⟨x, hx, hq⟩ := h` with `h : ∃ x, A x ∧ B x` · context: a witness and its facts -/
example {α : Type} (A B : α → Prop) (G : Prop) (hk : ∀ x, A x → B x → G) (h : ∃ x, A x ∧ B x) : G := by
  obtain ⟨x, hx, hq⟩ := h
  exact hk x hx hq

/-! ### R19. `cases h` with `h : (⟨i, x⟩ : Σ k, F k) = ⟨j, y⟩`, `i x` variables · context: both substituted -/
example {ι : Type} {F : ι → Type} (j : ι) (y : F j) (i : ι) (x : F i) (P : (k : ι) → F k → Prop)
    (hp : P j y) (h : (⟨i, x⟩ : Σ k, F k) = ⟨j, y⟩) : P i x := by
  cases h
  exact hp

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Induction + unfold + split + `simp_all`: R2 → R3 → R4 inside an induction -/
example (n : Nat) : step n = some n := by
  induction n with
    | zero => rfl
    | succ n ih =>
      simp only [step]
      split <;> simp_all

/-! ### W2. An inversion lemma for `step`: R7 → R8 → R9 → R10, impossible arm R11 -/
example (n k : Nat) (h : step (n + 1) = some k) : ∃ m, step n = some m ∧ k = m + 1 := by
  simp only [step] at h
  split at h
  · rename_i m hm
    exact ⟨m, hm, (Option.some.inj h).symm⟩
  · simp at h

/-! ### W3. A Σ-equation inside `some`: R14 → R15 → R16, then compute -/
example (n : Nat) (k : K) (e : Tm k)
    (h : (some ⟨.a, .atom n⟩ : Option (Σ k, Tm k)) = some ⟨k, e⟩) : e.leaves = 1 := by
  simp at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

end H009Guide
