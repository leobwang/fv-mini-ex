/- Guide for M050 (A fuel-based interpreter is complete).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a toy `Task` language run by
`go`, and a toy derivation predicate `Gen`).
Assumed: Lean basics (E001–E033). Core Lean only: no Mathlib.
-/

namespace M050Guide

/-! ## Toy objects used by the entries (not the exercise's)

`Gen n`: the number `n` is generated from `0` by adding `2`, or by adding two generated numbers.
A proof of `Gen n` is a *derivation*: a tree of constructor applications. -/
inductive Gen : Nat → Prop
  | zero : Gen 0
  | add2 {n : Nat} : Gen n → Gen (n + 2)
  | sum {m n : Nat} : Gen m → Gen n → Gen (m + n)

/-- A toy task language on one counter `x : Nat`. -/
inductive Task where
  | tick                                -- `x := x + 1`
  | pair (p q : Task)                   -- `p`, then `q`
  | guard (t : Nat → Bool) (p : Task)   -- `p` if `t x`, else stop with `x`
  | loop (t : Nat → Bool) (p : Task)    -- repeat `p` while `t x`

/-- `go k p x`: run task `p` from counter `x` with fuel `k`; `none` = out of fuel. Every
recursive call spends one unit of fuel. -/
def go : Nat → Task → Nat → Option Nat
  | 0, _, _ => none
  | _ + 1, .tick, x => some (x + 1)
  | k + 1, .pair p q, x =>
    match go k p x with
    | some y => go k q y
    | none => none
  | k + 1, .guard t p, x => if t x then go k p x else some x
  | k + 1, .loop t p, x =>
    if t x then
      match go k p x with
      | some y => go k (.loop t p) y
      | none => none
    else some x

/-! # Part R · Reference entries -/

/-! ## Induction on a number, with a hypothesis that mentions it -/

/-! ### R1. `induction m` (cases `zero`, `succ`) · goal list: one goal per case; a hypothesis
`hnm` that mentions `m` is carried along, so the IH gets it as a premise `n ≤ k → …`.
`induction m with | zero => tac₀ | succ k ih => tac₁` does the same and names `k ih` at once. -/
example (n m : Nat) (Q : Nat → Prop) (h0 : n ≤ 0 → Q 0)
    (hs : ∀ k, (n ≤ k → Q k) → n ≤ k + 1 → Q (k + 1)) (hnm : n ≤ m) : Q m := by
  induction m
  case zero => exact h0 hnm
  case succ k ih => exact hs k ih hnm

/-! ### R2. `omega` · closes a goal of linear arithmetic over `Nat`/`Int` (`+`, `-`, `*` by a
numeral, `≤`, `<`, `=`, `max`, `min`), using the hypotheses in the context -/
example (a b : Nat) (hle : a ≤ b + 1) (hge : a ≥ b + 1) : a = b + 1 := by
  omega

/-! ### R3. `subst e` · context: `e : a = t` (with `a` a variable) is used up; `a` is replaced by
`t` in the goal and in every hypothesis -/
example (a b : Nat) (P : Nat → Prop) (e : a = b + 1) (h : P (b + 1)) : P a := by
  subst e
  exact h

/-! ### R4. `rcases Nat.lt_or_ge a b with hlt | hge` · goal list: two goals, one with `hlt : a < b`,
one with `hge : a ≥ b`. The lemma is `Nat.lt_or_ge : ∀ (n m : Nat), n < m ∨ n ≥ m`. -/
example (a b : Nat) (G : Prop) (g1 : a < b → G) (g2 : a ≥ b → G) : G := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact g1 hlt
  · exact g2 hge

/-! ### R5. `exact thm _ _ (ih (by omega))` · closes the goal by applying a theorem. Each `_` is an
explicit argument Lean reads off the goal; `(by omega)` proves the IH's premise on the spot. -/
example {α : Type} (Q : Nat → α → Prop) (mono : ∀ (k : Nat) (x : α), Q k x → Q (k + 1) x)
    (k : Nat) (x : α) (ih : 1 ≤ k → Q k x) (hk : 2 ≤ k) : Q (k + 1) x := by
  exact mono _ _ (ih (by omega))

/-! ## Induction on a derivation -/

/-! ### R6. `induction h` for `h : Gen n` · goal list: one goal per constructor of `Gen`. The
constructor's implicit arguments arrive as `n✝`, its premises as `a✝`, and one IH `a_ih✝` per
premise of the predicate's own type. With `induction h with | add2 hk ih => …` you name the explicit
premises and IHs yourself (`case add2 k hk ih` below names `n✝ a✝ a_ih✝` afterwards). -/
example (P : Nat → Prop) (n : Nat) (h : Gen n) (h0 : P 0) (h2 : ∀ k, P k → P (k + 2))
    (hs : ∀ a b, P a → P b → P (a + b)) : P n := by
  induction h
  case zero => exact h0
  case add2 k hk ih => exact h2 k ih
  case sum a b ha hb iha ihb => exact hs a b iha ihb

/-! ## Existentials -/

/-! ### R7. `exact ⟨1, rfl⟩` · closes `∃ k, go k p x = v` when `go 1 p x` computes to `v`:
`rfl` accepts any two sides that are equal by unfolding definitions -/
example (x : Nat) : ∃ k, go k .tick x = some (x + 1) := by
  exact ⟨1, rfl⟩

/-! ### R8. `obtain ⟨n, hn⟩ := ih` · context: `ih : ∃ n, Q n` is replaced by a witness `n` and
`hn : Q n` -/
example (Q : Nat → Prop) (G : Prop) (ih : ∃ n, Q n) (g : ∀ n, Q n → G) : G := by
  obtain ⟨n, hn⟩ := ih
  exact g n hn

/-! ## Running a fuel interpreter one step -/

/-! ### R9. `simp only [go]` · goal: `go (k + 1) (p.pair q) x` → the body of that equation, a
`match` on the first sub-run. It fires only when the fuel has the literal form `k + 1`. -/
example (k x : Nat) (p q : Task) (P : Option Nat → Prop)
    (h : P (match go k p x with | some y => go k q y | none => none)) :
    P (go (k + 1) (p.pair q) x) := by
  simp only [go]
  exact h

/-! ### R10. `Nat.le_max_left`, `Nat.le_max_right` · `a ≤ max a b`, `b ≤ max a b` -/
example (a b : Nat) (P : Prop) (g : a ≤ max a b → b ≤ max a b → P) : P := by
  exact g (Nat.le_max_left a b) (Nat.le_max_right a b)

/-! ### R11. `rw [lift hle ha]` · goal: rewrite with a lemma whose premises you supply.
`lift (Nat.le_max_left _ _) ha : g (max a ?b) = some v`; `rw` finds `g (max a b)` and fixes `?b := b`.
Inside a `match`, the scrutinee becomes `some v`. -/
example {α : Type} (g : Nat → Option α)
    (lift : ∀ {k m : Nat} {v : α}, k ≤ m → g k = some v → g m = some v)
    (a b : Nat) (v : α) (ha : g a = some v) (P : Option α → Prop) (h : P (some v)) :
    P (g (max a b)) := by
  rw [lift (Nat.le_max_left _ _) ha]
  exact h

/-! ### R12. `exact e` · closes the goal when `e`'s type equals it up to computation:
`match some v with | some y => F y | none => none` computes to `F v`, so no rewrite is needed -/
example {α β : Type} (v : α) (F : α → Option β) (w : Option β) (h : F v = w) :
    (match some v with | some y => F y | none => none) = w := by
  exact h

/-! ### R13. `simp only [hb, if_true]` · goal: `if c then a else b` with `hb : c = true` → `a`.
A `Bool` condition prints as `c = true`; `hb` turns it into `true = true`, and `simp` reduces that
`if` to its `then` branch (`if_true : (if True then t else e) = t`). -/
example {α : Type} (c : Bool) (a b : α) (P : α → Prop) (hb : c = true) (h : P a) :
    P (if c then a else b) := by
  simp only [hb, if_true]
  exact h

/-! ### R14. `simp [go, hb, h]` · closes the goal: unfold `go`, rewrite with the hypotheses `hb`, `h`,
then finish with the default simp set -/
example (k x y : Nat) (t : Nat → Bool) (p : Task) (hb : t x = true) (h : go k p x = some y) :
    go (k + 1) (.guard t p) x = some y := by
  simp [go, hb, h]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. One step of `pair` with the same fuel for both halves: R9, `rw`, R12 -/
example (k x y z : Nat) (p q : Task) (hp : go k p x = some y) (hq : go k q y = some z) :
    go (k + 1) (p.pair q) x = some z := by
  simp only [go]
  rw [hp]
  exact hq

/-! ### W2. One step of `loop` when the test is true: R9 with R13 in one call, then `rw`, R12 -/
example (k x y z : Nat) (t : Nat → Bool) (p : Task) (ht : t x = true)
    (hp : go k p x = some y) (hl : go k (.loop t p) y = some z) :
    go (k + 1) (.loop t p) x = some z := by
  simp only [go, ht, if_true]
  rw [hp]
  exact hl

/-! ### W3. Induction on a derivation, one IH per premise, witnesses combined: R6, R8, R2 -/
example (n : Nat) (h : Gen n) : ∃ k, n = 2 * k := by
  induction h with
    | zero => exact ⟨0, rfl⟩
    | add2 _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, by omega⟩
    | sum _ _ ih1 ih2 =>
      obtain ⟨k1, hk1⟩ := ih1
      obtain ⟨k2, hk2⟩ := ih2
      exact ⟨k1 + k2, by omega⟩

end M050Guide
