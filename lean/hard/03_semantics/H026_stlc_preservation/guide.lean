/- Guide for H026 (STLC progress and preservation with de Bruijn substitutions).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `Q` stand for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a toy language (`Expr`, scopes `Nat → Bool`, the judgement `Ok`), NOT the
exercise's `Tm`, `Ctx`, `HasType`.
Part W: worked combinations on the same toy objects.
Assumed: Lean basics (E001–E033) and de Bruijn indices (M048).
-/

namespace H026Guide

/-! # Toy objects (not the exercise's) -/

/-- Toy syntax: a leaf names a de Bruijn index; `bind` opens one new index `0` for its body. -/
inductive Expr where
  | leaf (n : Nat)
  | pair (a b : Expr)
  | bind (a : Expr)

/-- A scope says which indices may occur. `ext s` opens a new index `0` and shifts the old ones up. -/
def ext (s : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => s n

/-- `Ok s e`: every leaf of `e` is in scope `s`. A proof of `Ok s e` is a tree of these three rules. -/
inductive Ok : (Nat → Bool) → Expr → Prop
  | leaf {s : Nat → Bool} {n : Nat} : s n = true → Ok s (.leaf n)
  | pair {s : Nat → Bool} {a b : Expr} : Ok s a → Ok s b → Ok s (.pair a b)
  | bind {s : Nat → Bool} {a : Expr} : Ok (ext s) a → Ok s (.bind a)

/-- A predicate with a single rule, like a "value" predicate. -/
inductive IsBind : Expr → Prop
  | bind {a : Expr} : IsBind (.bind a)

/-! # Part R · Reference entries -/

/-! ## Induction on a derivation and building derivations -/

/-! ### R1. `induction h generalizing s'` · goal list: one goal per rule of `Ok`, with an IH
for every premise of that rule; the IH is `∀ {s'}`, so it can be used at a different `s'`.
`induction h generalizing s' with | leaf hn => … | pair _ _ iha ihb => … | bind _ ih => …` names the
`✝` hypotheses: first the rule's premises, then one IH per premise that is itself an `Ok` (W1). -/
example {s s' : Nat → Bool} {e : Expr} (P : (Nat → Bool) → Expr → Prop)
    (hs : ∀ n, s n = true → s' n = true) (h : Ok s e) (k : ∀ s₂ e₂, P s₂ e₂) : P s' e := by
  induction h generalizing s'
  all_goals exact k _ _

/-! ### R2. A rule is a function: `exact .leaf hn` · closes the goal
`.leaf` means `Ok.leaf`: Lean reads the namespace off the goal's head `Ok`. -/
example {s : Nat → Bool} {n : Nat} (hn : s n = true) : Ok s (.leaf n) := by
  exact .leaf hn

/-! ### R3. `refine .bind (ih ?_)` · goal: the conclusion of a rule → the premise of the IH -/
example {s s' : Nat → Bool} {a : Expr}
    (ih : ∀ {s₂ : Nat → Bool}, (∀ n, ext s n = true → s₂ n = true) → Ok s₂ a)
    (k : ∀ n, ext s n = true → ext s' n = true) : Ok s' (.bind a) := by
  refine .bind (ih ?_)
  exact k

/-! ## Lifting a hypothesis under a binder -/

/-! ### R4. `cases n` · goal list: index `0` and index `n + 1` -/
example (P : Nat → Prop) (k0 : P 0) (k1 : ∀ m, P (m + 1)) (n : Nat) : P n := by
  cases n
  exact k0
  exact k1 _

/-! ### R5. Definitions compute: `ext s (n + 1)` is `s n` by definition · goal (`show`), or none
`exact` sees through this by itself; `show` only makes the computed form visible. -/
example (s s' : Nat → Bool) (n : Nat) (k : s n = true → s' n = true) (hn : ext s (n + 1) = true) :
    ext s' (n + 1) = true := by
  show s' n = true
  exact k hn

/-! ### R6. Named argument `(f := Nat.succ)` · fixes an implicit argument Lean cannot guess
With `f` fixed, `fun _ h => h` type-checks because `ext s (Nat.succ n)` computes to `s n` (R5). -/
example (s : Nat → Bool) (e : Expr) (Q : (Nat → Bool) → Expr → Prop)
    (L : ∀ {s₁ s₂ : Nat → Bool} {f : Nat → Nat}, (∀ n, s₁ n = true → s₂ (f n) = true) → Q s₂ e) :
    Q (ext s) e := by
  exact L (f := Nat.succ) (fun _ h => h)

/-! ## Inversion: taking a hypothesis apart -/

/-! ### R7. `cases hv` on a one-rule predicate · context: `e` is replaced by the rule's shape -/
example {e : Expr} (P : Expr → Prop) (k : ∀ a, P (.bind a)) (hv : IsBind e) : P e := by
  cases hv
  exact k _

/-! ### R8. `cases h` with `h : Ok s (.pair a b)` · context: `h` → the premises of the only rule
that can produce `.pair`; the rules for `.leaf` and `.bind` are dropped -/
example {s : Nat → Bool} {a b : Expr} (P : Prop) (k : Ok s a → Ok s b → P) (h : Ok s (.pair a b)) :
    P := by
  cases h
  exact k (by assumption) (by assumption)

/-! ### R9. `cases hn` with `hn : some a = some b` · context: `b` is replaced by `a` everywhere -/
example {α : Type} (a b : α) (P : α → α → Prop) (k : P a a) (hn : some a = some b) : P a b := by
  cases hn
  exact k

/-! ## Induction with a fixed index -/

/-! ### R10. `generalize hs : e₀ = s at h` · context: the expression `e₀` in `h` → a new variable `s`,
plus the equation `hs` -/
example {e : Expr} (P : Prop) (h : Ok (fun _ => false) e)
    (k : ∀ s, (fun _ => false) = s → Ok s e → P) : P := by
  generalize hs : (fun _ => false : Nat → Bool) = s at h
  exact k s hs h

/-! ### R11. `induction h` after R10 · goal list: the equation becomes a premise of every IH -/
example {s : Nat → Bool} {e : Expr} (P : Expr → Prop) (k : ∀ e₂, P e₂)
    (hs : (fun _ => false) = s) (h : Ok s e) : P e := by
  induction h
  all_goals exact k _

/-! ### R12. `subst hs` with `hs : e₀ = s` (`s` a variable) · context: `s` → `e₀` everywhere -/
example {s : Nat → Bool} {n : Nat} (G : Prop) (k : (fun _ => false) n = true → G)
    (hs : (fun _ => false) = s) (hn : s n = true) : G := by
  subst hs
  exact k hn

/-! ### R13. `cases hn` with `hn : none = some a` · goal list: closes the goal
(two different constructors are never equal). It also works when `hn` only computes to that. -/
example {α : Type} (a : α) (n : Nat) (G : Prop) (hn : (fun _ => none : Nat → Option α) n = some a) :
    G := by
  cases hn

/-! ### R14. `obtain ⟨a, rfl⟩ := hv` with `hv : ∃ a, e = .bind a` · context: `e` → `.bind a` -/
example {e : Expr} (P : Expr → Prop) (k : ∀ a, P (.bind a)) (hv : ∃ a, e = .bind a) : P e := by
  obtain ⟨a, rfl⟩ := hv
  exact k a

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. Widening the scope: R1, R2, R3, `intro`, R4, R5 -/
theorem Ok.mono {s s' : Nat → Bool} (hs : ∀ n, s n = true → s' n = true) {e : Expr}
    (h : Ok s e) : Ok s' e := by
  induction h generalizing s' with
    | leaf hn => exact .leaf (hs _ hn)
    | pair _ _ iha ihb => exact .pair (iha hs) (ihb hs)
    | bind _ ih =>
      refine .bind (ih ?_)
      intro n hn
      cases n with
        | zero => exact hn
        | succ n => exact hs n hn

/-! ### W2. An empty scope: R10, R11, R12, R13 -/
def leftmost : Expr → Expr
  | .pair a _ => leftmost a
  | e => e

example {e : Expr} (h : Ok (fun _ => false) e) : IsBind (leftmost e) := by
  generalize hs : (fun _ => false : Nat → Bool) = s at h
  induction h with
    | leaf hn => subst hs; cases hn
    | pair _ _ ih1 _ => exact ih1 hs
    | bind _ => exact .bind

end H026Guide
