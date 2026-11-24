/- Guide for H020 (Type safety).
Part R: one reference entry per tactic or proof-term move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `G` stand for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `k…` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a toy language defined below (`Kd`, `Ex`, `Ok`, `Done`, `Red`), NOT the
exercise's `Ty`, `Tm`, `HasType`, `Value`, `Step`.
Part W: worked combinations on the same toy objects.
Assumed: Lean basics (E001–E033). No Mathlib: everything is core Lean.
-/

namespace H020Guide

/-! # Toy objects (not the exercise's) -/

/-- Two kinds, playing the role of types. -/
inductive Kd where
  | num
  | flag

/-- Toy syntax: numerals `k n`, two flags, a binary `add`, and `pos a` ("is `a` positive?"). -/
inductive Ex where
  | k (n : Nat)
  | on
  | off
  | add (a b : Ex)
  | pos (a : Ex)

/-- `Ok e K`: `e` has kind `K`. A proof of `Ok e K` is a tree of these rules (a *derivation*). -/
inductive Ok : Ex → Kd → Prop
  | k {n : Nat} : Ok (.k n) .num
  | on : Ok .on .flag
  | off : Ok .off .flag
  | add {a b : Ex} : Ok a .num → Ok b .num → Ok (.add a b) .num
  | pos {a : Ex} : Ok a .num → Ok (.pos a) .flag

/-- The finished expressions (the toy's values). -/
inductive Done : Ex → Prop
  | k {n : Nat} : Done (.k n)
  | on : Done .on
  | off : Done .off

/-- One reduction step. `addL` and `posC` reduce inside a subexpression (*congruence* rules). -/
inductive Red : Ex → Ex → Prop
  | addK {n m : Nat} : Red (.add (.k n) (.k m)) (.k (n * m))
  | addL {a a' b : Ex} : Red a a' → Red (.add a b) (.add a' b)
  | posZ : Red (.pos (.k 0)) .off
  | posS {n : Nat} : Red (.pos (.k (n + 1))) .on
  | posC {a a' : Ex} : Red a a' → Red (.pos a) (.pos a')

/-! # Part R · Reference entries -/

/-! ## Canonical forms: what a finished expression of a given kind looks like -/

/-! ### R1. `cases hv` with `hv : Done e` · goal list: one goal per rule of `Done`, `e` replaced by
that rule's shape. `cases hv with | k => … | on => … | off => …` names the cases. -/
example {e : Ex} (P : Ex → Prop) (k0 : ∀ n, P (.k n)) (k1 : P .on) (k2 : P .off) (hv : Done e) :
    P e := by
  cases hv
  exact k0 _
  exact k1
  exact k2

/-! ### R2. `exact ⟨_, rfl⟩` · closes `∃ n, a = b` when `b` becomes `a` for the right `n`
The `_` is the witness; Lean finds it while checking `rfl`. -/
example (m : Nat) : ∃ n, Ex.k m = Ex.k n := by
  exact ⟨_, rfl⟩

/-! ### R3. `cases h` where no rule can produce `h` · goal list: closes the goal
No rule of `Ok` concludes `Ok .on .num`, so there is no case left to prove. -/
example (G : Prop) (h : Ok .on .num) : G := by
  cases h

/-! ### R4. `exact Or.inl x` / `Or.inr x` · closes `A ∨ B` with a proof of one side
`.k` means `Done.k`: Lean reads the namespace off the expected type `Done (.k n)` (a rule is a
function from its premises to its conclusion; `Done.k` has no premises). -/
example (n : Nat) (B : Prop) : Done (.k n) ∨ B := by
  exact Or.inl .k

/-! ## Progress: induction on the kinding derivation -/

/-! ### R5. `induction h` with `h : Ok e K` · goal list: one goal per rule of `Ok`; every premise
that is itself an `Ok` gets an induction hypothesis (IH) `a_ih✝`.
`induction h with | k => … | add ha hb iha ihb => … | pos ha iha => …` names first the rule's
premises, then the IHs; the implicit `{a b}` stay `a✝ b✝`. -/
example {e : Ex} {K : Kd} (P : Ex → Kd → Prop) (kk : ∀ e K, P e K) (h : Ok e K) : P e K := by
  induction h
  all_goals exact kk _ _

/-! ### R6. `right` (and `left`) · goal: `A ∨ B` → `B` (`left`: → `A`) -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R7. `rcases ih with hv | ⟨a', st⟩` · goal list: one goal per side of `∨`; the `∃` is
opened into a witness `a'` and its proof `st` -/
example {a : Ex} (G : Prop) (k1 : Done a → G) (k2 : ∀ a', Red a a' → G)
    (ih : Done a ∨ ∃ a', Red a a') : G := by
  rcases ih with hv | ⟨a', st⟩
  exact k1 hv
  exact k2 a' st

/-! ### R8. `obtain ⟨n, rfl⟩ := hc` with `hc : ∃ n, e = Ex.k n` · context and goal: `e` is
replaced by `Ex.k n` everywhere (`e` must be a local variable) -/
example {e : Ex} (P : Ex → Prop) (kk : ∀ n, P (.k n)) (hc : ∃ n, e = Ex.k n) : P e := by
  obtain ⟨n, rfl⟩ := hc
  exact kk n

/-! ### R9. `exact ⟨_, .addK⟩` · closes `∃ e', Red e e'` with a rule; the witness `_` is read
off the rule's conclusion -/
example (n m : Nat) : ∃ e', Red (.add (.k n) (.k m)) e' := by
  exact ⟨_, .addK⟩

/-! ### R10. `rcases hc with rfl | rfl` with `hc : e = Ex.on ∨ e = Ex.off` · goal list: two goals,
`e` replaced by `Ex.on` in the first and by `Ex.off` in the second -/
example {e : Ex} (P : Ex → Prop) (k1 : P .on) (k2 : P .off) (hc : e = Ex.on ∨ e = Ex.off) :
    P e := by
  rcases hc with rfl | rfl
  exact k1
  exact k2

/-! ### R11. `cases n` on a `Nat` inside a term · goal list: `0` and `n + 1`, so a rule whose
conclusion mentions `k 0` or `k (n + 1)` now matches.
`cases n with | zero => … | succ n => …` names the new `n`. -/
example (n : Nat) : ∃ e', Red (.pos (.k n)) e' := by
  cases n
  exact ⟨_, .posZ⟩
  exact ⟨_, .posS⟩

/-! ## Preservation: induction on the step, inversion of the kinding -/

/-! ### R12. `induction hs generalizing K` · goal list: one goal per rule of `Red`. `h` mentions
`e`, so Lean carries it into each goal; with `generalizing K` the IH reads `∀ {K}, Ok a K → …`. -/
example {e e' : Ex} {K : Kd} (P : Ex → Kd → Prop) (kk : ∀ e K, P e K) (h : Ok e K)
    (hs : Red e e') : P e' K := by
  induction hs generalizing K
  all_goals exact kk _ _

/-! ### R13. `cases h` with `h : Ok (.add a b) K` (inversion) · context and goal: `h` → the
premises of the only rule that concludes `Ok (.add …) _`, and `K` → that rule's kind `.num`.
`cases h with | add ha hb => …` names the premises. -/
example {a b : Ex} {K : Kd} (P : Kd → Prop) (kk : Ok a .num → Ok b .num → P .num)
    (h : Ok (.add a b) K) : P K := by
  cases h
  exact kk (by assumption) (by assumption)

/-! ### R14. `cases h` with `h : Ok (.k n) K` · context and goal: no premises, but `K` → `.num` -/
example {n m : Nat} {K : Kd} (h : Ok (.k n) K) : Ok (.k m) K := by
  cases h
  exact .k

/-! ### R15. `exact .add (ih ha) hb` · closes the goal: a rule applied to the IH; the IH's
implicit `{K}` is found from `ha` -/
example {a a' b : Ex} (ih : ∀ {K : Kd}, Ok a K → Ok a' K) (ha : Ok a .num) (hb : Ok b .num) :
    Ok (.add a' b) .num := by
  exact .add (ih ha) hb

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. Inversion twice: R13 on `pos`, then R3 -/
example {K : Kd} (h : Ok (.pos .on) K) : False := by
  cases h with
    | pos ha => cases ha

/-! ### W2. Finished expressions do not reduce: R1, then R3 on the step in every case -/
example {e e' : Ex} (hv : Done e) (hs : Red e e') : False := by
  cases hv <;> cases hs

/-! ### W3. Kinds survive a reduction: R12, then in each case R13/R14 and R15 -/
example {e e' : Ex} {K : Kd} (h : Ok e K) (hs : Red e e') : Ok e' K := by
  induction hs generalizing K with
    | addK => cases h; exact .k
    | addL _ ih => cases h with | add ha hb => exact .add (ih ha) hb
    | posZ => cases h; exact .off
    | posS => cases h; exact .on
    | posC _ ih => cases h with | pos ha => exact .pos (ih ha)

end H020Guide
