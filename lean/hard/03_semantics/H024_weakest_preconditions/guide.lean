/- Guide for H024 (Hoare logic: weakest preconditions and relative completeness).
Part R: one reference entry per tactic or term pattern the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
The entries about runs and derivations use a toy language `Op` on one counter `n : Nat`, its run
relation `Run`, a predicate `Up`, and a toy proof system `Ok`, all defined below. They are NOT the
exercise's objects.
Part W: worked combinations on the same toy objects.
Assumed: Lean basics (easy tier E001–E033). Core Lean only, no Mathlib.
-/

namespace H024Guide

/-! # Toy objects used by the entries -/

/-- A toy language on one counter `n : Nat`. -/
inductive Op where
  | inc                    -- n := n + 1
  | andThen (a b : Op)     -- a, then b
  | «while» (a : Op)       -- repeat a while n < 10; `while` is a keyword, hence «while»

/-- `Run a n k`: running `a` from counter `n` can end with counter `k`. -/
inductive Run : Op → Nat → Nat → Prop
  | inc {n : Nat} : Run .inc n (n + 1)
  | andThen {a b : Op} {n m k : Nat} : Run a n m → Run b m k → Run (.andThen a b) n k
  | stop {a : Op} {n : Nat} : 10 ≤ n → Run (.while a) n n
  | again {a : Op} {n m k : Nat} : n < 10 → Run a n m → Run (.while a) m k → Run (.while a) n k

/-- `Up Q n`: every counter value from `n` upward satisfies `Q`. A Prop-valued definition. -/
def Up (Q : Nat → Prop) (n : Nat) : Prop := ∀ m, n ≤ m → Q m

/-- `Ok P a Q`: a toy proof system with an `inc` axiom, sequencing, a loop rule, and weakening. -/
inductive Ok : (Nat → Prop) → Op → (Nat → Prop) → Prop
  | inc {Q : Nat → Prop} : Ok (fun n => Q (n + 1)) .inc Q
  | andThen {P Q R : Nat → Prop} {a b : Op} : Ok P a Q → Ok Q b R → Ok P (.andThen a b) R
  | loop {I : Nat → Prop} {a : Op} :
      Ok (fun n => I n ∧ n < 10) a I → Ok I (.while a) (fun n => I n ∧ 10 ≤ n)
  | weaken {P P' Q Q' : Nat → Prop} {a : Op} :
      (∀ n, P' n → P n) → Ok P a Q → (∀ n, Q n → Q' n) → Ok P' a Q'

/-! # Part R · Reference entries -/

/-! ## Moving through definitions and building runs -/

/-! ### R1. `intro` through a definition · context gains the ∀-variables of the unfolded body
`Up Q n` is a definition whose body is `∀ m, n ≤ m → Q m`; `intro` unfolds it by itself. -/
example (Q : Nat → Prop) (n : Nat) (h : ∀ m, n ≤ m → Q m) : Up Q n := by
  intro m hm
  exact h m hm

/-! ### R2. A hypothesis that is such a definition is a function: `h m hm` · goal closed
`h : Up Q n` applied to `m` and `hm : n ≤ m` is a proof of `Q m`. -/
example (Q : Nat → Prop) (n m : Nat) (h : Up Q n) (hm : n ≤ m) : Q m := by
  exact h m hm

/-! ### R3. `.ctor h₁ h₂` builds a run · goal closed
`.andThen h₁ h₂` means `Run.andThen h₁ h₂`: Lean reads the type name `Run` off the expected type,
and fills the implicit arguments `{a b n m k}` by unification. -/
example (a b : Op) (n m k : Nat) (h₁ : Run a n m) (h₂ : Run b m k) : Run (.andThen a b) n k := by
  exact .andThen h₁ h₂

/-! ## Building derivations -/

/-! ### R4. `.weaken pre d post` · goal closed; `fun _ h => h` proves `∀ n, Q n → Q n`
The rule of consequence: `pre` strengthens the precondition, `post` weakens the postcondition. -/
example (P' : Nat → Prop) (Q : Nat → Prop) (pre : ∀ n, P' n → Q (n + 1)) : Ok P' .inc Q := by
  exact .weaken pre .inc (fun _ h => h)

/-! ### R5. A lemma with arguments `(n) (h : A n)` IS a proof of `∀ n, A n → B n`
Pass it, partially applied, where a rule expects an implication between predicates. -/
theorem lt_succ_of_le' (k n : Nat) (h : n ≤ k) : n < k + 1 := Nat.lt_succ_of_le h
example (k : Nat) (Q : Nat → Prop) (d : Ok (fun n => n < k + 1) .inc Q) :
    Ok (fun n => n ≤ k) .inc Q := by
  exact .weaken (lt_succ_of_le' k) d (fun _ h => h)

/-! ### R6. A rule's conclusion has a fixed shape: `.loop d : Ok I (.while a) (fun n => I n ∧ 10 ≤ n)`
To reach another postcondition `Q`, wrap it: `.weaken (fun _ h => h) (.loop d) post`. -/
example (I Q : Nat → Prop) (a : Op) (d : Ok (fun n => I n ∧ n < 10) a I)
    (post : ∀ n, I n ∧ 10 ≤ n → Q n) : Ok I (.while a) Q := by
  refine .weaken (fun _ h => h) (.loop d) ?_
  exact post

/-! ## Equalities of predicates -/

/-! ### R7. `funext x` · goal `f = g` (functions) → context gains `x`, goal `f x = g x` -/
example {α : Type} (f g : α → Prop) (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-! ### R8. `apply propext` · goal `A = B` (propositions) → `A ↔ B`
`propext : (a ↔ b) → a = b` is the axiom of propositional extensionality. -/
example (A B : Prop) (h : A ↔ B) : A = B := by
  apply propext
  exact h

/-! ### R9. `constructor` on `↔` · goal `A ↔ B` → two goals `A → B` (case `mp`), `B → A` (case `mpr`) -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exact hab
  exact hba

/-! ## Inverting runs -/

/-! ### R10. `cases h` · context: `h` replaced by the premises of the one rule that fits
Only `Run.andThen` concludes `Run (.andThen a b) n k`, so there is one case. Its middle counter is
inaccessible (`m✝`): write `_` for it. `cases h with | andThen h₁ h₂ => tac` names the premises. -/
example (a b : Op) (n k : Nat) (P : Nat → Nat → Prop) (hP : ∀ m, Run a n m → Run b m k → P n k)
    (h : Run (.andThen a b) n k) : P n k := by
  cases h
  case andThen h₁ h₂ => exact hP _ h₁ h₂

/-! ### R11. `intro ⟨h₁, h₂⟩` · goal `A ∧ B → C` → context gains `h₁ : A`, `h₂ : B`, goal `C` -/
example (A B C : Prop) (h : A → B → C) : A ∧ B → C := by
  intro ⟨h₁, h₂⟩
  exact h h₁ h₂

/-! ### R12. `cases h` with two fitting rules · goal list: one goal per rule, indices substituted
`h : Run (.while a) n k` was made by `stop` (and then `k` is `n`) or by `again`. -/
example (a : Op) (n k : Nat) (P : Nat → Nat → Prop) (hstop : 10 ≤ n → P n n)
    (hagain : ∀ m, n < 10 → Run a n m → Run (.while a) m k → P n k)
    (h : Run (.while a) n k) : P n k := by
  cases h
  case stop hb => exact hstop hb
  case again m hb h₁ h₂ => exact hagain m hb h₁ h₂

/-! ## Induction on a language, and derivations with holes -/

/-! ### R13. `induction a generalizing n` · goal list: one goal per constructor; each IH is `∀ n, …`
Without `generalizing n`, each IH is only about the one `n` in the context. -/
example (P : Op → Nat → Prop) (hinc : ∀ n, P .inc n)
    (hand : ∀ a b, (∀ n, P a n) → (∀ n, P b n) → ∀ n, P (.andThen a b) n)
    (hwhile : ∀ a, (∀ n, P a n) → ∀ n, P (.while a) n) (a : Op) (n : Nat) : P a n := by
  induction a generalizing n
  case inc => exact hinc n
  case andThen a b iha ihb => exact hand a b iha ihb n
  case «while» a ih => exact hwhile a ih n

/-! ### R14. `refine .weaken ?_ d ?_` · goal list: the side conditions you left as `?_`
`d` must fix `P` and `Q`; a `?_` whose type still contains unknowns is an error. -/
example (P P' Q Q' : Nat → Prop) (a : Op) (d : Ok P a Q) (pre : ∀ n, P' n → P n)
    (post : ∀ n, Q n → Q' n) : Ok P' a Q' := by
  refine .weaken ?_ d ?_
  exact pre
  exact post

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. An unfolding equation for `Up`: R7 → R8 → R9, then R1, R2, R11, R12 -/
example (Q : Nat → Prop) : Up Q = fun n => Q n ∧ Up Q (n + 1) := by
  funext n
  apply propext
  constructor
  · intro h
    exact ⟨h n (Nat.le_refl n), fun m hm => h m (Nat.le_of_succ_le hm)⟩
  · intro ⟨h₀, h₁⟩ m hm
    cases hm with
      | refl => exact h₀
      | step hm' => exact h₁ _ (Nat.succ_le_succ hm')

/-! ### W2. Inverting a run, then rebuilding one: R10 and R3 -/
example (a b c : Op) (n k : Nat) (h : Run (.andThen (.andThen a b) c) n k) :
    Run (.andThen a (.andThen b c)) n k := by
  cases h with
    | andThen hab hc =>
      cases hab with
        | andThen ha hb => exact .andThen ha (.andThen hb hc)

/-! ### W3. A loop with an invariant (here `n ≤ 10`): R14, R6, R4 -/
example : Ok (fun n => n ≤ 10) (.while .inc) (fun n => n = 10) := by
  refine .weaken (fun _ h => h) (.loop (.weaken ?_ .inc (fun _ h => h))) ?_
  · intro n ⟨_, hlt⟩
    omega
  · intro n ⟨hle, hge⟩
    omega

end H024Guide
