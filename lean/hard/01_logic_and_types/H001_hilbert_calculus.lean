/- H001 | Hilbert calculus: deduction theorem and soundness | 45-75 min | inductive Prop, induction on derivations, rcases, Bool semantics
GOAL
  A Hilbert-style calculus for implicational logic with `⊥` (axiom schemes K, S, double negation;
  rule modus ponens). Derive `a → a`, prove the deduction theorem and hypothetical syllogism, then
  soundness for Boolean valuations, and conclude that `⊥` is not provable.

REFERENCE
  -- `Prov Γ a`: formula `a` is derivable from the hypothesis list `Γ`; rules are its constructors.
  example (a b : H001.Form) : H001.Prov [] (.imp a (.imp b a)) := .ax1   -- dot-constructor syntax
  example (a b : H001.Form) : H001.Prov [a, .imp a b] b := .mp (a := a) (.hyp (by simp)) (.hyp (by simp))
  -- ^ `(a := a)` names `mp`'s implicit cut formula; without it each `by simp` meets a metavariable
  #check @List.mem_cons   -- a ∈ b :: l ↔ a = b ∨ a ∈ l
  -- `induction h` works directly on `h : Prov (a :: Γ) b`: `Γ` is a parameter of `Prov` (same in every rule).
  -- hyp case: `rcases List.mem_cons.mp hm with rfl | hm` splits "it is `a` itself" vs "it is in `Γ`".
  -- `induction h with | hyp hm => _ | ax1 => _ | ... | mp _ _ ih1 ih2 => _`
  -- `simp [eval]` unfolds the semantics; `cases h : eval v a` splits a Bool, keeping `h : eval v a = …`;
  -- `grind` closes Bool tautologies.
NOTE: `.imp a b` is "a → b" in the object logic, Lean's `→` is the meta level.
NOTE: `try?` finds a one-line proof of `soundness` (and then `consistent` is one `simpa`). Doing
  `soundness` by hand, one case per rule, is good practice; the real work is `deduction`.
-/

namespace H001

-- BEGIN SPEC
inductive Form where
  | var (n : Nat)
  | bot
  | imp (a b : Form)

/-- Hilbert system: three axiom schemes, modus ponens, hypotheses from Γ. -/
inductive Prov : List Form → Form → Prop
  | hyp {Γ : List Form} {a : Form} : a ∈ Γ → Prov Γ a
  | ax1 {Γ : List Form} {a b : Form} : Prov Γ (.imp a (.imp b a))
  | ax2 {Γ : List Form} {a b c : Form} :
      Prov Γ (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | ax3 {Γ : List Form} {a : Form} : Prov Γ (.imp (.imp (.imp a .bot) .bot) a)
  | mp {Γ : List Form} {a b : Form} : Prov Γ (.imp a b) → Prov Γ a → Prov Γ b

/-- Boolean semantics: `v` assigns a truth value to each variable. -/
def eval (v : Nat → Bool) : Form → Bool
  | .var n => v n
  | .bot => false
  | .imp a b => !eval v a || eval v b
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem imp_intro {Γ : List Form} {a b : Form} (h : Prov Γ b) : Prov Γ (.imp a b) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem eval_imp (v : Nat → Bool) (a b : Form) :
    eval v (.imp a b) = true ↔ (eval v a = true → eval v b = true) := by
  sorry

-- BEGIN SPEC
theorem prov_self (Γ : List Form) (a : Form) : Prov Γ (.imp a a) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem deduction {Γ : List Form} {a b : Form} (h : Prov (a :: Γ) b) : Prov Γ (.imp a b) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem prov_trans (Γ : List Form) (a b c : Form) :
    Prov Γ (.imp (.imp a b) (.imp (.imp b c) (.imp a c))) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem soundness {Γ : List Form} {a : Form} (h : Prov Γ a) (v : Nat → Bool)
    (hv : ∀ g ∈ Γ, eval v g = true) : eval v a = true :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem consistent : ¬ Prov [] .bot :=
-- END SPEC
  sorry

end H001

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `prov_self` is the combinator identity `I = S K K`: two `ax1`s fed into one `ax2`. `consistent` is `soundness` at the valuation `fun _ => true`.
H2. `deduction`: induct on the derivation `h`. A hypothesis is either `a` itself (`prov_self`) or in `Γ`; an axiom or old hypothesis `x` becomes `a → x` via `ax1` (`imp_intro`); for `mp`, combine both IHs with `ax2`. `prov_trans`: apply `deduction` three times. `soundness`: induction on `h`, unfold `eval` in each case.
H3. `prov_self`: `.mp (.mp .ax2 (.ax1 (b := .imp a a))) (.ax1 (b := a))`. `deduction`'s `mp` case: `exact .mp (.mp .ax2 ih1) ih2`. `prov_trans`: after `apply deduction` three times the context is `[a, b → c, a → b] ++ Γ` and the goal is `c`: two `mp`s with cut formulas `b` and `a`, all premises `.hyp (by simp)`.
-/
