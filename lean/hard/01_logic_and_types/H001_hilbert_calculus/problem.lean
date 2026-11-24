/- H001 | Hilbert calculus: deduction theorem and soundness | 45-75 min | inductive Prop, induction on derivations, rcases, Bool semantics
GOAL
  A Hilbert-style calculus for implicational logic with `⊥` (axiom schemes K, S, double negation;
  rule modus ponens). Derive `a → a`, prove the deduction theorem and hypothetical syllogism, then
  soundness for Boolean valuations, and conclude that `⊥` is not provable.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · imp_intro   (milestone: prove it first; used in `deduction`, cases `hyp` and axioms)
  (In the skeletons `x ⇒ y` is the object-level `.imp x y`, Lean prints it `x.imp y`.)
  1. One `mp`: major premise the axiom `ax1 : b ⇒ (a ⇒ b)`, minor premise `h`;
     every implicit formula is fixed by unification:                         R1
-/
-- MILESTONE (optional: change or delete)
theorem imp_intro {Γ : List Form} {a b : Form} (h : Prov Γ b) : Prov Γ (.imp a b) := by
  sorry

/- SKELETON · eval_imp   (milestone: prove it first; used in `soundness`, cases `ax1`, `ax2`, `mp`)
  1. Split on the Bool `eval v a`, keeping the equation `h`:                  R2
  2. In both goals (one tactic for both: `<;>`): unfold `eval` at `a.imp b`
     and rewrite with `h`; the Bool laws close the goal:                     R3, R4
-/
-- MILESTONE (optional: change or delete)
theorem eval_imp (v : Nat → Bool) (a b : Form) :
    eval v (.imp a b) = true ↔ (eval v a = true → eval v b = true) := by
  sorry

/- SKELETON · prov_self   (I = S K K; build the derivation tree bottom up)
  Fix any formula `b'` (e.g. `a`) and put `B := b' ⇒ a`.
  1. Outer `mp` with cut formula `a ⇒ B`: premises `Prov Γ ((a ⇒ B) ⇒ (a ⇒ a))`
     and `Prov Γ (a ⇒ B)`. As one term, the cut is fixed by the premises below;
     with `refine .mp ?_ ?_` it is not, so name it `(a := …)`:               R1, R5
  2. First premise: `mp` of `ax2` (S) with `ax1 : a ⇒ (B ⇒ a)`; naming that
     `ax1`'s second formula `B` is safe (in the full term unification finds it):  R1, R5
  3. Second premise: `ax1 : a ⇒ (b' ⇒ a)`; nothing fixes `b'`, so name it:     R5
-/
-- BEGIN SPEC
theorem prov_self (Γ : List Form) (a : Form) : Prov Γ (.imp a a) :=
-- END SPEC
  sorry

/- SKELETON · deduction   (milestone `imp_intro` and `prov_self` first; the real work)
  1. Induction on the derivation `h`; every goal is `Prov Γ (a.imp ·)`:      R6
  2. `hyp`: turn the membership in `a :: Γ` into `= a ∨ ∈ Γ`, split it,
     substituting in the first branch:                                       R7, R8
       it is `a`:      `prov_self`
       it is in `Γ`:   `imp_intro` of a `.hyp`                              R1
  3. `ax1`, `ax2`, `ax3`: `imp_intro` of that axiom                           R1
  4. `mp`: the IHs are `Prov Γ (a ⇒ (x ⇒ y))` and `Prov Γ (a ⇒ x)`; feed them
     to `ax2` with two `mp`s (implicits inferred)                            R1
-/
-- BEGIN SPEC
theorem deduction {Γ : List Form} {a b : Form} (h : Prov (a :: Γ) b) : Prov Γ (.imp a b) :=
-- END SPEC
  sorry

/- SKELETON · prov_trans   (uses `deduction`)
  1. `deduction` backwards, three times; the context list is then
     `a :: b.imp c :: a.imp b :: Γ` and the goal is `c`:                     R9
  2. `mp` with cut formula `b` named; its major premise `b ⇒ c` is a
     hypothesis, membership by `simp`:                                       R5, R1, R10
  3. The minor premise `b`: `mp` with cut formula `a` named; both premises
     are hypotheses:                                                         R5, R10
-/
-- BEGIN SPEC
theorem prov_trans (Γ : List Form) (a b c : Form) :
    Prov Γ (.imp (.imp a b) (.imp (.imp b c) (.imp a c))) :=
-- END SPEC
  sorry

/- SKELETON · soundness   (milestone `eval_imp` first)
  1. Induction on the derivation `h`:                                        R6
  2. `hyp`: apply `hv` to the formula and its membership proof:              R11
  3. `ax1`, `ax2`: rewrite every `⇒` with `eval_imp`, then `intro` the
     premises and apply them:                                                R12
  4. `ax3`: unfold `eval`; the Bool laws close it:                           R13
  5. `mp`: `eval_imp`'s `.mp` turns the first IH into a function; apply it
     to the second IH:                                                       R14
-/
-- BEGIN SPEC
theorem soundness {Γ : List Form} {a : Form} (h : Prov Γ a) (v : Nat → Bool)
    (hv : ∀ g ∈ Γ, eval v g = true) : eval v a = true :=
-- END SPEC
  sorry

/- SKELETON · consistent   (uses `soundness`)
  1. Assume a derivation `h` of `⊥` (`¬X` is `X → False`)
  2. `soundness h` at the valuation `fun _ => true`; its hypothesis
     argument is about the empty list:                                       R16
  3. The resulting `eval (fun _ => true) Form.bot = true` simplifies to `False`:   R15
-/
-- BEGIN SPEC
theorem consistent : ¬ Prov [] .bot :=
-- END SPEC
  sorry

end H001

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones first: `imp_intro` is one `mp` with `ax1` (R1); `eval_imp` is a case split on
    `eval v a` keeping the equation (R2), then unfolding (R3, R4). `prov_self` is the combinator identity
    `I = S K K`: two `ax1`s fed into one `ax2`, with the free formula named (R5). `consistent` is
    `soundness` at the valuation `fun _ => true`.
H2. `deduction`: induct on the derivation `h` (R6). A hypothesis is either `a` itself (`prov_self`) or in
    `Γ` (`List.mem_cons`, `rcases … with rfl | hm`: R7, R8); an axiom or old hypothesis `x` becomes
    `a → x` via `imp_intro`; for `mp`, combine both IHs with `ax2`. `prov_trans`: `apply deduction`
    three times (R9). `soundness`: induction on `h`; `simp only [eval_imp]` for `ax1`/`ax2` (R12),
    `simp [eval]` for `ax3` (R13), `(eval_imp v _ _).mp` for `mp` (R14).
H3. `prov_self`: `.mp (.mp .ax2 (.ax1 (b := .imp a a))) (.ax1 (b := a))`. `deduction`'s `mp` case:
    `exact .mp (.mp .ax2 ih1) ih2`. `prov_trans`: after `apply deduction` three times the context is
    `a :: b.imp c :: a.imp b :: Γ` and the goal is `c`: two `mp`s with cut formulas `b` and `a`, all
    premises `.hyp (by simp)` (R5, R10).
-/
