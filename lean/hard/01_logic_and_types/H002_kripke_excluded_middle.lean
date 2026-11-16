/- H002 | Kripke semantics: excluded middle is not intuitionistic | 1-1.5 h | natural deduction, Kripke models, structure, soundness, countermodel
GOAL
  Intuitionistic natural deduction `ND` is sound for Kripke models. Show `¬¬(a ∨ ¬a)` is derivable,
  then build a two-world Kripke model where `p ∨ ¬p` fails, so `p ∨ ¬p` is not derivable.

REFERENCE
  -- Kripke model: worlds `W` preordered by `le` ("w' extends w"); `val n w`: variable n holds at w,
  -- and stays true in extensions (`mono`). `Forces M w (.imp a b)`: every `w' ≥ w` forcing a forces b.
  example : H002.Kripke := { W := Unit, le _ _ := True, refl _ := trivial, trans _ _ := trivial, val _ _ := True, mono _ h := h }
  example (M : H002.Kripke) (u v w : M.W) (h1 : M.le u v) (h2 : M.le v w) : M.le u w := M.trans h1 h2
  example (M : H002.Kripke) (w : M.W) (a b : H002.Form) (h : H002.Forces M w (.and a b)) : H002.Forces M w a := h.1
  example (a b : H002.Form) : H002.ND [a, .imp a b] b := .impE (a := a) (.hyp (by simp)) (.hyp (by simp))
  -- ^ give `impE` its implicit cut formula `(a := …)`, otherwise each `by simp` meets a metavariable
  -- `induction a generalizing w w' with | var n => _ | ... | imp a b iha ihb => _` (on a formula)
  -- `induction h generalizing w with | hyp hm => _ | ... | impE _ _ ih1 ih2 => _` (on a derivation)
  #check @List.mem_cons   -- a ∈ b :: l ↔ a = b ∨ a ∈ l
NOTE: `neg a` abbreviates `a → ⊥`. `Forces` unfolds by `rfl`, so `intro w' hle ha` works on an `.imp` goal.
-/

namespace H002

-- BEGIN SPEC
inductive Form where
  | var (n : Nat)
  | bot
  | and (a b : Form)
  | or (a b : Form)
  | imp (a b : Form)

/-- Intuitionistic natural deduction. -/
inductive ND : List Form → Form → Prop
  | hyp {Γ : List Form} {a : Form} : a ∈ Γ → ND Γ a
  | botE {Γ : List Form} {a : Form} : ND Γ .bot → ND Γ a
  | andI {Γ : List Form} {a b : Form} : ND Γ a → ND Γ b → ND Γ (.and a b)
  | andE1 {Γ : List Form} {a b : Form} : ND Γ (.and a b) → ND Γ a
  | andE2 {Γ : List Form} {a b : Form} : ND Γ (.and a b) → ND Γ b
  | orI1 {Γ : List Form} {a b : Form} : ND Γ a → ND Γ (.or a b)
  | orI2 {Γ : List Form} {a b : Form} : ND Γ b → ND Γ (.or a b)
  | orE {Γ : List Form} {a b c : Form} :
      ND Γ (.or a b) → ND (a :: Γ) c → ND (b :: Γ) c → ND Γ c
  | impI {Γ : List Form} {a b : Form} : ND (a :: Γ) b → ND Γ (.imp a b)
  | impE {Γ : List Form} {a b : Form} : ND Γ (.imp a b) → ND Γ a → ND Γ b

/-- A Kripke model: a preorder of worlds and a monotone valuation. -/
structure Kripke where
  W : Type
  le : W → W → Prop
  refl : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w
  val : Nat → W → Prop
  mono : ∀ {n : Nat} {w w' : W}, le w w' → val n w → val n w'

def Forces (M : Kripke) : M.W → Form → Prop
  | w, .var n => M.val n w
  | _, .bot => False
  | w, .and a b => Forces M w a ∧ Forces M w b
  | w, .or a b => Forces M w a ∨ Forces M w b
  | w, .imp a b => ∀ w', M.le w w' → Forces M w' a → Forces M w' b

abbrev neg (a : Form) : Form := .imp a .bot
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem forces_mono (M : Kripke) (a : Form) {w w' : M.W} (hle : M.le w w') (h : Forces M w a) :
    Forces M w' a := by
  sorry

-- MILESTONE (optional: change or delete)
theorem forces_cons (M : Kripke) {Γ : List Form} {a : Form} {w : M.W}
    (hΓ : ∀ g ∈ Γ, Forces M w g) (ha : Forces M w a) : ∀ g ∈ a :: Γ, Forces M w g := by
  sorry

-- MILESTONE (optional: change or delete)
theorem lem_countermodel : ∃ (M : Kripke) (w : M.W), ¬ Forces M w (.or (.var 0) (neg (.var 0))) := by
  sorry

-- BEGIN SPEC
theorem nnlem (a : Form) : ND [] (neg (neg (.or a (neg a)))) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem soundness {Γ : List Form} {a : Form} (h : ND Γ a) (M : Kripke) (w : M.W)
    (hΓ : ∀ g ∈ Γ, Forces M w g) : Forces M w a :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem lem_not_derivable : ¬ ND [] (.or (.var 0) (neg (.var 0))) :=
-- END SPEC
  sorry

end H002

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `nnlem`: assume `¬(a ∨ ¬a)`; to reach `⊥` prove `¬a` (assume `a`, then `a ∨ ¬a` contradicts the hypothesis). Countermodel: two worlds `false ≤ true`, with `p` true only at `true`.
H2. `soundness`: induction on `h` generalizing `w`. `impI` moves to a later world `w'`, so every hypothesis must be carried to `w'` (`forces_mono` on each). `orE` cases on the forced disjunction and uses `forces_cons`. `lem_not_derivable`: apply `soundness` at the countermodel's world `false`.
H3. Model: `W := Bool`, `le a b := a = true → b = true`, `val _ w := w = true`. At `false`, `p` is not forced, and `¬p` fails since world `true ≥ false` forces `p`. `nnlem`: `.impI (.impE (a := .or a (neg a)) (.hyp (by simp)) (.orI2 (.impI _)))`.
-/
