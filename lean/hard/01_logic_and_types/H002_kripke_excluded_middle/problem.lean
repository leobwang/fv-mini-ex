/- H002 | Kripke semantics: excluded middle is not intuitionistic | 1-1.5 h | natural deduction, Kripke models, structure, soundness, countermodel
GOAL
  Intuitionistic natural deduction `ND` is sound for Kripke models. Show `¬¬(a ∨ ¬a)` is derivable,
  then build a two-world Kripke model where `p ∨ ¬p` fails, so `p ∨ ¬p` is not derivable.

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · forces_mono   (prove this first; used in `soundness`, case `impI`)
  1. Induction on the formula `a`, generalizing `w w'`:                    R1
  2. `var`: forcing a variable is `M.val n w` (R2); the field `M.mono`:      R2, R3
  3. `bot`: `h` is already `False` (R2), so it proves anything forced       R2
  4. `and`: take `h.1`, `h.2`, push each through its IH, pair them         R2
       (the IH binds the worlds implicitly, `∀ {w w'}, …`: write `iha hle …`)  R1
  5. `or`: case on `h`, IH on that side, back with `.inl` / `.inr`          R4
  6. `imp`: no IH needed. The goal unfolds to a `∀` over worlds after `w'`:
       intro the later world `v` and its facts, then apply `h` at `v`
       (`v` is also after `w`: `M.trans`)                                 R5, R12, R3
-/
-- MILESTONE (optional: change or delete)
theorem forces_mono (M : Kripke) (a : Form) {w w' : M.W} (hle : M.le w w') (h : Forces M w a) :
    Forces M w' a := by
  sorry

/- SKELETON · forces_cons   (prove this second; used in `soundness`, cases `orE` and `impI`)
  1. Introduce `g` and `hg : g ∈ a :: Γ`:                                   R6
  2. Turn `hg` into `g = a ∨ g ∈ Γ`:                                         R7
  3. Split it, substituting `g := a` in the first branch:                    R8
       first branch `ha`, second branch `hΓ`
-/
-- MILESTONE (optional: change or delete)
theorem forces_cons (M : Kripke) {Γ : List Form} {a : Form} {w : M.W}
    (hΓ : ∀ g ∈ Γ, Forces M w g) (ha : Forces M w a) : ∀ g ∈ a :: Γ, Forces M w g := by
  sorry

/- SKELETON · lem_countermodel   (used in `lem_not_derivable`)
  1. Define the model with `let`: two worlds, one below the other; the variable
     holds only at the upper world. Fields with implicit binders as `fun h … => …`:   R9
  2. Pick the model and the lower world `w₀` (write it; `_` is not inferred):
                                                              refine ⟨M, w₀, ?_⟩
  3. Split the forced disjunction:                                          R10
  4. Left: forcing the variable at the lower world is an equation that is false:   R11
  5. Right: the forced `neg` is a function (R12); apply it at the upper world,
     which is later and forces the variable                                 R12
       both facts unfold through the `let` value to small `Bool` statements
       (an implication between equations, an equation): `fun _ => …`, `rfl`
-/
-- MILESTONE (optional: change or delete)
theorem lem_countermodel : ∃ (M : Kripke) (w : M.W), ¬ Forces M w (.or (.var 0) (neg (.var 0))) := by
  sorry

/- SKELETON · nnlem   (a derivation tree; build it bottom up, one `ND` constructor per step)
  1. `impI`: assume `h₀ = neg (a.or (neg a))`; goal `ND [h₀] Form.bot`:        R13
  2. `impE` with the cut formula `a.or (neg a)` named:                     R14
       premise 1 is the hypothesis `h₀`:                                   R13, R15
       premise 2: `ND [h₀] (a.or (neg a))`
  3. Choose the right disjunct `neg a` (`orI2`), then `impI` (assume `a`):     R13
       goal `ND [a, h₀] Form.bot`
  4. Repeat step 2; this time the disjunction comes from `a` (`orI1`, `hyp`):  R14, R13, R15
-/
-- BEGIN SPEC
theorem nnlem (a : Form) : ND [] (neg (neg (.or a (neg a)))) :=
-- END SPEC
  sorry

/- SKELETON · soundness   (milestones first: `forces_mono`, `forces_cons`)
  1. Induction on the derivation `h`, generalizing `w`:                      R16
  2. `hyp`: the membership premise and `hΓ`
  3. `botE`: the IH at `w` gives a forced `Form.bot`, i.e. `False`:           R17
  4. `andI`, `andE1`, `andE2`, `orI1`, `orI2`: IH at `w`, then `⟨_, _⟩`, `.1`, `.2`,
     `.inl`, `.inr`:                                                       R2, R4
  5. `orE`: split the IH's disjunction at `w` (`rcases … with h | h`, R8); in each
     branch the IH for that branch at `w`, its hypotheses from `forces_cons`
  6. `impI`: intro the later world `v`, `hv`, `ha` (R5). IH at `v`; its hypotheses:
     `forces_cons` of (each `hΓ` moved to `v` by `forces_mono` with `hv`) and `ha`
  7. `impE`: the IH for the implication at `w`, applied (R12) at `w` itself
     (`M.refl w`, R3) and to the IH for the premise
-/
-- BEGIN SPEC
theorem soundness {Γ : List Form} {a : Form} (h : ND Γ a) (M : Kripke) (w : M.W)
    (hΓ : ∀ g ∈ Γ, Forces M w g) : Forces M w a :=
-- END SPEC
  sorry

/- SKELETON · lem_not_derivable   (uses the milestone `lem_countermodel` and `soundness`)
  1. Assume a derivation `h` (`¬X` is `X → False`)
  2. Unpack the countermodel `M`, `w`, `hw`:                                 R18
  3. `soundness h M w _` forces the disjunction at `w`; its hypothesis argument
     is about the empty list:                                              R19
     that contradicts `hw`
-/
-- BEGIN SPEC
theorem lem_not_derivable : ¬ ND [] (.or (.var 0) (neg (.var 0))) :=
-- END SPEC
  sorry

end H002

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order. `forces_mono`: induction on `a` (R1); the `imp` case needs no IH,
    only `M.trans` (R3). `forces_cons`: `List.mem_cons` (R7) and `rcases … with rfl | hg` (R8).
    `nnlem`: assume `¬(a ∨ ¬a)`; to reach `⊥` prove `¬a` (assume `a`, then `a ∨ ¬a` contradicts the
    hypothesis). Countermodel: two worlds `false ≤ true`, with `p` true only at `true`.
H2. `soundness`: `induction h generalizing w` (R16). `impI` moves to a later world `v`, so every
    hypothesis must be carried to `v` (`forces_mono` on each) before `forces_cons` adds `ha`. `orE`
    cases on the forced disjunction and uses `forces_cons`. `impE` uses the implication at `w` itself
    (`M.refl w`). `lem_not_derivable`: apply `soundness` at the countermodel's world `false` (R18, R19).
H3. Model: `W := Bool`, `le a b := a = true → b = true`, `val _ w := w = true`, built with `let` (R9).
    At `false`, `p` is not forced, and `¬p` fails since world `true ≥ false` forces `p`.
    `nnlem`: `.impI (.impE (a := .or a (neg a)) (.hyp (by simp)) (.orI2 (.impI _)))` (R13–R15).
-/
