/- H021 | IMP big-step semantics | 45-75 min | inductive semantics, determinism, generalize, induction on derivations
GOAL
  For the imperative language IMP with a big-step semantics, prove that evaluation is
  deterministic, that `while true do c` never terminates, and compute a small program's result.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H021

-- BEGIN SPEC
abbrev State := Nat → Int

inductive AExp where
  | num (n : Int)
  | var (x : Nat)
  | plus (a b : AExp)
  | minus (a b : AExp)

def aeval (s : State) : AExp → Int
  | .num n => n
  | .var x => s x
  | .plus a b => aeval s a + aeval s b
  | .minus a b => aeval s a - aeval s b

inductive BExp where
  | tt
  | ff
  | le (a b : AExp)
  | not (b : BExp)
  | and (b1 b2 : BExp)

def beval (s : State) : BExp → Bool
  | .tt => true
  | .ff => false
  | .le a b => decide (aeval s a ≤ aeval s b)
  | .not b => !beval s b
  | .and b1 b2 => beval s b1 && beval s b2

inductive Com where
  | skip
  | assign (x : Nat) (a : AExp)
  | seq (c1 c2 : Com)
  | ite (b : BExp) (c1 c2 : Com)
  | while (b : BExp) (c : Com)

def update (s : State) (x : Nat) (v : Int) : State := fun y => if y = x then v else s y

inductive BigStep : Com → State → State → Prop
  | skip {s : State} : BigStep .skip s s
  | assign {s : State} {x : Nat} {a : AExp} : BigStep (.assign x a) s (update s x (aeval s a))
  | seq {c1 c2 : Com} {s s' s'' : State} :
      BigStep c1 s s' → BigStep c2 s' s'' → BigStep (.seq c1 c2) s s''
  | iteT {b : BExp} {c1 c2 : Com} {s s' : State} :
      beval s b = true → BigStep c1 s s' → BigStep (.ite b c1 c2) s s'
  | iteF {b : BExp} {c1 c2 : Com} {s s' : State} :
      beval s b = false → BigStep c2 s s' → BigStep (.ite b c1 c2) s s'
  | whileF {b : BExp} {c : Com} {s : State} :
      beval s b = false → BigStep (.while b c) s s
  | whileT {b : BExp} {c : Com} {s s' s'' : State} :
      beval s b = true → BigStep c s s' → BigStep (.while b c) s' s'' → BigStep (.while b c) s s''

def prog : Com := .seq (.assign 0 (.num 1)) (.assign 1 (.plus (.var 0) (.num 1)))
-- END SPEC

/- SKELETON · bigstep_det
  No milestones: the three theorems are independent. This is the longest one.
  1. Induct on the first derivation, keeping the second end state free:          R1, R2
       `induction h1 generalizing s2 with`, one alternative per rule (7)
  2. In each alternative, invert the second derivation `h2`:                      R3, R4
       skip, assign: one case survives and the goal is `a = a`                   rfl
       seq: one case. `ih1` on the first premise equates the two middle
         states; retype the second premise with it, then `ih2`                   R5
       ite, while: two cases survive (`iteT`/`iteF`, `whileF`/`whileT`)
         same rule as the outer case: the IH (whileF: rfl; whileT: as seq)       R5
         the other rule: guards `= true` and `= false` clash                     R6
-/
-- BEGIN SPEC
theorem bigstep_det {c : Com} {s s1 s2 : State} (h1 : BigStep c s s1) (h2 : BigStep c s s2) :
    s1 = s2 :=
-- END SPEC
  by
    induction h1 generalizing s2 with
    | skip => cases h2; rfl
    | assign => cases h2; rfl
    | seq _ _ ih1 ih2 =>
      cases h2 with
      | seq h1' h2' => exact ih2 (ih1 h1' ▸ h2')
    | iteT hb _ ih =>
      cases h2 with
      | iteT _ h => exact ih h
      | iteF hb' _ => simp_all
    | iteF hb _ ih =>
      cases h2 with
      | iteT hb' _ => simp_all
      | iteF _ h => exact ih h
    | whileF hb =>
      cases h2 with
      | whileF _ => rfl
      | whileT hb' _ _ => simp_all
    | whileT hb _ _ ih1 ih2 =>
      cases h2 with
      | whileF hb' => simp_all
      | whileT _ h1' h2' => exact ih2 (ih1 h1' ▸ h2')

/- SKELETON · while_true_diverges
  1. The goal is a `¬`: intro h                                                  (E008)
  2. Replace the command in `h` by a variable so induction applies:              R7
       hw : Com.while BExp.tt c = w
  3. Induct on `h`; `hw` enters every case and every IH:                         R8
       whileF: `hw` forces the guard to be `BExp.tt`, but `hb` says it is
         `false`: split `hw`, substitute the guard, evaluate `hb`                R9 → R10 → R11
       whileT: the IH of the loop premise takes `hw`                             exact
       every other rule (one `| _ =>`): `hw` equates different constructors      R12
-/
-- BEGIN SPEC
theorem while_true_diverges (c : Com) (s s' : State) : ¬ BigStep (.while .tt c) s s' :=
-- END SPEC
  by
    intro h
    generalize hw : Com.while BExp.tt c = w at h
    induction h with
    | whileF hb =>
      injection hw with h1 h2
      subst h1
      simp [beval] at hb
    | whileT _ _ _ _ ih2 => exact ih2 hw
    | _ => cases hw

/- SKELETON · prog_result
  1. Invert `h`: `prog` unfolds to a `seq`; name its two premises                R13, R4
  2. Invert each premise: the `assign` rule fixes its end state                  R3, R3
  3. Compute `s' 1`: unfold `update` and `aeval`, decide the `if`s               R14
-/
-- BEGIN SPEC
theorem prog_result (s s' : State) (h : BigStep prog s s') : s' 1 = 2 :=
-- END SPEC
  by
    cases h with
    | seq h1 h2 =>
      cases h1
      cases h2
      simp [update, aeval]

end H021

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Determinism and divergence are inductions on a derivation (rule induction, R1); `prog_result`
    is pure inversion with `cases` (R3, R13) followed by computation.
H2. Determinism: `induction h1 generalizing s2`, then `cases h2` in every case. In `seq` and
    `whileT`, the first IH identifies the middle states before the second IH applies; cases with
    contradictory guards close with `simp_all`. Divergence: `generalize` the command, then induct:
    `whileF` contradicts `beval s .tt = true`, `whileT` is the IH, every other rule clashes with `hw`.
H3. `seq` case: `cases h2 with | seq h1' h2' => exact ih2 (ih1 h1' ▸ h2')`.
    Divergence: `generalize hw : Com.while BExp.tt c = w at h`; its `whileF` case is
    `injection hw with h1 h2; subst h1; simp [beval] at hb`. `prog_result` ends with `simp [update, aeval]`.
-/
