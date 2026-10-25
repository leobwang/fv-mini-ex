/- H04 | IMP big-step semantics | 45-75 min | inductive semantics, determinism, generalize, induction on derivations
GOAL
  For the imperative language IMP with a big-step semantics, prove that evaluation is
  deterministic, that `while true do c` never terminates, and compute a small program's result.

REFERENCE
  -- BigStep c s s' : running c from state s terminates in state s'.
  example (s : H04.State) : H04.BigStep .skip s s := .skip
  -- Determinism: `induction h1 generalizing s2`, then `cases h2` in each case; contradictory
  -- branch conditions (`beval s b = true` and `= false`) close with `simp_all`.
  -- Induction on `h : BigStep (.while .tt c) s s'` fails (the command is not a variable):
  example (c : H04.Com) (s s' : H04.State) (h : H04.BigStep (.while .tt c) s s') : True := by
    generalize hw : H04.Com.while .tt c = w at h   -- now `induction h` works; hw remembers the shape
    trivial
  `h ▸ e` rewrites the type of `e` with `h : a = b`.
-/

namespace H04

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

-- BEGIN SPEC
theorem prog_result (s s' : State) (h : BigStep prog s s') : s' 1 = 2 :=
-- END SPEC
  by
    cases h with
    | seq h1 h2 =>
      cases h1
      cases h2
      simp [update, aeval]

end H04

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Determinism and divergence are both inductions on a derivation; `prog_result` is pure inversion (`cases`).
H2. Determinism: the `seq` and `whileT` cases need the IH for the first part to identify the intermediate state before using the second IH. Divergence: after `generalize`, the `whileF` case contradicts `beval s .tt = true`, the `whileT` case is the IH, and all other rules clash with `hw`.
H3. `seq` case: `cases h2 with | seq h1' h2' => exact ih2 (ih1 h1' ▸ h2')`. Divergence: `generalize hw : Com.while BExp.tt c = w at h; induction h with | whileF hb => injection hw with h1 h2; subst h1; simp [beval] at hb | whileT _ _ _ _ ih2 => exact ih2 hw | _ => cases hw`.
-/
