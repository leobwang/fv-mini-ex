/- M044 | A fuel-based interpreter is sound and monotone | 15-20 min | interpreter with fuel, Option, split at, induction on fuel
GOAL
  `run n c s` executes the IMP command `c` from state `s` with fuel `n` (one unit per level of
  recursion; `none` = out of fuel). Prove it is sound (a result is a big-step result) and
  monotone (one more unit of fuel never changes a successful result).

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M044

-- BEGIN SPEC
abbrev State := Nat → Int

inductive AExp where
  | num (n : Int)
  | var (x : Nat)
  | plus (a b : AExp)
  | times (a b : AExp)

def aeval (s : State) : AExp → Int
  | .num n => n
  | .var x => s x
  | .plus a b => aeval s a + aeval s b
  | .times a b => aeval s a * aeval s b

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

/-- An interpreter with fuel: `none` means "ran out of fuel". -/
def run : Nat → Com → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, s => some s
  | _ + 1, .assign x a, s => some (update s x (aeval s a))
  | n + 1, .seq c1 c2, s =>
    match run n c1 s with
    | some s' => run n c2 s'
    | none => none
  | n + 1, .ite b c1 c2, s => if beval s b then run n c1 s else run n c2 s
  | n + 1, .while b c, s =>
    if beval s b then
      match run n c s with
      | some s' => run n (.while b c) s'
      | none => none
    else some s
-- END SPEC

/- SKELETON · run_sound
  1. Induct on the fuel, keeping the command and both states general:          R1
       ih : ∀ c s s', run n c s = some s' → BigStep c s s'
  2. zero: `run 0 c s` is `none`, so `h : none = some s'` is absurd:            R2, R3
  3. succ: one goal per command (write the last one `| «while» b c`):           R4
  4. skip, assign: unfold `h`, strip the `some`s, substitute, apply the rule:    R2, R5, R6, R7
  5. seq c1 c2: unfold `h`, split on the inner `match`:                         R2, R8
       some branch: `BigStep.seq` from the IH on both runs (the first one is
                    `heq✝ : run n c1 s = some s'✝`):                             R7, R10, R9
       none branch: `h : none = some s'`:                                       R3
  6. ite b c1 c2: unfold `h`, split on the `if`:                                R2, R11
       true:  `BigStep.iteT`, condition `h✝ : beval s b = true`:                R7, R9, R10
       false: `BigStep.iteF`; its first premise `beval s b = false`
              comes from `h✝ : ¬beval s b = true`:                              R7, R12, R10
  7. while b c: unfold `h`, split the `if`, then (true branch) the `match`:    R2, R11, R8
       true, some: `BigStep.whileT` with the IH twice (body, then the loop):    R7, R9, R10
       true, none:                                                              R3
       false: `h : some s = some s'`, then `BigStep.whileF`:                    R5, R6, R7, R12
-/
-- BEGIN SPEC
theorem run_sound (n : Nat) (c : Com) (s s' : State) (h : run n c s = some s') :
    BigStep c s s' :=
-- END SPEC
  sorry

/- SKELETON · run_mono
  1. The same induction:                                                        R1
       ih : ∀ c s s', run n c s = some s' → run (n + 1) c s = some s'
  2. zero: as in run_sound:                                                     R2, R3
  3. succ: one goal per command:                                                R4
  4. skip, assign: goal and `h` unfold to the same statement:                   R14
  5. seq c1 c2: unfold `h` AND the goal, split `h`'s `match`:                   R13, R8
       some: rewrite the goal's inner `run (n + 1) c1 s` with the IH on
             `heq✝`, then finish with the IH on `h`:                            R15, R9, R10
       none:                                                                    R3
  6. ite b c1 c2: unfold both, split `h`'s `if`; send the goal down the
     same branch, then the IH on `h`:                                           R13, R11, R16 / R17, R10
  7. while b c: unfold both, split `h`'s `if`:                                  R13, R11
       true:  pick the goal's `then` branch, split `h`'s `match`:               R16, R8
              some: rewrite the body's run with the IH, then the IH on `h`:     R15, R9, R10
                    (`simp only [run]` also unfolded the goal's loop call one level;
                    `ih _ _ _ h` still fits it by definition, see Traps)
              none:                                                             R3
       false: pick the goal's `else` branch; `h` is then the goal:              R17, exact h
-/
-- BEGIN SPEC
theorem run_mono (n : Nat) (c : Com) (s s' : State) (h : run n c s = some s') :
    run (n + 1) c s = some s' :=
-- END SPEC
  sorry

end M044

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems: induct on the fuel `n`, keeping `c s s'` general (R1): the recursive calls run other
    commands from other states. Then `cases c` (R4).
H2. In each successor case unfold one step of `run` with `simp only [run] at h` (`at h ⊢` for `run_mono`,
    R13), then `split at h` (R8, R11) to learn which branch produced `some s'`. `run_sound`: rebuild with
    the matching `BigStep` rule. `run_mono`: send the goal down the same branch with `if_pos`/`if_neg` and
    rewrite its inner `run` with the IH. A branch with `h : none = some _` closes by `simp at h`.
H3. `induction n generalizing c s s' with | zero => simp [run] at h | succ n ih => cases c with ...`; the `seq`
    case of `run_sound`: `simp only [run] at h; split at h; · exact .seq (ih _ _ _ ‹_›) (ih _ _ _ h); · simp at h`.
    The `false` branches: `.iteF (by simpa using ‹¬beval s b = true›) (ih _ _ _ h)`.
-/
