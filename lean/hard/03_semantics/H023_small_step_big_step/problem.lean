/- H023 | Small-step and big-step IMP agree | 1-1.5 h | small-step semantics, configurations, Star, induction on derivations, generalize
GOAL
  For IMP (H021's language, with `times` in place of `minus`), a big-step run `BigStep c s s'`
  exists iff the small-step semantics reaches the configuration `(skip, s')` from `(c, s)`.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H023

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

/-- Small-step semantics on configurations (command, state). `skip` is the final command. -/
inductive SmallStep : Com × State → Com × State → Prop
  | assign {x : Nat} {a : AExp} {s : State} :
      SmallStep (.assign x a, s) (.skip, update s x (aeval s a))
  | seqSkip {c : Com} {s : State} : SmallStep (.seq .skip c, s) (c, s)
  | seqStep {c1 c1' c2 : Com} {s s' : State} :
      SmallStep (c1, s) (c1', s') → SmallStep (.seq c1 c2, s) (.seq c1' c2, s')
  | iteT {b : BExp} {c1 c2 : Com} {s : State} :
      beval s b = true → SmallStep (.ite b c1 c2, s) (c1, s)
  | iteF {b : BExp} {c1 c2 : Com} {s : State} :
      beval s b = false → SmallStep (.ite b c1 c2, s) (c2, s)
  | whileUnfold {b : BExp} {c : Com} {s : State} :
      SmallStep (.while b c, s) (.ite b (.seq c (.while b c)) .skip, s)

/-- Zero or more small steps. -/
inductive Star : Com × State → Com × State → Prop
  | refl (p : Com × State) : Star p p
  | step {p q r : Com × State} : SmallStep p q → Star q r → Star p r
-- END SPEC

/- SKELETON · star_trans   (milestone 1: used in big_to_small, cases seq and whileT)
  1. Induction on `h1`; its indices `p q` are plain variables, so no generalize:       R2
  2. refl: `h2` (carried into each goal because it mentions `q`) is the goal itself.
     step: one `Star.step` with the step `st`, the rest is `ih` applied to `h2`:       R1
-/
-- MILESTONE (optional: change or delete)
theorem star_trans {p q r : Com × State} (h1 : Star p q) (h2 : Star q r) : Star p r := by
  sorry

/- SKELETON · star_seq   (milestone 2: used in big_to_small, cases seq and whileT)
  1. Both endpoints of `h` are pairs: generalize the source, then the target:          R4, R4
  2. Induction on `h`, generalizing `c1 s`; name the middle configuration `q'`:        R5, R3
  3. refl: `hp` and `hq` together force `c1 = c1'`, `s = s'`; then `Star.refl`:         R6, R7, R1
  4. step: substitute `hp`, split `q'` into `(c, t)`, then one `Star.step` whose
     small step is `SmallStep.seqStep st` and whose rest is `ih` at `(c, t)`:           R6, R8, R1, R9
-/
-- MILESTONE (optional: change or delete)
theorem star_seq {c1 c1' c2 : Com} {s s' : State} (h : Star (c1, s) (c1', s')) :
    Star (.seq c1 c2, s) (.seq c1' c2, s') := by
  sorry

/- SKELETON · step_then_big   (milestone 3: the whole step case of small_to_big)
  1. Generalize both configurations of `h1`:                                            R4, R4
  2. Induction on `h1`, generalizing `c c' s s' t` (so `ih` takes any `h2`):            R5
     six goals, one per `SmallStep` constructor
  3. In every goal, first `cases hp; cases hq` (both are pair = pair now) to turn
     `c c' s s'` into the step's data:                                                  R7, R7
  4. Then, per constructor:
       assign       invert `h2 : BigStep Com.skip …` (it fixes `t`), then `BigStep.assign`   R10, R1
       seqSkip      `BigStep.seq` with `BigStep.skip` first                                R1
       seqStep      invert `h2` on `seq`, use `ih` on the first half, rebuild `BigStep.seq`  R11, R9, R1
                    (`ih` takes the new big-step run first, then the two equations)
       iteT, iteF   the matching `BigStep.ite…` with `hb` and `h2`                         R1
       whileUnfold  invert `h2` on `ite`: two goals.  iteT: invert again on `seq`, then
                    `BigStep.whileT`.  iteF: invert on `skip`, then `BigStep.whileF`        R12, R11, R10, R1
  Model: guide W2 (same shape on `Tm`, without the pairs).
-/
-- MILESTONE (optional: change or delete)
theorem step_then_big {c c' : Com} {s s' t : State} (h1 : SmallStep (c, s) (c', s'))
    (h2 : BigStep c' s' t) : BigStep c s t := by
  sorry

/- SKELETON · big_to_small
  Prove star_trans and star_seq first; steps 3 and 5 use them.
  1. Induction on the big-step run `h` (indices `c s s'` are variables):                R2
     seven goals: skip, assign, seq, iteT, iteF, whileF, whileT
  2. skip, assign, iteT, iteF: zero or one `SmallStep`, then the rest (`refl` or `ih`)  R1
  3. seq: run `c1` inside `seq _ c2` (star_seq ih1), take `SmallStep.seqSkip`, then ih2;
     glue the two runs with star_trans                                                  R1
  4. whileF: `whileUnfold`, then `SmallStep.iteF hb`, then `refl`                        R1
  5. whileT: `whileUnfold`, then `SmallStep.iteT hb`, then the chain of step 3            R1
-/
-- BEGIN SPEC
theorem big_to_small {c : Com} {s s' : State} (h : BigStep c s s') : Star (c, s) (.skip, s') :=
-- END SPEC
  sorry

/- SKELETON · small_to_big
  Prove step_then_big first; it is the whole step case (step 4).
  1. Generalize both pairs of `h`. In the target write `Com.skip`, not `.skip`:          R4, R4
  2. Induction on `h`, generalizing `c s`; name the middle configuration `q'`:          R5, R3
  3. refl: `cases hp; cases hq` leave `BigStep Com.skip _ _` (equal states): `BigStep.skip`  R6, R7, R1
  4. step: substitute `hp`, split `q'` into `(c', t)`, get the rest from `ih` with
     `rfl`, push the first step `st` back with step_then_big                             R6, R8, R9
-/
-- BEGIN SPEC
theorem small_to_big {c : Com} {s s' : State} (h : Star (c, s) (.skip, s')) : BigStep c s s' :=
-- END SPEC
  sorry

end H023

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order: star_trans, star_seq, step_then_big. big_to_small is an induction on the `BigStep` run where every case is a chain of `Star.step`s (R2, R1); `seq` and `whileT` run a whole sub-run inside `seq _ c2` (star_seq) and glue runs with star_trans. small_to_big is an induction on `Star` that pushes one small step back through a big-step run (step_then_big).
H2. `Star`'s indices are pairs, so `induction` needs `generalize hp : (c, s) = p at h; generalize hq : (Com.skip, s') = q at h; induction h generalizing c s with | refl => … | @step _ q' _ st _ ih => …` (R4, R5, R3). In the step case: `subst hp; obtain ⟨c', t⟩ := q'`, then `ih rfl hq` (R6, R8, R9). step_then_big: the same generalize, `induction h1 generalizing c c' s s' t`, `cases hp; cases hq` in each case, then invert `h2` with `cases h2` when its command is a constructor (`Com.skip`, `seq`, `ite`; R10–R12). In `seqStep`, `ih` takes the run first: `ih h21 rfl rfl`.
H3. `whileT` case: `.step .whileUnfold (.step (.iteT hb) (star_trans (star_seq ih1) (.step .seqSkip ih2)))`. `whileUnfold` case of `step_then_big`: `cases h2 with | iteT hb h => cases h with | seq h1 h2 => exact .whileT hb h1 h2 | iteF hb h => cases h; exact .whileF hb`.
-/
