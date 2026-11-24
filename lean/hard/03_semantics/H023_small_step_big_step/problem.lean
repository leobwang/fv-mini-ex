/- H023 | Small-step and big-step IMP agree | 1-1.5 h | small-step semantics, configurations, Star, induction on derivations, generalize
GOAL
  For IMP (H021's language, with `times` in place of `minus`), a big-step run `BigStep c s s'`
  exists iff the small-step semantics reaches the configuration `(skip, s')` from `(c, s)`.

REFERENCE
  -- A configuration is a pair `(c, s) : Com × State`; `Star` is the reflexive-transitive closure of `SmallStep`.
  example (s : H023.State) : H023.Star (.seq .skip .skip, s) (.skip, s) := .step .seqSkip (.refl _)
  -- `induction h` on `h : Star (c, s) (.skip, s')` fails: the indices are pairs, not variables.
  -- Generalize BOTH pairs (one alone still fails), then induct:
  example (c : H023.Com) (s s' : H023.State) (h : H023.Star (c, s) (.skip, s')) : True := by
    generalize hp : (c, s) = p at h; generalize hq : (H023.Com.skip, s') = q at h
    induction h generalizing c s <;> trivial
  -- NOTE: inside `generalize` write `Com.skip`, not `.skip`: there is no expected type to resolve `.skip`.
  -- `cases hp` on `hp : (c, s) = (c', s')` substitutes both components.
  -- `| @step _ q _ st _ ih =>` names the implicit middle configuration `q` of a `Star.step`;
  -- `obtain ⟨c', t⟩ := q` then splits it into command and state.
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

-- MILESTONE (optional: change or delete)
theorem star_trans {p q r : Com × State} (h1 : Star p q) (h2 : Star q r) : Star p r := by
  sorry

-- MILESTONE (optional: change or delete)
theorem star_seq {c1 c1' c2 : Com} {s s' : State} (h : Star (c1, s) (c1', s')) :
    Star (.seq c1 c2, s) (.seq c1' c2, s') := by
  sorry

-- MILESTONE (optional: change or delete)
theorem step_then_big {c c' : Com} {s s' t : State} (h1 : SmallStep (c, s) (c', s'))
    (h2 : BigStep c' s' t) : BigStep c s t := by
  sorry

-- BEGIN SPEC
theorem big_to_small {c : Com} {s s' : State} (h : BigStep c s s') : Star (c, s) (.skip, s') :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem small_to_big {c : Com} {s s' : State} (h : Star (c, s) (.skip, s')) : BigStep c s s' :=
-- END SPEC
  sorry

end H023

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Big to small: induction on the `BigStep` derivation; `seq` and `whileT` need to run a whole sub-derivation inside `seq _ c2`. Small to big: induction on `Star`, pushing one small step backwards through a big-step run.
H2. Prove `star_trans` (induction on `h1`) and `star_seq` (generalize both configurations, induction on the `Star`, wrap each step in `.seqStep`). `step_then_big`: induction on the generalized small step, then `cases h2` where the target is compound.
H3. `whileT` case: `.step .whileUnfold (.step (.iteT hb) (star_trans (star_seq ih1) (.step .seqSkip ih2)))`. `whileUnfold` case of `step_then_big`: `cases h2 with | iteT hb h => cases h with | seq h1 h2 => exact .whileT hb h1 h2 | iteF hb h => cases h; exact .whileF hb`.
-/
