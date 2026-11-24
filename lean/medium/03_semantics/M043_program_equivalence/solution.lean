/- M043 | Program equivalence in IMP | 15-20 min | behavioural equivalence, big-step inversion, loop unrolling, congruence
GOAL
  Two IMP commands are equivalent (`Equiv`) when they have the same big-step behaviour. Prove
  `skip; c ≈ c`, associativity of `;`, loop unrolling, that `;` respects `≈`, and `while false do c ≈ skip`.

REFERENCE
  -- IMP: expressions `AExp`/`BExp`; commands `skip`, `assign`, `seq`, `ite`, `while`.
  -- `BigStep c s s'` : running `c` from state `s` terminates in state `s'` (see also H021).
  -- `Equiv c1 c2` unfolds to `∀ s s', BigStep c1 s s' ↔ BigStep c2 s s'`; start with
  --   `intro s s'; constructor` (one goal per direction of the `↔`).
  -- Inversion: `cases h with | rule h1 h2 => …` names the premises of each rule that fits.
  example (x : Nat) (a : M043.AExp) (s s' : M043.State) (h : M043.BigStep (.assign x a) s s') :
      s' = M043.update s x (M043.aeval s a) := by
    cases h with
    | assign => rfl
  -- Rules build derivations: `.iteT hb (.seq hc hw) : BigStep (.ite b (.seq c w) c2) s s''`
  -- `simp [beval] at hb` turns `hb : beval s .ff = true` into `False`, closing the goal.
-/

namespace M043

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

/-- Behavioural equivalence: same final states from every initial state. -/
def Equiv (c1 c2 : Com) : Prop := ∀ s s', BigStep c1 s s' ↔ BigStep c2 s s'
-- END SPEC

-- BEGIN SPEC
theorem skip_seq (c : Com) : Equiv (.seq .skip c) c :=
-- END SPEC
  by
    intro s s'
    constructor
    · intro h
      cases h with
      | seq hs hc => cases hs; exact hc
    · intro h
      exact .seq .skip h

-- BEGIN SPEC
theorem seq_assoc (c1 c2 c3 : Com) : Equiv (.seq (.seq c1 c2) c3) (.seq c1 (.seq c2 c3)) :=
-- END SPEC
  by
    intro s s'
    constructor
    · intro h
      cases h with
      | seq h12 h3 =>
        cases h12 with
        | seq h1 h2 => exact .seq h1 (.seq h2 h3)
    · intro h
      cases h with
      | seq h1 h23 =>
        cases h23 with
        | seq h2 h3 => exact .seq (.seq h1 h2) h3

-- BEGIN SPEC
theorem while_unroll (b : BExp) (c : Com) :
    Equiv (.while b c) (.ite b (.seq c (.while b c)) .skip) :=
-- END SPEC
  by
    intro s s'
    constructor
    · intro h
      cases h with
      | whileF hb => exact .iteF hb .skip
      | whileT hb hc hw => exact .iteT hb (.seq hc hw)
    · intro h
      cases h with
      | iteT hb h =>
        cases h with
        | seq hc hw => exact .whileT hb hc hw
      | iteF hb h =>
        cases h
        exact .whileF hb

-- BEGIN SPEC
theorem seq_congr {c1 c1' c2 c2' : Com} (h1 : Equiv c1 c1') (h2 : Equiv c2 c2') :
    Equiv (.seq c1 c2) (.seq c1' c2') :=
-- END SPEC
  by
    intro s s'
    constructor
    · intro h
      cases h with
      | seq ha hb => exact .seq ((h1 _ _).mp ha) ((h2 _ _).mp hb)
    · intro h
      cases h with
      | seq ha hb => exact .seq ((h1 _ _).mpr ha) ((h2 _ _).mpr hb)

-- BEGIN SPEC
theorem while_false (c : Com) : Equiv (.while .ff c) .skip :=
-- END SPEC
  by
    intro s s'
    constructor
    · intro h
      cases h with
      | whileF _ => exact .skip
      | whileT hb _ _ => simp [beval] at hb
    · intro h
      cases h
      exact .whileF rfl

end M043

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every proof has the same shape: in each direction, invert the derivation you are given
    (`cases`, sometimes twice for nested commands) and rebuild one for the other command from the rules.
H2. `while_unroll` (→): a `while` derivation ends with `whileF` (use `iteF` and `skip`) or `whileT`
    (use `iteT` and `seq`). (←): invert the `ite`, then the `seq` or `skip` inside it.
    `seq_congr`: apply `(h1 s s').mp` / `.mpr` to the inverted premises.
H3. `while_unroll` (→): `cases h with | whileF hb => exact .iteF hb .skip | whileT hb hc hw => exact .iteT hb (.seq hc hw)`.
    `while_false` (→): the `whileT` case has `hb : beval s .ff = true`; `simp [beval] at hb`.
-/
