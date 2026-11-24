/- M046 | Sign analysis is sound | 10-15 min | abstract interpretation, concretisation, case analysis, Int sign lemmas
GOAL
  Abstractly evaluate arithmetic expressions in the sign domain {neg, zero, pos, top}. Prove it
  sound: if every variable's abstract sign describes its value, the abstract result describes
  the concrete result. `Sign.gamma a v` ("γ", concretisation) means "sign `a` describes `v`".

BANNED: try?, grind

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M046

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

inductive Sign where
  | neg
  | zero
  | pos
  | top

/-- Concretisation: which integers a sign describes. -/
def Sign.gamma : Sign → Int → Prop
  | .neg, v => v < 0
  | .zero, v => v = 0
  | .pos, v => 0 < v
  | .top, _ => True

def Sign.ofInt (n : Int) : Sign :=
  if n < 0 then .neg else if n = 0 then .zero else .pos

def Sign.plus : Sign → Sign → Sign
  | .zero, s => s
  | s, .zero => s
  | .pos, .pos => .pos
  | .neg, .neg => .neg
  | _, _ => .top

def Sign.times : Sign → Sign → Sign
  | .zero, _ => .zero
  | _, .zero => .zero
  | .pos, .pos => .pos
  | .neg, .neg => .pos
  | .pos, .neg => .neg
  | .neg, .pos => .neg
  | _, _ => .top

/-- Abstract evaluation over an abstract state. -/
def aevalSign (as : Nat → Sign) : AExp → Sign
  | .num n => Sign.ofInt n
  | .var x => as x
  | .plus a b => (aevalSign as a).plus (aevalSign as b)
  | .times a b => (aevalSign as a).times (aevalSign as b)
-- END SPEC

/- SKELETON · plus_sound
  1. One goal per pair of signs, 4 × 4 = 16 goals:                           R1, R2
  2. In every goal evaluate `Sign.plus` on the two constructors and turn
     each `gamma` into an (in)equality, in `ha`, `hb` and the goal at once.
     14 goals close here (`top` gives `True`, `zero` gives `x = 0`):          R3, R4
  3. Two goals are left, `neg.neg` and `pos.pos`; both are linear:           R5
     (chain steps 1–3 with `<;>` so each runs on every goal)
-/
-- BEGIN SPEC
theorem plus_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.plus b).gamma (x + y) :=
-- END SPEC
  sorry

/- SKELETON · times_sound
  1. One goal per pair of signs:                                             R2
  2. Evaluate `Sign.times` and `gamma` everywhere; 12 goals close:           R3, R4
  3. Four goals about the sign of `x * y` are left, in the order
     `neg.neg`, `neg.pos`, `pos.neg`, `pos.pos`. `omega` cannot see inside
     `x * y`; close each (one `·` bullet per goal) with its lemma on `ha hb`: R7, R9, R8, R6
-/
-- BEGIN SPEC
theorem times_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.times b).gamma (x * y) :=
-- END SPEC
  sorry

/- SKELETON · aevalSign_sound
  0. MILESTONE first: your own lemma, declared above this theorem and outside the spec regions,
       ofInt_sound (n : Int) : (Sign.ofInt n).gamma n            (used in the `num` case)
     Open `Sign.ofInt`, split the outer `if`; the `isTrue` branch by R4; in `isFalse`
     split the inner `if` and finish each branch with R4, then R5:      R10 → R11 → R4, R11 → R4 → R5
  1. Induction on `e`, naming the constructor arguments and the IHs of `plus`, `times`:  R12
  2. Each of the four alternatives is one `exact`, up to unfolding:                      R13
       num → the milestone,  var → the hypothesis `h`,
       plus / times → the operator lemma of Part 1 / 2 applied to the two IHs
-/
-- BEGIN SPEC
theorem aevalSign_sound (as : Nat → Sign) (s : State) (h : ∀ x, (as x).gamma (s x)) (e : AExp) :
    (aevalSign as e).gamma (aeval s e) :=
-- END SPEC
  sorry

end M046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The two operator lemmas are finite tables: split both signs (16 cases each) and let `simp_all`
    unfold the table and `gamma` (R1–R4). The main theorem is an induction on `e` (R12) that uses
    them, plus a milestone lemma for numerals.
H2. `plus_sound`: after `cases a <;> cases b <;> simp_all [Sign.plus, Sign.gamma]` every leftover is
    linear, so `<;> omega` (R5). `times_sound`: the same split leaves four goals about the sign of
    `x * y`, which `omega` cannot see; use the `Int.mul_*` lemmas (R6–R9). Milestone
    `ofInt_sound (n : Int) : (Sign.ofInt n).gamma n`: `unfold Sign.ofInt`, `split` (twice), then
    `simp_all [Sign.gamma]` and `omega` (R10, R11, R4, R5).
H3. `times_sound`: `cases a <;> cases b <;> simp_all [Sign.times, Sign.gamma]`, then
    `· exact Int.mul_pos_of_neg_of_neg ha hb`, `· exact Int.mul_neg_of_neg_of_pos ha hb`,
    `· exact Int.mul_neg_of_pos_of_neg ha hb`, `· exact Int.mul_pos ha hb`. Main:
    `induction e with | num n => exact ofInt_sound n | var x => exact h x | plus a b iha ihb => exact plus_sound iha ihb | ...`.
-/
