/- M046 | Sign analysis is sound | 10-15 min | abstract interpretation, concretisation, case analysis, Int sign lemmas
GOAL
  Abstractly evaluate arithmetic expressions in the sign domain {neg, zero, pos, top}. Prove it
  sound: if every variable's abstract sign describes its value, the abstract result describes
  the concrete result. `Sign.gamma a v` ("γ", concretisation) means "sign `a` describes `v`".

REFERENCE
  example (x y : Int) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := Int.mul_pos hx hy
  #check @Int.mul_neg_of_pos_of_neg   -- 0 < a → b < 0 → a * b < 0
  #check @Int.mul_neg_of_neg_of_pos   -- a < 0 → 0 < b → a * b < 0
  #check @Int.mul_pos_of_neg_of_neg   -- a < 0 → b < 0 → 0 < a * b
  example (a : Sign) : a.plus .zero = a := by cases a <;> rfl   -- `cases a`: one goal per sign
  -- `t1 <;> t2` runs t2 on every goal t1 makes.
  -- `omega` treats `x * y` as an opaque atom: it cannot find the sign of a product.
  -- `unfold Sign.ofInt; split` cases on the `if` in the goal.
BANNED: try?, grind
NOTE: `grind` is banned because `try?` prints `grind` one-liners for `plus_sound` and, given the
  two operator lemmas, for `aevalSign_sound`. Do not leave `exact?`/`apply?` in the file.
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

-- BEGIN SPEC
theorem plus_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.plus b).gamma (x + y) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem times_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.times b).gamma (x * y) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem aevalSign_sound (as : Nat → Sign) (s : State) (h : ∀ x, (as x).gamma (s x)) (e : AExp) :
    (aevalSign as e).gamma (aeval s e) :=
-- END SPEC
  sorry

end M046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The two operator lemmas are finite case analyses on the two signs (16 cases each); the main theorem is an induction on `e` that uses them, plus a small lemma for numerals.
H2. `plus_sound`: after the case split every goal is linear, so `omega` finishes. `times_sound`: the same split leaves four goals about the sign of `x * y`, which need the `Int.mul_*` lemmas. Numerals: prove `(Sign.ofInt n).gamma n` by splitting the `if`s.
H3. `cases a <;> cases b <;> simp_all [Sign.times, Sign.gamma]`, then close the four leftovers with `Int.mul_pos`, `Int.mul_pos_of_neg_of_neg`, `Int.mul_neg_of_pos_of_neg`, `Int.mul_neg_of_neg_of_pos`; main: `induction e with | num n => exact ofInt_sound n | var x => exact h x | plus a b iha ihb => exact plus_sound iha ihb | ...`.
-/
