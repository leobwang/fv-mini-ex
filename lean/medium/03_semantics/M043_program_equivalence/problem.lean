/- M043 | Program equivalence in IMP | 15-20 min | behavioural equivalence, big-step inversion, loop unrolling, congruence
GOAL
  Two IMP commands are equivalent (`Equiv`) when they have the same big-step behaviour. Prove
  `skip; c ≈ c`, associativity of `;`, loop unrolling, that `;` respects `≈`, and `while false do c ≈ skip`.

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · skip_seq
  1. Unfold `Equiv` and fix the two states:                                R1
  2. Split the `↔`, then `intro h` in each goal:                            R2
  3. (→) invert the `seq` derivation, then the `skip` premise (its two
     states become one), then use the `c` premise:                          R3 → R4, exact
  4. (←) build `skip; c` from a `skip` derivation and `h`:                  R6
-/
-- BEGIN SPEC
theorem skip_seq (c : Com) : Equiv (.seq .skip c) c :=
-- END SPEC
  sorry

/- SKELETON · seq_assoc
  1. Unfold `Equiv`, split the `↔`, `intro h` in each goal:                 R1, R2
  2. (→) invert the outer `seq`, then the inner one held by its first
     premise; rebuild with nested rules `seq _ (seq _ _)`:                  R3 → R3 → R6
  3. (←) the mirror image: invert the outer `seq`, then its second
     premise; rebuild `seq (seq _ _) _`:                                    R3 → R3 → R6
-/
-- BEGIN SPEC
theorem seq_assoc (c1 c2 c3 : Com) : Equiv (.seq (.seq c1 c2) c3) (.seq c1 (.seq c2 c3)) :=
-- END SPEC
  sorry

/- SKELETON · while_unroll
  1. Unfold `Equiv`, split the `↔`, `intro h` in each goal:                 R1, R2
  2. (→) a `while` derivation ends with `whileF` or `whileT`:               R5
       whileF: guard false → the `else` branch, a `skip`:                  R6 (iteF, skip)
       whileT: guard true → the `then` branch, a `seq`:                    R6 (iteT, seq)
  3. (←) an `ite` derivation ends with `iteT` or `iteF`:                    R5
       iteT: invert its `seq` premise, then rebuild with `whileT`:         R3 → R6
       iteF: invert its `skip` premise, then rebuild with `whileF`:        R4 → R6
-/
-- BEGIN SPEC
theorem while_unroll (b : BExp) (c : Com) :
    Equiv (.while b c) (.ite b (.seq c (.while b c)) .skip) :=
-- END SPEC
  sorry

/- SKELETON · seq_congr
  1. Unfold `Equiv`, split the `↔`, `intro h` in each goal:                 R1, R2
  2. (→) invert the `seq`; rebuild it from the two premises carried
     across `h1` and `h2` from left to right:                               R3 → R6 with R7
  3. (←) the same with the `↔` used right to left:                          R3 → R6 with R8
-/
-- BEGIN SPEC
theorem seq_congr {c1 c1' c2 c2' : Com} (h1 : Equiv c1 c1') (h2 : Equiv c2 c2') :
    Equiv (.seq c1 c2) (.seq c1' c2') :=
-- END SPEC
  sorry

/- SKELETON · while_false
  1. Unfold `Equiv`, split the `↔`, `intro h` in each goal:                 R1, R2
  2. (→) invert the `while`:                                                R5
       whileF: the states are already equal; build `skip`:                 R6
       whileT: its guard premise says `beval s .ff = true`, impossible:    R9
  3. (←) invert the `skip` (states become one), then build `whileF`,
     proving its guard premise by computation:                              R4 → R6 with R10
-/
-- BEGIN SPEC
theorem while_false (c : Com) : Equiv (.while .ff c) .skip :=
-- END SPEC
  sorry

end M043

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every proof has the same shape: `intro s s'` (R1), `constructor` (R2), and in each direction invert
    the derivation you are given with `cases` (R3–R5, twice for nested commands) and rebuild one for the
    other command from the rules (R6).
H2. `while_unroll` (→): a `while` derivation ends with `whileF` (rebuild with `iteF` and `skip`) or
    `whileT` (rebuild with `iteT` and `seq`). (←): invert the `ite`, then the `seq` or `skip` inside it.
    `seq_congr`: carry each premise across with `(h1 _ _).mp` / `(h2 _ _).mp` (R7), `.mpr` backwards (R8).
    `while_false`: the `whileT` case is impossible (R9); the `←` direction needs `.whileF rfl` (R10).
H3. `while_unroll` (→): `cases h with | whileF hb => exact .iteF hb .skip | whileT hb hc hw => exact .iteT hb (.seq hc hw)`.
    `while_false` (→): the `whileT` case has `hb : beval s .ff = true`; `simp [beval] at hb`.
-/
