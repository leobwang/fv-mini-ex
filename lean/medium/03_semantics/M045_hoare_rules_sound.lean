/- M045 | Hoare rules are sound | 15-20 min | Hoare logic, partial correctness, loop invariant, generalize
GOAL
  `Hoare P c Q` (partial correctness) says: from any state satisfying `P`, every terminating run
  of `c` ends in a state satisfying `Q`. Prove the assignment, sequencing, consequence and while
  rules sound, then use them to verify a countdown loop.

REFERENCE
  -- IMP: arithmetic `AExp`, boolean `BExp`, commands `Com`; `update s x v` sets variable `x` to `v`;
  -- `BigStep c s s'` means: running `c` from state `s` terminates in state `s'`.
  -- `Assn := State → Prop` is an assertion about states.
  -- `intro s s' hp h; cases h` inverts a derivation of a non-loop command.
  -- `induction h` fails on `h : BigStep (.while b c) s s'` (the command is not a variable):
  example (b : BExp) (c : Com) (s s' : State) (h : BigStep (.while b c) s s') : True := by
    generalize hw : Com.while b c = w at h   -- now `induction h`; `hw` remembers the shape
    trivial
  -- in the `whileT` case `cases hw` identifies `b` and `c`; `injection`/`cases hw` kills the rest.
  example (s : State) : update s 0 5 0 = 5 := by simp [update]
  example (s : State) : beval s (.le (.var 0) (.num 0)) = decide (s 0 ≤ 0) := by simp [beval, aeval]
BANNED: try?, grind
NOTE: `grind` is banned because `try?` prints a `grind [= Hoare]` one-liner for `hoare_conseq`.
  Do not leave search tactics (`exact?`, `apply?`) in the file.
-/

namespace M045

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

abbrev Assn := State → Prop

/-- Partial correctness: from a P-state, every terminating run ends in a Q-state. -/
def Hoare (P : Assn) (c : Com) (Q : Assn) : Prop := ∀ s s', P s → BigStep c s s' → Q s'

/-- `while 0 < x0 do x0 := x0 + (-1)`, written with `not (x0 ≤ 0)`. -/
def countdown : Com :=
  .while (.not (.le (.var 0) (.num 0))) (.assign 0 (.plus (.var 0) (.num (-1))))
-- END SPEC

-- BEGIN SPEC
theorem hoare_assign (Q : Assn) (x : Nat) (a : AExp) :
    Hoare (fun s => Q (update s x (aeval s a))) (.assign x a) Q :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hoare_seq {P Q R : Assn} {c1 c2 : Com} (h1 : Hoare P c1 Q) (h2 : Hoare Q c2 R) :
    Hoare P (.seq c1 c2) R :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hoare_conseq {P P' Q Q' : Assn} {c : Com} (h : Hoare P c Q) (hp : ∀ s, P' s → P s)
    (hq : ∀ s, Q s → Q' s) : Hoare P' c Q' :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hoare_while {I : Assn} {b : BExp} {c : Com}
    (h : Hoare (fun s => I s ∧ beval s b = true) c I) :
    Hoare I (.while b c) (fun s => I s ∧ beval s b = false) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem countdown_correct : Hoare (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) :=
-- END SPEC
  sorry

end M045

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `Hoare` (`intro s s' hp h`) and invert the derivation `h`. Only the while rule needs an induction, on the derivation, because the loop's own derivation appears inside it.
H2. `hoare_while`: `generalize hw : Com.while b c = w at h`, then `induction h`; `whileF` gives `⟨hI, hb⟩`, `whileT` uses the body triple and then the IH, and every other rule contradicts `hw`. `countdown_correct`: invariant `0 ≤ s 0`; combine `hoare_conseq`, `hoare_while` and `hoare_assign`.
H3. `countdown_correct`: `refine hoare_conseq (hoare_while (I := fun s => 0 ≤ s 0) (hoare_conseq (hoare_assign _ _ _) ?_ (fun _ h => h))) (fun _ h => h) ?_`, then each side condition by `intro s h; simp [beval, aeval, update] at *; omega`.
-/
