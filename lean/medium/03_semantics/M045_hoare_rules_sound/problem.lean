/- M045 | Hoare rules are sound | 15-20 min | Hoare logic, partial correctness, loop invariant, generalize
GOAL
  `Hoare P c Q` (partial correctness) says: from any state satisfying `P`, every terminating run
  of `c` ends in a state satisfying `Q`. Prove the assignment, sequencing, consequence and while
  rules sound, then use them to verify a countdown loop.

BANNED: try?, grind

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · hoare_assign
  1. Open the triple: states `s s'`, `hp`, the derivation `h : BigStep (.assign x a) s s'`:  R1
  2. Invert `h`: only rule `assign` ends in `.assign x a`, and it fixes the end state
     `s' := update s x (aeval s a)`:                                                    R2
  3. `hp` now has exactly the type of the goal:                                         exact hp
-/
-- BEGIN SPEC
theorem hoare_assign (Q : Assn) (x : Nat) (a : AExp) :
    Hoare (fun s => Q (update s x (aeval s a))) (.assign x a) Q :=
-- END SPEC
  sorry

/- SKELETON · hoare_seq
  1. Open the triple:                                                                   R1
  2. Invert `h`, naming the premises of rule `seq`:
       hc1 : BigStep c1 s s'✝,   hc2 : BigStep c2 s'✝ s''                              R3
  3. `h1` on `hp, hc1` gives `Q` at the middle state; `h2` on that and `hc2` gives `R s''`:
     one nested application, middle states as `_`                                       R4, R4
-/
-- BEGIN SPEC
theorem hoare_seq {P Q R : Assn} {c1 c2 : Com} (h1 : Hoare P c1 Q) (h2 : Hoare Q c2 R) :
    Hoare P (.seq c1 c2) R :=
-- END SPEC
  sorry

/- SKELETON · hoare_conseq   (a term proof; no tactic needed)
  1. The triple is a function of `s s' hp' hc`:                                         R5
  2. Its body, inside out: `hp` turns `P' s` into `P s`; `h` (with `hc`) gives `Q s'`;
     `hq` gives `Q' s'`:                                                                R4, R4, R4
-/
-- BEGIN SPEC
theorem hoare_conseq {P P' Q Q' : Assn} {c : Com} (h : Hoare P c Q) (hp : ∀ s, P' s → P s)
    (hq : ∀ s, Q s → Q' s) : Hoare P' c Q' :=
-- END SPEC
  sorry

/- SKELETON · hoare_while
  1. Open the triple: `s s'`, `hI : I s`, `h : BigStep (.while b c) s s'`:              R1
     (the new `h` hides the body triple, shown as `h✝` until step 3 consumes the derivation)
  2. `induction h` refuses the non-variable command: replace it by `w`, keeping `hw`:  R6
  3. Induct on `h` with named alternatives; `hI` moves into the IHs by itself:          R7
  4. `whileF hb`: identify the loop's guard and body with `b c`, then pair `hI, hb`:    R8, R10
  5. `whileT hb hc _ _ ih2`: identify `b c`; the body triple `h` on `⟨hI, hb⟩` and `hc`
     gives `I` at the middle state; pass it and `rfl` to `ih2`:                        R8, R4 inside R11
  6. All other rules (`| _ =>`): `hw` equates two different constructors of `Com`:      R9
-/
-- BEGIN SPEC
theorem hoare_while {I : Assn} {b : BExp} {c : Com}
    (h : Hoare (fun s => I s ∧ beval s b = true) c I) :
    Hoare I (.while b c) (fun s => I s ∧ beval s b = false) :=
-- END SPEC
  sorry

/- SKELETON · countdown_correct
  Invariant `I := fun s => 0 ≤ s 0`. Outside in, the triple is: `hoare_conseq` around
  `hoare_while` (with `I` named), whose body triple is `hoare_conseq` around `hoare_assign`.
  1. Build it with one `refine`; the two trivial consequence sides are R14, the two
     arithmetic ones are `?_`:                                                          R12, R13, R14
  2. `?_` 1, the body keeps `I`: `intro s h`, evaluate `beval`/`aeval`/`update` in `h`
     and the goal, finish:                                                              R15, R16, R18, R19
  3. `?_` 2, the exit gives `s 0 = 0`: `intro s h`, evaluate the guard in `h`, finish:  R15, R17, R19
-/
-- BEGIN SPEC
theorem countdown_correct : Hoare (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) :=
-- END SPEC
  sorry

end M045

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each rule: open `Hoare` with `intro s s' hp h` (R1) and invert the derivation `h` with `cases` (R2, R3); `hoare_conseq` needs no inversion and is a one-line term (R5). Only `hoare_while` needs an induction on the derivation, because the loop's derivation contains the same loop; `countdown_correct` never touches `BigStep`, only the four rules.
H2. `hoare_while`: `generalize hw : Com.while b c = w at h`, then `induction h with`; in `whileF`/`whileT` first `cases hw`; `whileF` is `⟨hI, hb⟩`, `whileT` applies the body triple and then the IH (its equation premise is `rfl`), and every other rule is `| _ => cases hw`. `countdown_correct`: invariant `0 ≤ s 0`; `hoare_conseq` around `hoare_while` around `hoare_conseq` around `hoare_assign`.
H3. `countdown_correct`: `refine hoare_conseq (hoare_while (I := fun s => 0 ≤ s 0) (hoare_conseq (hoare_assign _ _ _) ?_ (fun _ h => h))) (fun _ h => h) ?_`, then the body side by `intro s h; simp [beval, aeval, update] at *; omega` and the exit side by `intro s h; simp [beval, aeval] at h; omega`.
-/
