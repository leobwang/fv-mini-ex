/- H025 | An abstract interpreter for IMP | 1.5-2 h | abstract interpretation, sign domain, join, post-fixpoint, Kleene iteration, induction on commands
GOAL
  Lift M046's sign analysis to whole IMP programs. `aexec c st` runs `c` on an abstract state `st`
  (a list of signs, one per variable): `ite` joins both branches, `while` iterates until stable.
  Prove it sound: if `st` describes the start state of a terminating run, `aexec c st` describes the end.

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H025

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

inductive Sign where
  | neg
  | zero
  | pos
  | top
  deriving DecidableEq

/-- Concretisation: which integers a sign describes. -/
def Sign.gamma : Sign → Int → Prop
  | .neg, v => v < 0
  | .zero, v => v = 0
  | .pos, v => 0 < v
  | .top, _ => True

/-- Least upper bound in the flat lattice `neg, zero, pos ⊑ top`. -/
def Sign.join (a b : Sign) : Sign := if a = b then a else .top

def Sign.ofInt (n : Int) : Sign := if n < 0 then .neg else if n = 0 then .zero else .pos

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

/-- Abstract state: entry `x` is the sign of variable `x`; missing entries mean `top`. -/
abbrev AState := List Sign

def lookup : AState → Nat → Sign
  | [], _ => .top
  | a :: _, 0 => a
  | _ :: as, n + 1 => lookup as n

def aupdate : AState → Nat → Sign → AState
  | [], _, _ => []
  | _ :: as, 0, v => v :: as
  | a :: as, n + 1, v => a :: aupdate as n v

def ajoin : AState → AState → AState
  | a :: as, b :: bs => a.join b :: ajoin as bs
  | _, _ => []

def aevalSign (st : AState) : AExp → Sign
  | .num n => Sign.ofInt n
  | .var x => lookup st x
  | .plus a b => (aevalSign st a).plus (aevalSign st b)
  | .times a b => (aevalSign st a).times (aevalSign st b)

/-- Kleene iteration of `x ↦ ajoin init (f x)`, giving up (all `top`, i.e. `[]`) when fuel runs out. -/
def iterate (f : AState → AState) (init : AState) : Nat → AState → AState
  | 0, _ => []
  | k + 1, x =>
    let x' := ajoin init (f x)
    if x' = x then x else iterate f init k x'

def aexec : Com → AState → AState
  | .skip, st => st
  | .assign x a, st => aupdate st x (aevalSign st a)
  | .seq c1 c2, st => aexec c2 (aexec c1 st)
  | .ite _ c1 c2, st => ajoin (aexec c1 st) (aexec c2 st)
  | .while _ c, st => iterate (aexec c) st 10 st

/-- A concrete state is described by an abstract one. -/
def Approx (st : AState) (s : State) : Prop := ∀ x, (lookup st x).gamma (s x)
-- END SPEC

theorem plus_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.plus b).gamma (x + y) := by
  cases a <;> cases b <;> simp_all [Sign.plus, Sign.gamma] <;> omega

theorem times_sound {a b : Sign} {x y : Int} (ha : a.gamma x) (hb : b.gamma y) :
    (a.times b).gamma (x * y) := by
  cases a <;> cases b <;> simp_all [Sign.times, Sign.gamma]
  · exact Int.mul_pos_of_neg_of_neg ha hb
  · exact Int.mul_neg_of_neg_of_pos ha hb
  · exact Int.mul_neg_of_pos_of_neg ha hb
  · exact Int.mul_pos ha hb

theorem ofInt_sound (n : Int) : (Sign.ofInt n).gamma n := by
  unfold Sign.ofInt
  split
  · simp_all [Sign.gamma]
  · split <;> simp_all [Sign.gamma] <;> omega

-- MILESTONE (optional: change or delete)
/- SKELETON · aeval_sound
  0. Add three helpers above it first (they are the M046 lemmas):
       plus_sound  : a.gamma x → b.gamma y → (a.plus b).gamma (x + y)
         all 16 sign pairs, unfold `Sign.plus` and `Sign.gamma`, arithmetic       R1, R2, R3
       times_sound : the same for `Sign.times` and `x * y`
         R1, R2; four goals are left, in the order neg·neg, neg·pos, pos·neg, pos·pos: R5, R7, R6, R4
       ofInt_sound : (Sign.ofInt n).gamma n
         unfold, split the outer `if`, then the inner one; simp_all, omega        R8, R9, R2, R3
  1. Induct on `e`; each of the four cases is one `exact` with a helper, or `h x`  R11
-/
theorem aeval_sound (st : AState) (s : State) (h : Approx st s) (e : AExp) :
    (aevalSign st e).gamma (aeval s e) := by
  induction e with
  | num n => exact ofInt_sound n
  | var x => exact h x
  | plus a b iha ihb => exact plus_sound iha ihb
  | times a b iha ihb => exact times_sound iha ihb

theorem join_left {a b : Sign} {v : Int} (h : a.gamma v) : (a.join b).gamma v := by
  unfold Sign.join; split <;> simp_all [Sign.gamma]

theorem join_right {a b : Sign} {v : Int} (h : b.gamma v) : (a.join b).gamma v := by
  unfold Sign.join; split <;> simp_all [Sign.gamma]

-- MILESTONE (optional: change or delete)
/- SKELETON · lookup_ajoin_left   (lookup_ajoin_right: the same, with join_right)
  0. Helpers above it: join_left : a.gamma v → (a.join b).gamma v, and join_right
       unfold `Sign.join`, split, then simp_all with `Sign.gamma`                 R8, R9, R2
  1. Induct on `p`, generalizing `q x` (the recursion moves both)                  R12
  2. p = []: `ajoin` gives [], `lookup` gives top, `Sign.gamma .top v` is True     R15
  3. p = a :: as: split `q`; q = [] as in step 2                                   R13, R15
  4. both cons: split `x`; zero → join_left; succ n → the IH at `bs` and `n`       R14
-/
theorem lookup_ajoin_left (p q : AState) (x : Nat) (v : Int) (h : (lookup p x).gamma v) :
    (lookup (ajoin p q) x).gamma v := by
  induction p generalizing q x with
  | nil => simp [ajoin, lookup, Sign.gamma]
  | cons a as ih =>
    cases q with
    | nil => simp [ajoin, lookup, Sign.gamma]
    | cons b bs =>
      cases x with
      | zero => exact join_left h
      | succ n => exact ih bs n h

theorem lookup_ajoin_right (p q : AState) (x : Nat) (v : Int) (h : (lookup q x).gamma v) :
    (lookup (ajoin p q) x).gamma v := by
  induction p generalizing q x with
  | nil => simp [ajoin, lookup, Sign.gamma]
  | cons a as ih =>
    cases q with
    | nil => simp [ajoin, lookup, Sign.gamma]
    | cons b bs =>
      cases x with
      | zero => exact join_right h
      | succ n => exact ih bs n h

-- MILESTONE (optional: change or delete)
-- WHY: an `aupdate` past the end of the list is a no-op, which is still sound: the entry stays `top`.
/- SKELETON · approx_aupdate
  1. `Approx` is a `∀`: introduce the variable `y` to check                        R16
  2. Induct on `st`, generalizing `x y s`; st = []: compute                        R12, R15
  3. st = b :: bs: split `x`, then `y`                                             R14
  4. the three cases with a `0`: simplify and close with hv, h (m + 1) or h 0      R18
  5. succ n / succ m: the IH at the shifted state `fun k => s (k + 1)`, whose
     description is `fun k => h (k + 1)`; then simplify it into the goal           R17 → R18
-/
theorem approx_aupdate (st : AState) (s : State) (h : Approx st s) (x : Nat) (a : Sign) (v : Int)
    (hv : a.gamma v) : Approx (aupdate st x a) (update s x v) := by
  intro y
  induction st generalizing x y s with
  | nil => simp [aupdate, lookup, Sign.gamma]
  | cons b bs ih =>
    cases x with
    | zero =>
      cases y with
      | zero => simpa [aupdate, lookup, update] using hv
      | succ m => simpa [aupdate, lookup, update] using h (m + 1)
    | succ n =>
      cases y with
      | zero => simpa [aupdate, lookup, update] using h 0
      | succ m =>
        have := ih (fun k => s (k + 1)) (fun k => h (k + 1)) n m
        simpa [aupdate, lookup, update] using this

-- MILESTONE (optional: change or delete)
/-- `Le p q` (`p ⊑ q`): every concrete state described by `p` is described by `q`. -/
def Le (p q : AState) : Prop := ∀ s, Approx p s → Approx q s

/- SKELETON · iterate_post
  1. Induct on the fuel `k`, generalizing `x` (cases `zero`, `succ k ih`)          R12
  2. zero: the result is `[]`; each part: introduce s, hs, y, then compute         R16, R15
  3. succ: unfold one round, split on the stability test, name it `heq`           R19, R9, R10
       stable, heq : ajoin init (f x) = x: give `hx`, open the second part,
         rewrite the goal's `x` back with ← heq, then lookup_ajoin_right          R20, rw [← heq]
       not stable: the IH at `ajoin init (f x)`; its argument `init ⊑ ajoin init (f x)`
         is `fun s hs y => …` (R16 in term mode) closed by lookup_ajoin_left      R16
-/
theorem iterate_post (f : AState → AState) (init : AState) (k : Nat) (x : AState)
    (hx : Le init x) : Le init (iterate f init k x) ∧
      Le (f (iterate f init k x)) (iterate f init k x) := by
  induction k generalizing x with
  | zero =>
    exact ⟨fun _ _ y => by simp [iterate, lookup, Sign.gamma],
      fun _ _ y => by simp [iterate, lookup, Sign.gamma]⟩
  | succ k ih =>
    simp only [iterate]
    split
    next heq =>
      refine ⟨hx, fun s hs y => ?_⟩
      rw [← heq]
      exact lookup_ajoin_right _ _ y _ (hs y)
    next => exact ih _ (fun s hs y => lookup_ajoin_left _ _ y _ (hs y))

-- MILESTONE (optional: change or delete)
/- SKELETON · while_inv
  1. Replace the command `Com.while b c` in `h` by a variable `w`, keeping hw      R21
  2. Induct on the run `h`; name whileF and whileT, catch the rest with `_`       R22
       whileF: the end state is the start state
       whileT: substitute the equation (R24); ih2 needs `Approx I` of the state
         after one body run: hc on that run, then hI; and the equation (rfl)
       the other five rules: hw equates different constructors                  R23
-/
theorem while_inv {b : BExp} {c : Com} (I : AState)
    (hc : ∀ st s s', BigStep c s s' → Approx st s → Approx (aexec c st) s')
    (hI : Le (aexec c I) I) {s s' : State} (h : BigStep (.while b c) s s') (hs : Approx I s) :
    Approx I s' := by
  generalize hw : Com.while b c = w at h
  induction h with
  | whileF => exact hs
  | whileT _ h1 _ _ ih2 =>
    cases hw
    exact ih2 (hI _ (hc _ _ _ h1 hs)) rfl
  | _ => cases hw

/- SKELETON · aexec_sound
  Prove the milestones first, in this order. Where each one is used:
    aeval_sound (Part 1)                         step 3
    lookup_ajoin_left, lookup_ajoin_right (2)    step 5, and inside iterate_post
    approx_aupdate (3)                           step 3
    iterate_post (4), while_inv (5)              step 6
  1. Induct on the command, generalizing `s s' st` (the IH must hold for every
     run of the body and every abstract state); the last case is «while»          R11, R12
  2. skip:   invert `h` (the end state is the start state), then hs              R25
  3. assign: invert `h`; approx_aupdate, its `hv` from aeval_sound                R25
  4. seq:    invert `h` into two runs; the IH for c1, then the IH for c2 on it   R25
  5. ite:    invert `h` into iteT / iteF; the IH for the branch taken, then
             lookup_ajoin_left / _right for each variable (`fun y => …`)          R25, R16
  6. while:  iterate_post (aexec c) st 10 st (its `hx : st ⊑ st` is `fun _ h => h`)
             gives, for I := iterate (aexec c) st 10 st, st ⊑ I and aexec c I ⊑ I;
             then while_inv, its `hc` built from ih (reorder: `fun st s s' h hs => …`)
-/
-- BEGIN SPEC
theorem aexec_sound {c : Com} {s s' : State} (h : BigStep c s s') (st : AState)
    (hs : Approx st s) : Approx (aexec c st) s' :=
-- END SPEC
  by
    induction c generalizing s s' st with
    | skip => cases h; exact hs
    | assign x a => cases h; exact approx_aupdate st s hs x _ _ (aeval_sound st s hs a)
    | seq c1 c2 ih1 ih2 => cases h with | seq h1 h2 => exact ih2 h2 _ (ih1 h1 _ hs)
    | ite b c1 c2 ih1 ih2 =>
      cases h with
      | iteT _ h1 => exact fun y => lookup_ajoin_left _ _ y _ (ih1 h1 _ hs y)
      | iteF _ h2 => exact fun y => lookup_ajoin_right _ _ y _ (ih2 h2 _ hs y)
    | «while» b c ih =>
      -- WHY: the IH must hold for every run and every abstract state, hence `generalizing s s' st`.
      have hp := iterate_post (aexec c) st 10 st (fun _ h => h)
      exact while_inv _ (fun st s s' h hs => ih h st hs) hp.2 h (hp.1 _ hs)

end H025

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three layers, one milestone group each: expressions (Part 1), the list operations `lookup` after
    `ajoin` / `aupdate` (Parts 2, 3), and commands (Parts 4–6). Every case of `aexec_sound` but `while`
    is "invert the run, apply the IHs and one milestone". For `while` you need an abstract state `I`
    that is stable under the body (`aexec c I ⊑ I`): `iterate_post` finds one, `while_inv` shows it holds
    after every run of the loop.
H2. Induct on what the recursion walks, generalizing every argument that changes in the recursive call:
    `induction e` (Part 1); `induction p generalizing q x`, then `cases q`, `cases x` (Part 2);
    `intro y; induction st generalizing x y s`, then `cases x`, `cases y` (Part 3; the tail describes the
    shifted state `fun k => s (k + 1)`); `induction k generalizing x` (Part 4; in the stable branch
    `x = ajoin init (f x)`, so `f x ⊑ x` by `lookup_ajoin_right`); `generalize hw : Com.while b c = w at h`,
    then `induction h` (Part 5); `induction c generalizing s s' st` and `cases h` (Part 6).
H3. `while` case: `have hp := iterate_post (aexec c) st 10 st (fun _ h => h)` then
    `exact while_inv _ (fun st s s' h hs => ih h st hs) hp.2 h (hp.1 _ hs)`.
    `approx_aupdate`, `succ n` / `succ m`: `have := ih (fun k => s (k + 1)) (fun k => h (k + 1)) n m`, then
    `simpa [aupdate, lookup, update] using this`. Head case of `lookup_ajoin_left`: `unfold Sign.join; split`.
-/
