/- H025 | An abstract interpreter for IMP | 1.5-2 h | abstract interpretation, sign domain, join, post-fixpoint, Kleene iteration, induction on commands
GOAL
  Lift M046's sign analysis to whole IMP programs. `aexec c st` runs `c` on an abstract state `st`
  (a list of signs, one per variable): `ite` joins both branches, `while` iterates until stable.
  Prove it sound: if `st` describes the start state of a terminating run, `aexec c st` describes the end.

REFERENCE
  -- `Approx st s`: every variable's sign in `st` describes its value in `s` (`Sign.gamma`, as in M046).
  example : H025.lookup [] 5 = .top := rfl   -- missing entries are `top`, so `[]` describes every state
  example : H025.ajoin [.pos, .neg] [.pos, .zero] = [.pos, .top] := rfl   -- pointwise join, cut to the shorter
  #check @Int.mul_pos_of_neg_of_neg   -- a < 0 → b < 0 → 0 < a * b
  -- siblings for the other sign cases: Int.mul_pos, Int.mul_neg_of_pos_of_neg, Int.mul_neg_of_neg_of_pos
  example (x y : H025.AState) : (if x = y then x else y) = y := by
    split <;> simp_all   -- `split` cases on the `if` in the goal; `next heq => ..` names the condition
  -- `induction c generalizing s s' st with | ... | «while» b c ih => ..` (`while` is a keyword).
  -- Before inducting on `h : BigStep (.while b c) s s'`: `generalize hw : Com.while b c = w at h`.
  -- Inversion: `cases h with | iteT hb h1 => .. | iteF hb h2 => ..` on `h : BigStep (.ite b c1 c2) s s'`.
NOTE: Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file.
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

-- MILESTONE (optional: change or delete)
theorem aeval_sound (st : AState) (s : State) (h : Approx st s) (e : AExp) :
    (aevalSign st e).gamma (aeval s e) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem lookup_ajoin_left (p q : AState) (x : Nat) (v : Int) (h : (lookup p x).gamma v) :
    (lookup (ajoin p q) x).gamma v := by
  sorry

theorem lookup_ajoin_right (p q : AState) (x : Nat) (v : Int) (h : (lookup q x).gamma v) :
    (lookup (ajoin p q) x).gamma v := by
  sorry

-- MILESTONE (optional: change or delete)
theorem approx_aupdate (st : AState) (s : State) (h : Approx st s) (x : Nat) (a : Sign) (v : Int)
    (hv : a.gamma v) : Approx (aupdate st x a) (update s x v) := by
  sorry

-- MILESTONE (optional: change or delete)
/-- `Le p q` (`p ⊑ q`): every concrete state described by `p` is described by `q`. -/
def Le (p q : AState) : Prop := ∀ s, Approx p s → Approx q s

theorem iterate_post (f : AState → AState) (init : AState) (k : Nat) (x : AState)
    (hx : Le init x) : Le init (iterate f init k x) ∧
      Le (f (iterate f init k x)) (iterate f init k x) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem while_inv {b : BExp} {c : Com} (I : AState)
    (hc : ∀ st s s', BigStep c s s' → Approx st s → Approx (aexec c st) s')
    (hI : Le (aexec c I) I) {s s' : State} (h : BigStep (.while b c) s s') (hs : Approx I s) :
    Approx I s' := by
  sorry

-- BEGIN SPEC
theorem aexec_sound {c : Com} {s s' : State} (h : BigStep c s s') (st : AState)
    (hs : Approx st s) : Approx (aexec c st) s' :=
-- END SPEC
  sorry

end H025

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three layers: expressions (M046's `plus_sound`/`times_sound` plus `(Sign.ofInt n).gamma n`), abstract-state operations (`lookup` after `ajoin`/`aupdate`), and commands. The only hard case is `while`: you need an abstract state that is stable under the loop body.
H2. `iterate_post`: induction on the fuel `k` generalizing `x`; fuel `0` returns `[]` (describes everything); in the stable branch `x = ajoin init (f x)`, so `f x ⊑ x` by `lookup_ajoin_right`. `approx_aupdate`: `intro y`, then `induction st generalizing x y s` and `cases x`, `cases y`; in the `succ`/`succ` case the tail describes the shifted state `fun k => s (k + 1)`. Then `while_inv`: an `I` with `aexec c I ⊑ I` is an invariant of every run (generalize the `while`, induct on the run). Main: `induction c generalizing s s' st`, so the IH for the body holds for every run and every abstract state.
H3. `while` case: `have hp := iterate_post (aexec c) st 10 st (fun _ h => h)` then `exact while_inv _ (fun st s s' h hs => ih h st hs) hp.2 h (hp.1 _ hs)`. `approx_aupdate`, `succ n`/`succ m` case: `have := ih (fun k => s (k + 1)) (fun k => h (k + 1)) n m`, then `simpa [aupdate, lookup, update] using this`. `lookup_ajoin_left`/`_right`: `induction p generalizing q x`, then `cases q` and `cases x`; the head case is `(a.join b).gamma v` from `a.gamma v` (resp. `b.gamma v`): `unfold Sign.join; split`.
-/
