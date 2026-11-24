/- M050 | A fuel-based interpreter is complete | 15-20 min | interpreter with fuel, completeness, induction on derivations, max of fuels, monotonicity
GOAL
  `run n c s` executes IMP command `c` from state `s` with fuel `n` (`none` = out of fuel).
  Prove completeness: every big-step run `BigStep c s s'` is found by `run` with enough fuel.
  `run_mono` (one more unit of fuel never hurts; M044's exercise) is given.

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M050

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

/-- An interpreter with fuel: `none` means "ran out of fuel". -/
def run : Nat → Com → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, s => some s
  | _ + 1, .assign x a, s => some (update s x (aeval s a))
  | n + 1, .seq c1 c2, s =>
    match run n c1 s with
    | some s' => run n c2 s'
    | none => none
  | n + 1, .ite b c1 c2, s => if beval s b then run n c1 s else run n c2 s
  | n + 1, .while b c, s =>
    if beval s b then
      match run n c s with
      | some s' => run n (.while b c) s'
      | none => none
    else some s

/-- Given (proved here; it is M044's exercise): more fuel never hurts. -/
theorem run_mono (n : Nat) (c : Com) (s s' : State) (h : run n c s = some s') :
    run (n + 1) c s = some s' := by
  induction n generalizing c s s' with
  | zero => simp [run] at h
  | succ n ih =>
    cases c with
    | skip => simpa [run] using h
    | assign x a => simpa [run] using h
    | seq c1 c2 =>
      simp only [run] at h ⊢
      split at h
      · rw [ih _ _ _ ‹_›]; exact ih _ _ _ h
      · simp at h
    | ite b c1 c2 =>
      simp only [run] at h ⊢
      split at h
      · rw [if_pos ‹_›]; exact ih _ _ _ h
      · rw [if_neg ‹_›]; exact ih _ _ _ h
    | «while» b c =>
      simp only [run] at h ⊢
      split at h
      · rw [if_pos ‹_›]
        split at h
        · rw [ih _ _ _ ‹_›]; exact ih _ _ _ h
        · simp at h
      · rw [if_neg ‹_›]; exact h
-- END SPEC

-- MILESTONE (optional: change or delete)
/- SKELETON · run_mono_le   (MILESTONE: prove it first; run_complete uses it in `seq` and `whileT`)
  1. Induct on the bound `m`; `hnm : n ≤ m` rides along into the IH:            R1
  2. zero:  `hnm : n ≤ 0` gives `n = 0`; substitute it, then `h` is the goal:   R2, R3
  3. succ m  (ih : n ≤ m → run m c s = some s',  hnm : n ≤ m + 1):
       split on `n < m + 1` or `n ≥ m + 1`:                                     R4
       n < m + 1:  `run_mono` on top of `ih`, the premise `n ≤ m` by `omega`:   R5 (with R2)
       n ≥ m + 1:  then `n = m + 1`; substitute it, `h` is the goal:            R2, R3
-/
theorem run_mono_le {n m : Nat} {c : Com} {s s' : State} (hnm : n ≤ m) (h : run n c s = some s') :
    run m c s = some s' := by
  sorry

/- SKELETON · run_complete   (uses the milestone `run_mono_le` in steps 5 and 6)
  1. Induct on the derivation `h`, not on `c`: one case per BigStep rule:          R6
  2. skip, assign: fuel 1; the run computes:                                       R7
  3. iteT, iteF (one IH): unpack it; fuel `n + 1`; unfold with `hb` and the IH:   R8, R14
  4. whileF: fuel 1; unfold with `hb`:                                             R14
  5. seq (two IHs, fuels n1 n2):
       unpack both IHs:                                                            R8
       choose the fuel `max n1 n2 + 1`:                                            refine ⟨_, ?_⟩
       run one step:                                                               R9
       lift the first sub-run to fuel `max n1 n2` (run_mono_le):                   R10 → R11
       lift the second the same way; it closes through the reduced `match`:       R10 → R12
  6. whileT (two IHs): as seq, but the step also uses `hb` to take the `then`
     branch:                                                     R8, refine, R9 + R13, R10 → R11, R10 → R12
-/
-- BEGIN SPEC
theorem run_complete {c : Com} {s s' : State} (h : BigStep c s s') : ∃ n, run n c s = some s' :=
-- END SPEC
  sorry

end M050

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestone `run_mono_le` first: induction on `m`, iterating `run_mono`. Then induct on the
    derivation `h`, not on `c`: the `whileT` case needs an IH for the *same* loop, which only the
    derivation provides.
H2. `skip`, `assign`, `whileF` need fuel 1. `iteT`/`iteF`: fuel `n + 1` from the IH's `n`. `seq`/`whileT`
    have two IHs with fuels `n1`, `n2`: run both at `max n1 n2` (by `run_mono_le`) and give `max n1 n2 + 1`.
H3. `run_mono_le`: `induction m`; zero: `have : n = 0 := by omega; subst this`; succ:
    `rcases Nat.lt_or_ge n (m + 1) with hlt | hge`, then `run_mono _ _ _ _ (ih (by omega))` or
    `n = m + 1`. `seq` case: `refine ⟨max n1 n2 + 1, ?_⟩; simp only [run]; rw [run_mono_le (Nat.le_max_left _ _) h1]`.
    `whileT` case: same shape, but `simp only [run, hb, if_true]` to take the `then` branch.
-/
