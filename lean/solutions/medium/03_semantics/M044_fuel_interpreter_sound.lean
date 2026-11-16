/- M044 | A fuel-based interpreter is sound and monotone | 15-20 min | interpreter with fuel, Option, split at, induction on fuel
GOAL
  `run n c s` executes the IMP command `c` from state `s` with fuel `n` (one unit per level of
  recursion; `none` = out of fuel). Prove it is sound (a result is a big-step result) and
  monotone (one more unit of fuel never changes a successful result).

REFERENCE
  -- IMP: arithmetic `AExp`, boolean `BExp`, commands `Com`; `update s x v` sets variable `x` to `v`;
  -- `BigStep c s s'` means: running `c` from state `s` terminates in state `s'`.
  example (n : Nat) (s : State) : run (n + 1) .skip s = some s := by simp only [run]  -- one step
  -- `split at h` on `h : (match run n c1 s with ...) = some s'` or `h : (if beval s b then ..) = ..`
  -- gives one goal per branch, with the branch condition as a new hypothesis.
  example (b : Bool) (h : ¬ b = true) : b = false := by simpa using h
  example (p : Prop) [Decidable p] (x y : Nat) (hp : p) : (if p then x else y) = x := if_pos hp
  -- `‹beval s b = true›` names a hypothesis by its type; `if_neg` is the `¬ p` twin of `if_pos`.
  -- `cases c with | skip => .. | «while» b c => ..`   (`while` is a keyword, so write «while»)
-/

namespace M044

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
-- END SPEC

-- BEGIN SPEC
theorem run_sound (n : Nat) (c : Com) (s s' : State) (h : run n c s = some s') :
    BigStep c s s' :=
-- END SPEC
  by
    induction n generalizing c s s' with
    | zero => simp [run] at h
    | succ n ih =>
      cases c with
      | skip => simp only [run, Option.some.injEq] at h; subst h; exact .skip
      | assign x a => simp only [run, Option.some.injEq] at h; subst h; exact .assign
      | seq c1 c2 =>
        simp only [run] at h
        split at h
        · exact .seq (ih _ _ _ ‹_›) (ih _ _ _ h)
        · simp at h
      | ite b c1 c2 =>
        simp only [run] at h
        split at h
        · exact .iteT ‹_› (ih _ _ _ h)
        · exact .iteF (by simpa using ‹¬beval s b = true›) (ih _ _ _ h)
      | «while» b c =>
        simp only [run] at h
        split at h
        · split at h
          · exact .whileT ‹_› (ih _ _ _ ‹_›) (ih _ _ _ h)
          · simp at h
        · simp only [Option.some.injEq] at h
          subst h
          exact .whileF (by simpa using ‹¬beval s b = true›)

-- BEGIN SPEC
theorem run_mono (n : Nat) (c : Com) (s s' : State) (h : run n c s = some s') :
    run (n + 1) c s = some s' :=
-- END SPEC
  by
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
          · -- WHY: rewrite the inner run of the body first, then the recursive loop call.
            rw [ih _ _ _ ‹_›]; exact ih _ _ _ h
          · simp at h
        · rw [if_neg ‹_›]; exact h

end M044

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems: induct on the fuel `n`, keeping `c s s'` general (the recursive calls change them).
H2. In the successor case do `cases c`, unfold one step of `run` in `h` (and in the goal for `run_mono`), then `split at h` to learn which branch produced the result; rebuild with the matching `BigStep` rule, or rewrite the inner `run` with the IH.
H3. `induction n generalizing c s s' with | zero => simp [run] at h | succ n ih => cases c with ...`; the `seq` case of `run_sound`: `simp only [run] at h; split at h; · exact .seq (ih _ _ _ ‹_›) (ih _ _ _ h); · simp at h`.
-/
