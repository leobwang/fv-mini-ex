/- M050 | A fuel-based interpreter is complete | 15-20 min | interpreter with fuel, completeness, induction on derivations, max of fuels, monotonicity
GOAL
  `run n c s` executes IMP command `c` from state `s` with fuel `n` (`none` = out of fuel).
  Prove completeness: every big-step run `BigStep c s s'` is found by `run` with enough fuel.
  `run_mono` (one more unit of fuel never hurts; M044's exercise) is given.

REFERENCE
  -- `induction h with | skip => _ | seq h1 h2 ih1 ih2 => _ | whileT hb h1 h2 ih1 ih2 => _ | ...`
  example (a b : Nat) : a ≤ max a b := Nat.le_max_left a b      -- and `Nat.le_max_right`
  example (n m : Nat) : n < m ∨ n ≥ m := Nat.lt_or_ge n m
  example (n m : Nat) (h : n ≤ m + 1) : n ≤ m ∨ n = m + 1 := by omega   -- omega knows max, ≤
  -- `obtain ⟨n1, h1⟩ := ih1` unpacks `∃ n, run n c s = some s'`
  -- `simp only [run]` unfolds one step of `run (k + 1) ...`; then `rw [h1]` fires its `match`
  -- for `.while b c`, also pass `hb`: `simp only [run, hb, if_true]` takes the `then` branch
  -- `simp [run, hb, h]` evaluates `run (n + 1) (.ite b c1 c2) s` given `hb : beval s b = true`
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
theorem run_mono_le {n m : Nat} {c : Com} {s s' : State} (hnm : n ≤ m) (h : run n c s = some s') :
    run m c s = some s' := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact run_mono _ _ _ _ (ih (by omega))
    · have : n = m + 1 := by omega
      subst this; exact h

-- BEGIN SPEC
theorem run_complete {c : Com} {s s' : State} (h : BigStep c s s') : ∃ n, run n c s = some s' :=
-- END SPEC
  by
  induction h with
  | skip => exact ⟨1, rfl⟩
  | assign => exact ⟨1, rfl⟩
  | seq _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    -- WHY: the two sub-runs used different fuels; lift both to their max.
    refine ⟨max n1 n2 + 1, ?_⟩
    simp only [run]
    rw [run_mono_le (Nat.le_max_left _ _) h1]
    exact run_mono_le (Nat.le_max_right _ _) h2
  | iteT hb _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, by simp [run, hb, h]⟩
  | iteF hb _ ih =>
    obtain ⟨n, h⟩ := ih
    exact ⟨n + 1, by simp [run, hb, h]⟩
  | whileF hb => exact ⟨1, by simp [run, hb]⟩
  | whileT hb _ _ ih1 ih2 =>
    obtain ⟨n1, h1⟩ := ih1
    obtain ⟨n2, h2⟩ := ih2
    refine ⟨max n1 n2 + 1, ?_⟩
    simp only [run, hb, if_true]
    rw [run_mono_le (Nat.le_max_left _ _) h1]
    exact run_mono_le (Nat.le_max_right _ _) h2

end M050

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Lift `run_mono` from `n + 1` to any `m ≥ n` first. Then induct on the derivation `h`, not on `c`:
    the `whileT` case needs an IH for the *same* loop, which only the derivation provides.
H2. `skip`, `assign`, `whileF` need fuel 1. `iteT`/`iteF`: fuel `n + 1` from the IH's `n`. `seq`/`whileT`
    have two IHs with fuels `n1`, `n2`: run both at `max n1 n2` (by `run_mono_le`) and give `max n1 n2 + 1`.
H3. `run_mono_le`: `induction m`, then `Nat.lt_or_ge n (m + 1)`: either `run_mono _ _ _ _ (ih (by omega))` or
    `n = m + 1`. `seq` case: `refine ⟨max n1 n2 + 1, ?_⟩; simp only [run]; rw [run_mono_le (Nat.le_max_left _ _) h1]`.
    `whileT` case: same shape, but `simp only [run, hb, if_true]` first to take the `then` branch.
-/
