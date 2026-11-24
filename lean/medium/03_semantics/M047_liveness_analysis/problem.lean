/- M047 | Liveness analysis for straight-line code | 15-20 min | dataflow analysis, backward analysis, agreement lemma, List.filter
GOAL
  `live p L` computes, backwards through a list of assignments `p`, a superset of the variables
  whose initial values can influence the variables in `L` at the end (it keeps `fv a` even when
  the assigned `x` is dead, so it over-approximates). Prove it sound: two initial states that
  agree on `live p L` produce final states that agree on `L`.

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M047

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

def update (s : State) (x : Nat) (v : Int) : State := fun y => if y = x then v else s y

/-- Straight-line code: a list of assignments `x := a`, run front to back. -/
abbrev Prog := List (Nat × AExp)

def exec : Prog → State → State
  | [], s => s
  | (x, a) :: p, s => exec p (update s x (aeval s a))

/-- The variables occurring in an expression. -/
def fv : AExp → List Nat
  | .num _ => []
  | .var x => [x]
  | .plus a b => fv a ++ fv b
  | .times a b => fv a ++ fv b

/-- Backward liveness: a superset of the variables whose initial values can influence the
    variables in `L` after running `p` (`fv a` is added even when `x` is dead). -/
def live : Prog → List Nat → List Nat
  | [], L => L
  | (x, a) :: p, L => (live p L).filter (· ≠ x) ++ fv a
-- END SPEC

/- SKELETON · live_sound
  0. MILESTONE first: your own lemma, declared above this theorem and outside the spec regions,
       aeval_agree (a : AExp) (s1 s2 : State) (h : ∀ y ∈ fv a, s1 y = s2 y) :
         aeval s1 a = aeval s2 a                           (used in step 5, case y = x)
     Induction on `a` with named alternatives:                                R1
       num:          both sides compute to `n`                                R2
       var:          `h x` applied to a proof of `x ∈ fv (.var x)`            R3
       plus, times:  unfold `aeval`, then rewrite with both IHs, each given
                     its premise by shrinking `h` to `fv a` / `fv b`          R4, R7 with R6 (R5)
  1. Induction on `p` generalizing `s1 s2` (named alternatives):              R8
  2. nil: the goal is `h` up to unfolding:                                    R9
  3. cons: split the pair, then use the IH on the updated states:             R10, R11
  4. Open the bounded ∀ and split on whether `y` is the assigned variable:    R12, R13
  5. y = x: replace `x`, evaluate the update, close with the milestone; its
     premise: every `z ∈ fv a` is in `live ((y, a) :: p) L`:                  R14, R15, R6 (R5)
  6. y ≠ x: evaluate the update, close with `h y`; its premise:
     `y ∈ live ((x, a) :: p) L` from `hy` and `hyx`:                          R16, R17 (R5)
-/
-- BEGIN SPEC
theorem live_sound (p : Prog) (L : List Nat) (s1 s2 : State)
    (h : ∀ y ∈ live p L, s1 y = s2 y) : ∀ y ∈ L, exec p s1 y = exec p s2 y :=
-- END SPEC
  sorry

end M047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Assigning `x := a` stores `aeval s a`, so first prove the milestone `aeval_agree`: two states
    that agree on `fv a` give `a` the same value (induction on `a`, R1–R7). Then induct on the
    program; the IH must hold for ALL pairs of states, because after one assignment the states are
    `update s1 x (aeval s1 a)` and `update s2 x (aeval s2 a)`.
H2. `induction p generalizing s1 s2 with | nil => exact h | cons xa p ih => …`. In `cons`:
    `obtain ⟨x, a⟩ := xa`, `apply ih`, `intro y hy`, `by_cases hyx : y = x`. If `y = x` the updates
    return the two values of `a` (milestone; every variable of `a` is live); otherwise they return
    `s1 y`, `s2 y`, and `y` survives the `filter (· ≠ x)`, so `h` applies.
H3. The premises are the crux. Milestone, `plus`: after `simp only [aeval]`,
    `rw [iha fun y hy => h y (by simp [fv, hy])]` (the same for `ihb`). Main, `y = x`: after
    `subst hyx` and `simp only [update, if_pos]`, the milestone needs
    `fun z hz => h z (by simp [live, hz])`. Main, `y ≠ x`: `h y (by simp [live, List.mem_filter, hy, hyx])`.
-/
