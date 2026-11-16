/- M047 | Liveness analysis for straight-line code | 15-20 min | dataflow analysis, backward analysis, agreement lemma, List.filter
GOAL
  `live p L` computes, backwards through a list of assignments `p`, a superset of the variables
  whose initial values can influence the variables in `L` at the end (it keeps `fv a` even when
  the assigned `x` is dead, so it over-approximates). Prove it sound: two initial states that
  agree on `live p L` produce final states that agree on `L`.

REFERENCE
  #check @List.mem_filter   -- x ∈ l.filter p ↔ x ∈ l ∧ p x = true
  #check @List.mem_append   -- a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t
  example (y : Nat) (h : y ∈ [1, 2].filter (· ≠ 1)) : y = 2 := by simp at h; omega
  example (s : State) (x : Nat) (v : Int) : update s x v x = v := by simp [update]
  -- `by_cases hy : y = x` splits on whether `y` is the variable just assigned.
  -- `induction p generalizing s1 s2 with | nil => .. | cons xa p ih => obtain ⟨x, a⟩ := xa; ..`
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

/-- `aeval s a` only looks at the variables of `a`. -/
theorem aeval_agree (a : AExp) (s1 s2 : State) (h : ∀ y ∈ fv a, s1 y = s2 y) :
    aeval s1 a = aeval s2 a := by
  induction a with
  | num n => rfl
  | var x => exact h x (by simp [fv])
  | plus a b iha ihb =>
    simp only [aeval]
    rw [iha fun y hy => h y (by simp [fv, hy]), ihb fun y hy => h y (by simp [fv, hy])]
  | times a b iha ihb =>
    simp only [aeval]
    rw [iha fun y hy => h y (by simp [fv, hy]), ihb fun y hy => h y (by simp [fv, hy])]

-- BEGIN SPEC
theorem live_sound (p : Prog) (L : List Nat) (s1 s2 : State)
    (h : ∀ y ∈ live p L, s1 y = s2 y) : ∀ y ∈ L, exec p s1 y = exec p s2 y :=
-- END SPEC
  by
    induction p generalizing s1 s2 with
    | nil => exact h
    | cons xa p ih =>
      obtain ⟨x, a⟩ := xa
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        simp only [update, if_pos]
        exact aeval_agree a s1 s2 fun z hz => h z (by simp [live, hz])
      · simp only [update, if_neg hyx]
        exact h y (by simp [live, List.mem_filter, hy, hyx])

end M047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First show that `aeval s a` only depends on the variables in `fv a`; then induct on the program.
H2. Helper `aeval_agree : (∀ y ∈ fv a, s1 y = s2 y) → aeval s1 a = aeval s2 a` by induction on `a`. Main: induction on `p` generalizing `s1 s2`; for `(x, a) :: p` apply the IH to the two updated states.
H3. In the `cons` case the IH needs `∀ y ∈ live p L, update s1 x (aeval s1 a) y = update s2 x (aeval s2 a) y`: `by_cases y = x`; if equal use `aeval_agree` (every `fv a` variable is live), otherwise `y` is in `(live p L).filter (· ≠ x)`, so `h` applies.
-/
