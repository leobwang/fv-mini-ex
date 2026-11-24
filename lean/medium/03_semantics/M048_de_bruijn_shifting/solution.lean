/- M048 | de Bruijn shifting | 15-20 min | de Bruijn indices, binders, cutoff, induction generalizing, if-splitting
GOAL
  In de Bruijn notation a variable is a number: `var k` points to the `k`-th enclosing `lam`.
  `shift d c t` adds `d` to every variable of `t` that is free at cutoff `c` (index `≥ c`).
  Prove: shifting by 0 is the identity, shifts at one cutoff add up, and unit shifts at
  cutoffs `c ≤ c'` commute (the cutoff `c'` moves to `c' + 1`).

REFERENCE
  example : shift 1 0 (.lam (.app (.var 0) (.var 1))) = .lam (.app (.var 0) (.var 2)) := rfl
  -- the cutoff grows under `lam`, so the IH must hold for every cutoff:
  -- `induction t generalizing c with | var n => .. | lam t ih => .. | app t u iht ihu => ..`
  example (n c : Nat) (h : ¬ n < c) : shift 1 c (.var n) = .var (n + 1) := by simp [shift, h]
  example (n c : Nat) : shift 0 c (.var n) = .var n := by simp only [shift]; split <;> rfl
  example (n c : Nat) (h : ¬ n < c) : ¬ n + 1 < c := by omega   -- feed such facts to `simp [shift, ..]`
  -- `by_cases h : n < c` splits on an index comparison; `show ¬ n + 1 < c by omega` inside simp.
BANNED: try?, grind
NOTE: `grind` is banned because `try?` prints `fun_induction shift .. <;> grind` for `shift_shift`.
  `shift_zero` is the warm-up; `shift_comm` is the real work. Do not leave `exact?`/`apply?` in.
-/

namespace M048

-- BEGIN SPEC
/-- Untyped lambda terms with de Bruijn indices: `var 0` is the nearest enclosing binder. -/
inductive Tm where
  | var (n : Nat)
  | lam (t : Tm)
  | app (t u : Tm)

/-- `shift d c t` adds `d` to every variable of `t` that is free at cutoff `c`. -/
def shift (d c : Nat) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam t => .lam (shift d (c + 1) t)
  | .app t u => .app (shift d c t) (shift d c u)
-- END SPEC

-- BEGIN SPEC
theorem shift_zero (c : Nat) (t : Tm) : shift 0 c t = t :=
-- END SPEC
  by
    induction t generalizing c with
    | var n => simp only [shift]; split <;> rfl
    | lam t ih => simp [shift, ih]
    | app t u iht ihu => simp [shift, iht, ihu]

-- BEGIN SPEC
theorem shift_shift (d d' c : Nat) (t : Tm) : shift d c (shift d' c t) = shift (d + d') c t :=
-- END SPEC
  by
    induction t generalizing c with
    | var n =>
      by_cases h : n < c
      · simp [shift, h]
      · simp [shift, h, show ¬ n + d' < c by omega, Nat.add_assoc, Nat.add_comm d d']
    | lam t ih => simp [shift, ih]
    | app t u iht ihu => simp [shift, iht, ihu]

-- BEGIN SPEC
theorem shift_comm (c c' : Nat) (t : Tm) (h : c ≤ c') :
    shift 1 c (shift 1 c' t) = shift 1 (c' + 1) (shift 1 c t) :=
-- END SPEC
  by
    -- WHY: the cutoffs grow under `lam`, so both (and `h`) must stay general in the IH.
    induction t generalizing c c' with
    | var n =>
      simp only [shift]
      by_cases h1 : n < c'
      · by_cases h2 : n < c
        · simp [shift, h1, h2, show n < c' + 1 by omega]
        · simp [shift, h1, h2, show n + 1 < c' + 1 by omega]
      · simp [shift, h1, show ¬ n < c by omega, show ¬ n + 1 < c by omega,
          show ¬ n + 1 < c' + 1 by omega]
    | lam t ih => simp [shift, ih (c + 1) (c' + 1) (by omega)]
    | app t u iht ihu => simp [shift, iht c c' h, ihu c c' h]

end M048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three are inductions on `t`. The interesting case is `var`; `lam` is the IH at the bigger cutoff(s).
H2. Generalize every cutoff (`generalizing c`, and `c c'` for `shift_comm`, together with `h`): under `lam` you need the IH at `c + 1` (and `c' + 1`, with `c + 1 ≤ c' + 1`). In the `var` case split every `if` and let `omega` compare indices.
H3. `shift_comm`: `induction t generalizing c c' with`; `lam t ih => simp [shift, ih (c + 1) (c' + 1) (by omega)]`; in the `var n` case `by_cases h1 : n < c'` and `by_cases h2 : n < c`, then e.g. `simp [shift, h1, h2, show n < c' + 1 by omega]`.
-/
