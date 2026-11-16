/- M040 | Small-step arithmetic: progress and determinism | 10-15 min | small-step semantics, inductive relation, cases inversion, induction on derivations
GOAL
  For a left-to-right small-step semantics of arithmetic expressions, prove that numerals cannot
  step, that every non-numeral can step (progress), and that stepping is deterministic.

REFERENCE
  -- `Step e e'` : `e` reduces to `e'` in one step. Rules are constructors, so they build proofs:
  example : M040.Step (.plus (.plus (.num 1) (.num 2)) (.num 0)) (.plus (.num 3) (.num 0)) :=
    .plusL .plusNum
  -- Inversion: `cases h` on `h : Step e e'` makes one goal per rule whose left side can match
  -- `e`; if no rule matches, the goal is closed.
  -- `rcases h with ⟨n, rfl⟩ | ⟨e', h'⟩` splits `(∃ n, e = .num n) ∨ ∃ e', Step e e'` and
  -- substitutes `e := .num n` in the first branch.
  -- `induction h1 generalizing e2` : induct on a derivation; the IH then holds for every `e2`.
-/

namespace M040

-- BEGIN SPEC
inductive Expr where
  | num (n : Nat)
  | plus (a b : Expr)
  | times (a b : Expr)

/-- Left-to-right small-step reduction: reduce the left operand to a numeral first, then the
right one, then combine two numerals. -/
inductive Step : Expr → Expr → Prop
  | plusNum {m n : Nat} : Step (.plus (.num m) (.num n)) (.num (m + n))
  | timesNum {m n : Nat} : Step (.times (.num m) (.num n)) (.num (m * n))
  | plusL {a a' b : Expr} : Step a a' → Step (.plus a b) (.plus a' b)
  | plusR {m : Nat} {b b' : Expr} : Step b b' → Step (.plus (.num m) b) (.plus (.num m) b')
  | timesL {a a' b : Expr} : Step a a' → Step (.times a b) (.times a' b)
  | timesR {m : Nat} {b b' : Expr} : Step b b' → Step (.times (.num m) b) (.times (.num m) b')
-- END SPEC

-- BEGIN SPEC
theorem num_stuck (n : Nat) (e : Expr) : ¬ Step (.num n) e :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem progress (e : Expr) : (∃ n, e = .num n) ∨ ∃ e', Step e e' :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem step_det {e e1 e2 : Expr} (h1 : Step e e1) (h2 : Step e e2) : e1 = e2 :=
-- END SPEC
  sorry

end M040

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `num_stuck` is pure inversion. `progress`: induction on `e`; in the `plus a b` case, ask the IH
    for `a` first (if `a` steps, use `plusL`), then the IH for `b` (`plusR` or `plusNum`).
H2. `step_det`: induct on `h1` (generalizing `e2`) and invert `h2` in each case. Mismatched rule
    pairs contain a step out of a numeral (kill it with `num_stuck`); matching pairs follow from the IH.
H3. Start with `induction h1 generalizing e2 <;> cases h2`. The mismatched pairs die by `num_stuck`
    (a numeral that supposedly steps).
-/
