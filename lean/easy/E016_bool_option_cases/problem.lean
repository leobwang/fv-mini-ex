/- E016 | Bool and Option cases | 2-3 min | cases, Bool, Option, <;>
GOAL
  Prove facts by splitting a `Bool` or an `Option` into its constructors.

REFERENCE
  example (b : Bool) : (b || false) = b := by cases b <;> rfl   -- goals for false and true
  example (o : Option Nat) : o.getD 0 ≥ 0 := by
    cases o with
    | none => simp
    | some x => simp
  `t <;> s` runs `s` on every goal produced by `t`.
  `simp_all` simplifies all hypotheses and the goal together (good after `cases`).
-/

-- BEGIN SPEC
def getOr (o : Option Nat) (d : Nat) : Nat :=
  match o with
  | some x => x
  | none => d
-- END SPEC

-- BEGIN SPEC
theorem and_not_self_bool (b : Bool) : (b && !b) = false :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem getOr_le (o : Option Nat) (d : Nat) : getOr o d ≤ getOr o 0 + d :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem map_eq_some (o : Option Nat) (h : o.map (· + 1) = some 5) : o = some 4 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `Bool` is `false` or `true`; an `Option` is `none` or `some x`. Split, then compute.
H2. After `cases o`, unfold `getOr` with `simp [getOr]`; for `map_eq_some`, simplify `h` as well.
H3. `cases b <;> rfl`, `cases o <;> simp [getOr]`, `cases o <;> simp_all`.
-/
