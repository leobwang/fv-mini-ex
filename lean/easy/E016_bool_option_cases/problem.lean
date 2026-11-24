/- E016 | Bool and Option cases | 2-3 min | cases, Bool, Option, <;>
GOAL
  Prove facts by splitting a `Bool` or an `Option` into its constructors.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def getOr (o : Option Nat) (d : Nat) : Nat :=
  match o with
  | some x => x
  | none => d
-- END SPEC

/- SKELETON · and_not_self_bool
  1. Split `b` into `false` and `true`:                                     R1
  2. In each case both sides are closed `Bool` terms that compute:          R2
     Do 1 and 2 in one line, running the closer on both goals:              R3
-/
-- BEGIN SPEC
theorem and_not_self_bool (b : Bool) : (b && !b) = false :=
-- END SPEC
  sorry

/- SKELETON · getOr_le
  1. `getOr o _` cannot compute while `o` is unknown: split `o`:            R4
  2. In both cases (via R3): unfold `getOr` on the constructor             R5
     (before the split, unfolding only shows a stuck `match o with …`);
     case `none` is then `d ≤ 0 + d`, case `some` is `val✝ ≤ val✝ + d`;
     the same `simp` call closes these                                      R6
-/
-- BEGIN SPEC
theorem getOr_le (o : Option Nat) (d : Nat) : getOr o d ≤ getOr o 0 + d :=
-- END SPEC
  sorry

/- SKELETON · map_eq_some
  1. Split `o`:                                                             R4
  2. The information is in `h`, so simplify `h` and the goal together
     in both cases (via R3):                                                R12
       case `none`: `h` becomes `none = some 5`, which is impossible        R7 → R8
       case `some`: `h` becomes `some (_ + 1) = some 5`, then `_ + 1 = 5`,
       then `_ = 4`; the goal `some _ = some 4` follows from it             R9 → R10 → R11
-/
-- BEGIN SPEC
theorem map_eq_some (o : Option Nat) (h : o.map (· + 1) = some 5) : o = some 4 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `Bool` is `false` or `true`; an `Option` is `none` or `some x`. Every goal here only computes once the
    variable is a constructor, so start each proof with `cases` (R1, R4).
H2. `and_not_self_bool`: after the split both sides are closed terms (R2). `getOr_le`: unfold `getOr` with
    `simp [getOr]` in each case (R5, R6). `map_eq_some`: the facts are in `h`; simplify `h` together with the
    goal (R12), which also disposes of the impossible `none` case (R8). Use `<;>` to treat both cases alike (R3).
H3. `cases b <;> rfl`; `cases o <;> simp [getOr]`; `cases o <;> simp_all`.
-/
