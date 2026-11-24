/- M042 | The substitution lemma | 10-15 min | syntactic substitution, induction on expressions, update, Hoare assignment rule
GOAL
  Substituting `a` for `x` in `e`, then evaluating, equals evaluating `e` in the state where `x`
  holds `a`'s value (the core of Hoare's assignment rule). Also: a variable that does not occur in `e`
  does not affect its value, and if `x` does not occur in `a`, substituting for `x` a second time
  (after replacing `x` by `a`) changes nothing.

BANNED: try?, grind
GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M042

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

/-- Replace every occurrence of variable `x` in `e` by `a`. -/
def subst (x : Nat) (a : AExp) : AExp → AExp
  | .num n => .num n
  | .var y => if y = x then a else .var y
  | .plus e1 e2 => .plus (subst x a e1) (subst x a e2)
  | .times e1 e2 => .times (subst x a e1) (subst x a e2)

/-- Does variable `x` occur in `e`? -/
def occurs (x : Nat) : AExp → Bool
  | .num _ => false
  | .var y => y == x
  | .plus e1 e2 => occurs x e1 || occurs x e2
  | .times e1 e2 => occurs x e1 || occurs x e2
-- END SPEC

/- SKELETON · aeval_subst
  1. Induction on `e`, one alternative per constructor; `plus` and `times`
     share one tactic:                                                      R1, R8
  2. `num n`: both sides compute to `n`:                                    R2
  3. `var y`: split on `y = x`, then in both cases (`<;>`) unfold `subst`,
     `aeval` and `update` and decide the `if` with `h`:                     R3 → R4, R5, R6
  4. `plus` / `times`: unfold `subst` and `aeval` one step, then rewrite
     with `ih1`, `ih2`:                                                     R4 → R7
-/
-- BEGIN SPEC
theorem aeval_subst (s : State) (x : Nat) (a e : AExp) :
    aeval s (subst x a e) = aeval (update s x (aeval s a)) e :=
-- END SPEC
  sorry

/- SKELETON · aeval_update_irrelevant
  1. Induction on `e` as before; `h` mentions `e`, so each IH now has the
     premise `occurs x e1 = false`:                                         R1, R8, R9
  2. `num n`:                                                               R2
  3. `var y`: first get the fact  hne : y ≠ x  from `h`:                    have, R11 (R10 inside)
     then unfold `aeval`, `update` and decide the `if` with `hne`:          R4, R5, R6
  4. `plus` / `times`: split `h` into the premises of the two IHs, then
     unfold `aeval` and rewrite with the IHs applied to them:               R12 → R4, R13
-/
-- BEGIN SPEC
theorem aeval_update_irrelevant (s : State) (x : Nat) (v : Int) (e : AExp)
    (h : occurs x e = false) : aeval (update s x v) e = aeval s e :=
-- END SPEC
  sorry

/- SKELETON · subst_twice
  Prove two MILESTONES first, above this theorem (outside the spec regions):
    M1  occurs_subst {x : Nat} {a : AExp} (h : occurs x a = false) (e : AExp) :
          occurs x (subst x a e) = false
        induction on `e` as in `aeval_subst`:                               R1, R8, R2
        `var y`: split on `y = x`; then in both cases ONE `simp` with
        `subst`, `occurs`, the split hypothesis and `h` (`occurs` unfolds
        only once the `if` is decided, so not two separate calls):          R3 → R4, R6, R10
        nodes: unfold, rewrite with the IHs; `rw` leaves the goal
          (false || false) = false   which computes, so close it:           R4 → R7 → R2
    M2  subst_of_not_occurs {x : Nat} (b : AExp) {e : AExp} (h : occurs x e = false) :
          subst x b e = e
        the shape of `aeval_update_irrelevant`, with `subst` for `aeval`:   R1, R8, R9, R2
        `var y`: get  hne : y ≠ x  from `h`, then unfold `subst` and
        decide the `if` with `hne`:                                         have, R11 → R4, R6
        nodes: split `h`, unfold `subst`, rewrite with the IHs applied
        to `h.1`, `h.2`:                                                    R12 → R4, R13
  Then: M2 (with this `b`) applied to M1 (with this `h` and `e`); no
  induction in this theorem:                                                R14
-/
-- BEGIN SPEC
theorem subst_twice (x : Nat) (a b e : AExp) (h : occurs x a = false) :
    subst x b (subst x a e) = subst x a e :=
-- END SPEC
  sorry

end M042

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three go by `induction e` (R1), with `plus` and `times` handled by one shared tactic (R8). Only
    the `var y` case needs thought: split on `y = x` (R3). The `num n` cases are `rfl` (R2).
H2. `aeval_subst`: in every case unfold `subst`, `aeval`, `update` with `simp`, adding the split
    hypothesis or the IHs (R4–R7). `aeval_update_irrelevant`: `h` mentions `e`, so the IHs need
    `occurs x e1 = false` (R9): get it by rewriting `h` with `occurs` and `Bool.or_eq_false_iff` (R12).
    `subst_twice`: after substituting `a` (where `x` does not occur) for `x`, `x` no longer occurs (M1),
    and substituting for an absent variable does nothing (M2).
H3. `aeval_subst`, case `var y`: `by_cases h : y = x <;> simp [subst, aeval, update, h]`.
    `aeval_update_irrelevant`, nodes: `simp only [occurs, Bool.or_eq_false_iff] at h`, then
    `simp [aeval, ih1 h.1, ih2 h.2]`; case `var y`: `have : y ≠ x := by simpa [occurs] using h`.
    `subst_twice`: `subst_of_not_occurs b (occurs_subst h e)`, with M1 and M2 as in the SKELETON.
-/
