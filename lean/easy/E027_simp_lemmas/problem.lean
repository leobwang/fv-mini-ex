/- E027 | simp lemmas | 2-3 min | @[simp], attribute, simp
GOAL
  Prove two equations tagged `@[simp]`, then watch plain `simp` use them.

GUIDE
  Entries R1–R5: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def inc (n : Nat) : Nat := n + 1
-- END SPEC

/- SKELETON · twice_apply
  1. The right side `f (f x)` is the body of `twice`: the equation holds by
     unfolding the definition, so close it by definition:                  R1
  The `@[simp]` tag is not used here; it puts the lemma in the simp set for
  `twice_twice_inc` (R2, with a function variable `f`: R3).
-/
-- BEGIN SPEC
@[simp] theorem twice_apply (f : Nat → Nat) (x : Nat) : twice f x = f (f x) :=
-- END SPEC
  sorry

/- SKELETON · inc_eq
  1. The right side `n + 1` is the body of `inc`: close it by definition:   R1
  The tag again only matters for `twice_twice_inc` (R2).
-/
-- BEGIN SPEC
@[simp] theorem inc_eq (n : Nat) : inc n = n + 1 :=
-- END SPEC
  sorry

/- SKELETON · twice_twice_inc
  1. One plain `simp`, no list in brackets: `twice_apply` and `inc_eq` are
     in the default simp set because of their tags:                        R2
     inside that call, in this order:
       the outer call, with `f := twice inc` (a partial application)
         → `twice inc (twice inc n)`                                       R3
       each of the two new full calls `twice inc t` → `inc (inc t)`         R4
       each `inc t` → `t + 1`                                               R2
       left over: `n + 1 + 1 + 1 + 1 = n + 4`, cancelled and closed         R5
-/
-- BEGIN SPEC
theorem twice_twice_inc (n : Nat) : twice (twice inc) n = n + 4 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Compare each tagged lemma with the `def` above it: its right side is the definition's body (R1).
    The third theorem is about what the tags do, not about new reasoning (R2).
H2. Prove `twice_apply` and `inc_eq` by definition (R1). After that, plain `simp` knows both
    equations: it unfolds the outer `twice`, the two inner `twice inc` calls and every `inc` (R3, R4,
    R2), then closes the arithmetic (R5). No `[twice, inc]` list is needed.
H3. `rfl`, `rfl`, `by simp`.
-/
