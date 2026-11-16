/- E027 | simp lemmas | 2-3 min | @[simp], attribute, simp
GOAL
  Prove two equations tagged `@[simp]`, then watch plain `simp` use them.

REFERENCE
  def addTwo (n : Nat) : Nat := n + 2
  @[simp] theorem addTwo_eq (n : Nat) : addTwo n = n + 2 := rfl   -- simp now rewrites addTwo
  example (n : Nat) : addTwo (addTwo n) = n + 4 := by simp         -- no `[addTwo]` needed
  attribute [simp] Nat.mul_comm   -- tag an existing lemma (careful: may loop or misfire)
  example (n : Nat) : addTwo n = n + 2 := by simp [-addTwo_eq, addTwo]   -- `-name` drops one
  A good simp lemma rewrites a complicated left side into a simpler right side.
-/

-- BEGIN SPEC
def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
def inc (n : Nat) : Nat := n + 1
-- END SPEC

-- BEGIN SPEC
@[simp] theorem twice_apply (f : Nat → Nat) (x : Nat) : twice f x = f (f x) :=
-- END SPEC
  sorry

-- BEGIN SPEC
@[simp] theorem inc_eq (n : Nat) : inc n = n + 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem twice_twice_inc (n : Nat) : twice (twice inc) n = n + 4 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The two tagged lemmas are true by definition.
H2. Once they are proved and tagged, `simp` unfolds `twice` and `inc` by itself.
H3. `rfl`, `rfl`, `by simp`.
-/
