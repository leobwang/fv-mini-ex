/- M042 | The substitution lemma | 10-15 min | syntactic substitution, induction on expressions, update, Hoare assignment rule
GOAL
  Substituting `a` for `x` in `e`, then evaluating, equals evaluating `e` in the state where `x`
  holds `a`'s value (the core of Hoare's assignment rule). Also: a variable that does not occur in `e`
  does not affect its value, and if `x` does not occur in `a`, substituting for `x` a second time
  (after replacing `x` by `a`) changes nothing.

REFERENCE
  -- `update s x v` is the state `s` with variable `x` set to `v` (often written s[x ↦ v])
  example (s : M042.State) (x y : Nat) (h : y ≠ x) : M042.update s x 7 y = s y := by
    simp [M042.update, h]
  example (s : M042.State) (x y : Nat) : M042.update s x (s x) y = s y := by
    by_cases h : y = x <;> simp [M042.update, h]   -- split on `y = x`, then simp each case
  -- `| plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 => tac` : one tactic for two induction cases
  #check Bool.or_eq_false_iff  -- (x || y) = false ↔ x = false ∧ y = false
BANNED: try?, grind
NOTE: `grind` is banned because `induction e <;> grind [...]` closes the first two theorems
  outright; the point here is the induction itself. Do not leave search tactics (`exact?`, `apply?`) in the file.
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

-- BEGIN SPEC
theorem aeval_subst (s : State) (x : Nat) (a e : AExp) :
    aeval s (subst x a e) = aeval (update s x (aeval s a)) e :=
-- END SPEC
  by
    induction e with
    | num n => rfl
    | var y => by_cases h : y = x <;> simp [subst, aeval, update, h]
    | plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 => simp [subst, aeval, ih1, ih2]

-- BEGIN SPEC
theorem aeval_update_irrelevant (s : State) (x : Nat) (v : Int) (e : AExp)
    (h : occurs x e = false) : aeval (update s x v) e = aeval s e :=
-- END SPEC
  by
    induction e with
    | num n => rfl
    | var y =>
      have : y ≠ x := by simpa [occurs] using h
      simp [aeval, update, this]
    | plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 =>
      simp only [occurs, Bool.or_eq_false_iff] at h
      simp [aeval, ih1 h.1, ih2 h.2]

theorem occurs_subst {x : Nat} {a : AExp} (h : occurs x a = false) (e : AExp) :
    occurs x (subst x a e) = false := by
  induction e with
  | num n => rfl
  | var y => by_cases hy : y = x <;> simp [subst, occurs, hy, h]
  | plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 => simp [subst, occurs, ih1, ih2]

theorem subst_of_not_occurs {x : Nat} (b : AExp) {e : AExp} (h : occurs x e = false) :
    subst x b e = e := by
  induction e with
  | num n => rfl
  | var y =>
    have : y ≠ x := by simpa [occurs] using h
    simp [subst, this]
  | plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 =>
    simp only [occurs, Bool.or_eq_false_iff] at h
    simp [subst, ih1 h.1, ih2 h.2]

-- BEGIN SPEC
theorem subst_twice (x : Nat) (a b e : AExp) (h : occurs x a = false) :
    subst x b (subst x a e) = subst x a e :=
-- END SPEC
  subst_of_not_occurs b (occurs_subst h e)

end M042

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three go by `induction e`. Only the `var y` case needs thought: split on `y = x`.
H2. In `aeval_update_irrelevant`, `h` mentions `e`, so the IH needs `occurs x e1 = false`: get it by
    rewriting `h` with `occurs` and `Bool.or_eq_false_iff`. For `subst_twice`, after substituting
    `a` (where `x` does not occur) for `x`, `x` no longer occurs, and substituting for an absent variable does nothing.
H3. Two helpers: `occurs x a = false → occurs x (subst x a e) = false` and
    `occurs x e = false → subst x b e = e`, each by induction on `e`.
-/
