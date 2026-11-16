/- E056 | Sections and variables | 2-3 min | section, variable, include, namespace, open in
GOAL
  Read a `section` whose `variable` line supplies arguments to every declaration in it: prove facts about
  `twice`, one of which needs a hypothesis that arrives only via `include … in`. Then use a lemma that
  lives in the namespace `Shape`.

REFERENCE
  section Demo                                -- `variable`s live until the matching `end Demo`
  variable {α : Type} (l : List α) (h : l.length = 3)
  def dup : List α := l ++ l                  -- becomes `dup {α} (l : List α)`: only variables it mentions
  include h in                                -- the next declaration also takes `h`, though its type never says so
  theorem len_pos : 0 < l.length := by omega  -- `#check @len_pos` : ∀ {α} (l : List α), l.length = 3 → 0 < l.length
  end Demo
  example (a b : List Nat) : (a ++ b).length = a.length + b.length := List.length_append  -- full name
  example (a b : List Nat) : (a ++ b).length = a.length + b.length := by open List in exact length_append
  -- `namespace X … end X` prefixes names with `X.`; `open X in` drops the prefix for one command or tactic
  #check List.append_eq_nil_iff   -- p ++ q = [] ↔ p = [] ∧ q = []
BANNED: Nat.mul_comm, ac_rfl, grind, exact?, try?
NOTE: never add a `variable`/`include` line yourself: it changes the frozen statements after it (the checker rejects that).
-/

namespace E056

section Lists
-- BEGIN SPEC
variable {α : Type} (xs ys : List α) (hne : xs ≠ [])

def twice : List α := xs ++ xs
-- END SPEC

-- BEGIN SPEC
theorem twice_length : (twice xs).length = 2 * xs.length :=
-- END SPEC
  by simp [twice]; omega

-- BEGIN SPEC
theorem twice_append : twice (xs ++ ys) = xs ++ ys ++ (xs ++ ys) :=
-- END SPEC
  rfl

-- BEGIN SPEC
include hne in
theorem twice_ne_nil : twice xs ≠ [] :=
-- END SPEC
  -- WHY: `hne` is usable here only because of `include hne in`.
  fun h => hne (List.append_eq_nil_iff.mp h).1
end Lists

namespace Shape
-- BEGIN SPEC
def area (w h : Nat) : Nat := w * h
theorem area_comm (w h : Nat) : area w h = area h w := Nat.mul_comm w h
-- END SPEC
end Shape

-- BEGIN SPEC
theorem area_twice (w h : Nat) : Shape.area w h + Shape.area h w = 2 * Shape.area w h :=
-- END SPEC
  by open Shape in rw [area_comm h w]; omega

end E056

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Inside the section, `twice xs` is `xs ++ xs`, and `hne : xs ≠ []` is in scope in `twice_ne_nil` only because
    of `include hne in`. `area_twice` is about `w * h` versus `h * w`, which `omega` cannot relate (nonlinear).
H2. `twice_length`: unfold and use `List.length_append`, then arithmetic. `twice_append` holds by definition.
    `twice_ne_nil`: assume `twice xs = []` and split it with `List.append_eq_nil_iff`. `area_twice`: rewrite the
    second area with the namespaced lemma, then it is linear.
H3. `simp [twice]; omega`; `rfl`; `intro h; exact hne (List.append_eq_nil_iff.mp h).1`;
    `rw [Shape.area_comm h w]; omega` (or `open Shape in rw [area_comm h w]`, then `omega`).
-/
