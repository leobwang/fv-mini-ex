/- E003 | intro, exact, apply | 2-3 min | intro, exact, apply
GOAL
  Prove four implications with the three basic tactics.

REFERENCE
  example (P Q : Prop) : P → Q → P := by intro hp hq; exact hp  -- `intro` names assumptions
  example (P Q : Prop) (h : P → Q) (hp : P) : Q := by apply h; exact hp
      -- `apply h` works backwards: goal `Q` becomes goal `P` (one goal per premise of h)
  example (p : Nat → Prop) (h : ∀ n, p n) : p 3 := by exact h 3   -- ∀ is a function: apply it
  `by` starts tactic mode; `;` or a new line separates tactics.
BANNED: simp, simp_all, grind
-/

-- BEGIN SPEC
theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem two_premises (P Q R : Prop) (h : P → Q → R) (hp : P) (hq : Q) : R :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem swap_args (P Q R : Prop) : (P → Q → R) → (Q → P → R) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem step_twice (p : Nat → Prop) (step : ∀ n, p n → p (n + 1)) (h0 : p 0) : p 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start each proof with `intro` for every `→` left of the goal, then look at what remains.
H2. When the goal matches the conclusion of a hypothesis, `apply` it and prove its premises.
H3. `step_twice`: `apply step; apply step; exact h0` (the goal goes p 2 → p 1 → p 0).
-/
