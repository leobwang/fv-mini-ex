/- M071 | Cantor's theorem | 10 min | diagonal argument, Set, Function.Surjective, mathlib
GOAL
  No function `α → Set α` is surjective; and no list of Boolean sequences indexed by ℕ contains
  every sequence.

REFERENCE
  example (α : Type) (f : α → Set α) : Set α := {x | x ∉ f x}   -- set-builder notation
  #check Set.mem_setOf_eq   -- (a ∈ {x | p x}) = p a
  example (P : Prop) (h : P ↔ ¬P) : False := by by_cases hp : P; exact h.mp hp hp; exact hp (h.mpr hp)
  example (b : Bool) : (!b) ≠ b := by cases b <;> decide
  example (f g : ℕ → Bool) (h : f = g) (n : ℕ) : f n = g n := congrFun h n
BANNED: Function.cantor_surjective, Function.cantor_injective
-/
import Mathlib

namespace M071

-- BEGIN SPEC
theorem cantor {α : Type} (f : α → Set α) : ¬ Function.Surjective f :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem diagonal (f : ℕ → ℕ → Bool) : ∃ g : ℕ → Bool, ∀ n, f n ≠ g :=
-- END SPEC
  sorry

end M071

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Diagonalise: build the set (or sequence) that disagrees with `f a` at `a`.
H2. `cantor`: take `D = {x | x ∉ f x}`; if `f a = D`, then `a ∈ f a ↔ a ∉ f a`.
H3. `obtain ⟨a, ha⟩ := hf {x | x ∉ f x}`; prove `a ∈ f a ↔ a ∉ f a` by rewriting with `ha`. `diagonal`: `g := fun n => !f n n`, and compare at `n` with `congrFun h n`.
-/
