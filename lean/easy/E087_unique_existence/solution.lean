/- E087 | Unique existence | 2-3 min | ExistsUnique, ∃!, anonymous constructor, obtain, mathlib
GOAL
  Prove `∃! x, p x` ("exactly one `x` satisfies `p`") for two equations, then use a uniqueness
  hypothesis to show that two solutions are equal.

REFERENCE
  -- `∃! x, p x` means `∃ x, p x ∧ ∀ y, p y → y = x`   (type `∃!` as `\exists!`)
  example : ∃! n : ℕ, n = 2 := ⟨2, rfl, fun _ hy => hy⟩   -- ⟨witness, it works, uniqueness⟩
  example (p : ℕ → Prop) (h : ∃! n, p n) : ∃ n, p n := h.exists   -- forget the uniqueness
  example (p : ℕ → Prop) (h : ∃! n, p n) : ∃ n, p n := by
    obtain ⟨x, hx, hu⟩ := h; exact ⟨x, hx⟩     -- hu : ∀ y, p y → y = x
  -- `refine ⟨3, ?_, ?_⟩` leaves "3 works" and "anything that works is 3" as two goals
BANNED: simp, simp_all, simpa, norm_num, aesop, grind, ExistsUnique.unique, exact?, try?
-/
import Mathlib

namespace E087

-- BEGIN SPEC
theorem unique_sol : ∃! n : ℕ, n + 2 = 5 :=
-- END SPEC
  by
    refine ⟨3, rfl, ?_⟩
    intro y hy
    omega

-- BEGIN SPEC
theorem unique_real : ∃! x : ℝ, 2 * x + 1 = 7 :=
-- END SPEC
  ⟨3, by linarith, fun y hy => by linarith⟩

-- BEGIN SPEC
theorem unique_use (p : ℕ → Prop) (h : ∃! n, p n) (a b : ℕ) (ha : p a) (hb : p b) : a = b :=
-- END SPEC
  by
    obtain ⟨x, hx, hu⟩ := h
    rw [hu a ha, hu b hb]

end E087

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An `∃!` proof is a triple: the witness, a proof it satisfies `p`, and a uniqueness function.
H2. Witness `3` in both. The uniqueness part is `fun y hy => ...` (or `intro y hy`), closed by
    `omega` over ℕ and `linarith` over ℝ. For `unique_use`, destructure `h`: both `a` and `b` equal `x`.
H3. `refine ⟨3, rfl, ?_⟩; intro y hy; omega`; `unique_use`: `obtain ⟨x, hx, hu⟩ := h; rw [hu a ha, ...]`.
-/
