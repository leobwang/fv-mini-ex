/- E30 | Prop-valued definitions | 3 min | def Prop, unfold, show
GOAL
  Prove facts about predicates defined with `def … : Prop`.

REFERENCE
  def Pos (n : Nat) : Prop := 0 < n              -- a predicate is a function into Prop
  example : Pos 3 := by unfold Pos; decide        -- `unfold` exposes the body
  example (n : Nat) (h : Pos n) : n ≠ 0 := by unfold Pos at h; omega
  example : Pos 3 := by show 0 < 3; decide        -- `show` accepts any definitionally equal goal
  example (n : Nat) (h : ∃ k, n = 2 * k) : True := by obtain ⟨k, hk⟩ := h; trivial
  `obtain`/`intro`/`⟨_, _⟩` see through definitions automatically; `rw`/`simp`/`omega` do not.
-/

-- BEGIN SPEC
def Divides (d n : Nat) : Prop := ∃ k, n = d * k

def UpperBound (b : Nat) (xs : List Nat) : Prop := ∀ x ∈ xs, x ≤ b
-- END SPEC

-- BEGIN SPEC
theorem divides_refl (n : Nat) : Divides n n :=
-- END SPEC
  ⟨1, (Nat.mul_one n).symm⟩

-- BEGIN SPEC
theorem divides_trans (a b c : Nat) (h1 : Divides a b) (h2 : Divides b c) : Divides a c :=
-- END SPEC
  by
    obtain ⟨k, rfl⟩ := h1
    obtain ⟨m, rfl⟩ := h2
    exact ⟨k * m, Nat.mul_assoc a k m⟩

-- BEGIN SPEC
theorem upperBound_cons (b x : Nat) (xs : List Nat) (hx : x ≤ b) (h : UpperBound b xs) :
    UpperBound b (x :: xs) :=
-- END SPEC
  by
    unfold UpperBound at *
    intro y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact h y hy

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Divides a b` is an `∃`, and `UpperBound b xs` is a bounded `∀`: prove them like E07 and E25.
H2. `divides_trans`: unpack both witnesses with the `rfl` pattern, then the witness is a product.
H3. `exact ⟨k * m, Nat.mul_assoc a k m⟩`; for `upperBound_cons`: `unfold UpperBound at *; intro y hy; rw [List.mem_cons] at hy`.
-/
