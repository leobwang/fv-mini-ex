/- E25 | Bounded quantifiers | 3 min | ∀ x ∈ xs, List.mem_map, List.mem_append
GOAL
  Work with `∀ x ∈ xs, P x` and `∃ x ∈ xs, P x` over lists.

REFERENCE
  -- `∀ x ∈ xs, P x` unfolds to `∀ x, x ∈ xs → P x`;  `∃ x ∈ xs, P x` to `∃ x, x ∈ xs ∧ P x`
  example (xs : List Nat) (h : ∀ x ∈ xs, x > 0) (y : Nat) (hy : y ∈ xs) : y > 0 := h y hy
  #check List.mem_map      -- b ∈ List.map f l ↔ ∃ a, a ∈ l ∧ f a = b
  #check List.mem_append   -- a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t
  #check List.mem_cons     -- a ∈ b :: l ↔ a = b ∨ a ∈ l
  example (f : Nat → Nat) (y : Nat) (h : ∃ a, a ∈ [1] ∧ f a = y) : True := by
    obtain ⟨a, ha, rfl⟩ := h; trivial   -- the `rfl` pattern substitutes y := f a
-/

-- BEGIN SPEC
theorem all_map_double (xs : List Nat) (h : ∀ x ∈ xs, x > 0) : ∀ y ∈ xs.map (· * 2), y > 1 :=
-- END SPEC
  by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have := h x hx
    omega

-- BEGIN SPEC
theorem all_append (p : Nat → Prop) (xs ys : List Nat) (h1 : ∀ x ∈ xs, p x) (h2 : ∀ y ∈ ys, p y) :
    ∀ z ∈ xs ++ ys, p z :=
-- END SPEC
  by
    intro z hz
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · exact h1 z hz
    · exact h2 z hz

-- BEGIN SPEC
theorem exists_big (xs : List Nat) (h : 3 ∈ xs) : ∃ x ∈ 0 :: xs, x > 2 :=
-- END SPEC
  ⟨3, List.mem_cons.mpr (Or.inr h), by decide⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Start `∀ y ∈ ...` goals with `intro y hy`; turn membership in a `map`/`++` into its meaning with `rw [..] at hy`.
H2. `all_map_double`: after `rw [List.mem_map] at hy`, unpack `⟨x, hx, rfl⟩` and use `h x hx`.
H3. `exists_big`: `⟨3, List.mem_cons.mpr (Or.inr h), by decide⟩`.
-/
