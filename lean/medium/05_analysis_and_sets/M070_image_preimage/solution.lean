/- M070 | Image and preimage | 10-15 min | Set.image, Set.preimage, ext, mathlib
GOAL
  Prove four basic laws of images `f '' A` and preimages `f ⁻¹' B`.

REFERENCE
  #check Set.mem_image      -- b ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = b
  #check Set.mem_preimage   -- a ∈ f ⁻¹' s ↔ f a ∈ s
  example (f : ℕ → ℕ) (A : Set ℕ) (x : ℕ) (hx : x ∈ A) : f x ∈ f '' A := ⟨x, hx, rfl⟩
  example (f : ℕ → ℕ) (A : Set ℕ) (y : ℕ) (h : y ∈ f '' A) : True := by
    obtain ⟨x, hx, rfl⟩ := h; trivial     -- unpack an image membership
  Type `''` as two apostrophes and `⁻¹'` as `\inv'`.
BANNED: Set.image_union, Set.image_preimage_subset, Set.subset_preimage_image, Set.preimage_inter
-/
import Mathlib

namespace M070

variable {α β : Type}

-- BEGIN SPEC
theorem image_union_eq (f : α → β) (A B : Set α) : f '' (A ∪ B) = f '' A ∪ f '' B :=
-- END SPEC
  by
    ext y
    constructor
    · rintro ⟨x, hx | hx, rfl⟩
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, Or.inl hx, rfl⟩
      · exact ⟨x, Or.inr hx, rfl⟩

-- BEGIN SPEC
theorem image_preimage_sub (f : α → β) (B : Set β) : f '' (f ⁻¹' B) ⊆ B :=
-- END SPEC
  by
    rintro y ⟨x, hx, rfl⟩
    exact hx

-- BEGIN SPEC
theorem sub_preimage_image (f : α → β) (A : Set α) : A ⊆ f ⁻¹' (f '' A) :=
-- END SPEC
  fun x hx => ⟨x, hx, rfl⟩

-- BEGIN SPEC
theorem preimage_inter_eq (f : α → β) (B C : Set β) : f ⁻¹' (B ∩ C) = f ⁻¹' B ∩ f ⁻¹' C :=
-- END SPEC
  by
    ext x
    rfl

end M070

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Set equalities: `ext y` then two directions; image memberships unpack as `⟨x, hx, rfl⟩`.
H2. Preimage membership is definitional: `x ∈ f ⁻¹' B` is literally `f x ∈ B`.
H3. `image_union_eq` →: `rintro ⟨x, hx | hx, rfl⟩`; ←: `rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`. `preimage_inter_eq`: `ext x; rfl`.
-/
