/- M070 | Image and preimage | 10-15 min | Set.image, Set.preimage, ext, mathlib
GOAL
  Prove four basic laws of images `f '' A` and preimages `f ⁻¹' B`: the image of a union, the image of a
  preimage, the preimage of an image, and the preimage of an intersection.
BANNED: Set.image_union, Set.image_preimage_subset, Set.subset_preimage_image, Set.preimage_inter

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M070

variable {α β : Type}

/- SKELETON · image_union_eq
  1. Set equation → membership of one point `y : β`:                        R1
  2. Split the `↔` into its two directions:                                 R2
  3. (→) Introduce and unpack `y ∈ f '' (A ∪ B)` in ONE `rintro`: a point `x`,
     which side of `A ∪ B` it is on, and `f x = y` (substituted away):       R5 with R6 nested inside
     In each of the two goals `f x ∈ f '' A ∪ f '' B`:
       pick the side of the union                                           R7
       prove the image membership with the witness `x`                      R8
  4. (←) Introduce and unpack `y ∈ f '' A ∪ f '' B`: first the union, then
     the image on each side:                                                R6 with R5 on each side
     In each goal `f x ∈ f '' (A ∪ B)`: witness `x` first, then the side     R8, then R7
-/
-- BEGIN SPEC
theorem image_union_eq (f : α → β) (A B : Set α) : f '' (A ∪ B) = f '' A ∪ f '' B :=
-- END SPEC
  sorry

/- SKELETON · image_preimage_sub
  1. Introduce the point and unpack its image membership in one `rintro`:   R9 with R5
     (the infoview prints `f '' (f ⁻¹' B)` as `f '' f ⁻¹' B`)
  2. What you got, `hx : x ∈ f ⁻¹' B`, is the goal `f x ∈ B` by definition:  R10 (`exact`)
-/
-- BEGIN SPEC
theorem image_preimage_sub (f : α → β) (B : Set β) : f '' (f ⁻¹' B) ⊆ B :=
-- END SPEC
  sorry

/- SKELETON · sub_preimage_image
  1. Introduce the point `x` and `hx : x ∈ A` (`intro`, or a term `fun x hx => …`):   R9
  2. The goal `x ∈ f ⁻¹' f '' A` (that is, `x ∈ f ⁻¹' (f '' A)`) is
     `f x ∈ f '' A` by definition: no step needed (`rw` only to see it)    R10
  3. Prove the image membership with the witness `x`:                       R8
-/
-- BEGIN SPEC
theorem sub_preimage_image (f : α → β) (A : Set α) : A ⊆ f ⁻¹' (f '' A) :=
-- END SPEC
  sorry

/- SKELETON · preimage_inter_eq
  1. Set equation → membership of one point `x : α`:                        R1
  2. Both sides of the `↔` unfold to `f x ∈ B ∧ f x ∈ C` (R10, R11), so no
     directions are needed: close it                                        R12
-/
-- BEGIN SPEC
theorem preimage_inter_eq (f : α → β) (B C : Set β) : f ⁻¹' (B ∩ C) = f ⁻¹' B ∩ f ⁻¹' C :=
-- END SPEC
  sorry

end M070

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything is membership. A set equation becomes `x ∈ S ↔ x ∈ T` with `ext`, a subset `S ⊆ T` is a
    `∀ x, x ∈ S → x ∈ T` you `intro`. Image, preimage, `∪` and `∩` memberships all hold by definition
    (cheatsheet, "Reading the goals"), so patterns and `exact` see through them.
H2. `image_union_eq`: `constructor`, then in each direction unpack the hypothesis with a `rintro` pattern that
    combines the image pattern `⟨x, hx, rfl⟩` with the union pattern `h | h`, and rebuild the goal with
    `Or.inl`/`Or.inr` and `⟨x, hx, rfl⟩`. The two subset laws are one-liners with the same image pattern.
    `preimage_inter_eq` needs no directions: after `ext`, both sides are the same proposition.
H3. `image_union_eq` →: `rintro ⟨x, hx | hx, rfl⟩`, then `exact Or.inl ⟨x, hx, rfl⟩` (and `Or.inr`);
    ←: `rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)`, then `exact ⟨x, Or.inl hx, rfl⟩` (and `Or.inr`).
    `image_preimage_sub`: `rintro y ⟨x, hx, rfl⟩`. `sub_preimage_image`: the term `⟨x, hx, rfl⟩`.
    `preimage_inter_eq`: `ext x; rfl`.
-/
