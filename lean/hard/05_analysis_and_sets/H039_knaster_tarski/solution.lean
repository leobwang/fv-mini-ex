/- H039 | Knaster–Tarski | 30-60 min | fixed points, Set, sInter, sUnion, mathlib
GOAL
  For a monotone `f : Set α → Set α`, the intersection of all `f`-closed sets is the least fixed
  point and the union of all `f`-consistent sets is the greatest fixed point.

REFERENCE
  #check Set.sInter_subset_of_mem   -- t ∈ S → ⋂₀ S ⊆ t
  #check Set.subset_sInter          -- (∀ t' ∈ S, t ⊆ t') → t ⊆ ⋂₀ S
  #check Set.subset_sUnion_of_mem   -- t ∈ S → t ⊆ ⋃₀ S
  #check Set.sUnion_subset          -- (∀ t' ∈ S, t' ⊆ t) → ⋃₀ S ⊆ t
  #check subset_antisymm            -- a ⊆ b → b ⊆ a → a = b
  example (A B C : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := h1.trans h2
  -- `A ∈ {X | f X ⊆ X}` unfolds to `f A ⊆ A` by definition.
-/
import Mathlib

namespace H039

-- BEGIN SPEC
def Mono {α : Type} (f : Set α → Set α) : Prop := ∀ A B, A ⊆ B → f A ⊆ f B

def lfp {α : Type} (f : Set α → Set α) : Set α := ⋂₀ {A | f A ⊆ A}

def gfp {α : Type} (f : Set α → Set α) : Set α := ⋃₀ {A | A ⊆ f A}
-- END SPEC

-- BEGIN SPEC
theorem lfp_least {α : Type} (f : Set α → Set α) (A : Set α) (hA : f A ⊆ A) : lfp f ⊆ A :=
-- END SPEC
  Set.sInter_subset_of_mem hA

-- BEGIN SPEC
theorem lfp_fixed {α : Type} (f : Set α → Set α) (hf : Mono f) : f (lfp f) = lfp f :=
-- END SPEC
  by
    have h1 : f (lfp f) ⊆ lfp f := by
      apply Set.subset_sInter
      intro A hA
      exact (hf _ _ (lfp_least f A hA)).trans hA
    exact subset_antisymm h1 (lfp_least f _ (hf _ _ h1))

-- BEGIN SPEC
theorem gfp_greatest {α : Type} (f : Set α → Set α) (A : Set α) (hA : A ⊆ f A) : A ⊆ gfp f :=
-- END SPEC
  Set.subset_sUnion_of_mem hA

-- BEGIN SPEC
theorem gfp_fixed {α : Type} (f : Set α → Set α) (hf : Mono f) : f (gfp f) = gfp f :=
-- END SPEC
  by
    have h1 : gfp f ⊆ f (gfp f) := by
      apply Set.sUnion_subset
      intro A hA
      exact hA.trans (hf _ _ (gfp_greatest f A hA))
    exact subset_antisymm (gfp_greatest f _ (hf _ _ h1)) h1

-- BEGIN SPEC
theorem lfp_subset_gfp {α : Type} (f : Set α → Set α) (hf : Mono f) : lfp f ⊆ gfp f :=
-- END SPEC
  lfp_least f _ (gfp_fixed f hf).le

end H039

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `lfp_least` and `gfp_greatest` are one lemma each. For the fixed points, prove one inclusion first and get the other by monotonicity plus least/greatest.
H2. `f (lfp f) ⊆ lfp f`: for every closed `A`, `lfp f ⊆ A`, so `f (lfp f) ⊆ f A ⊆ A`. Then `f (lfp f)` is itself closed, so `lfp f ⊆ f (lfp f)`.
H3. `have h1 : f (lfp f) ⊆ lfp f := Set.subset_sInter (fun A hA => (hf _ _ (lfp_least f A hA)).trans hA)` then `subset_antisymm h1 (lfp_least f _ (hf _ _ h1))`. Dually for gfp.
-/
