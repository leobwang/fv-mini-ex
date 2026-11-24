/- H039 | Knaster–Tarski | 30-60 min | fixed points, Set, sInter, sUnion, mathlib
GOAL
  For a monotone `f : Set α → Set α`, the intersection of all `f`-closed sets is the least fixed
  point and the union of all `f`-consistent sets is the greatest fixed point.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H039

-- BEGIN SPEC
def Mono {α : Type} (f : Set α → Set α) : Prop := ∀ A B, A ⊆ B → f A ⊆ f B

def lfp {α : Type} (f : Set α → Set α) : Set α := ⋂₀ {A | f A ⊆ A}

def gfp {α : Type} (f : Set α → Set α) : Set α := ⋃₀ {A | A ⊆ f A}
-- END SPEC

/- SKELETON · lfp_least   (prove first: used by lfp_fixed, steps 1c and 3, and by lfp_subset_gfp)
  1. Optional: see the intersection behind `lfp f`:                           R1 (`unfold lfp`)
  2. `A` is one of the closed sets intersected, so the intersection is below it: R2
  3. The remaining membership `A ∈ {A | f A ⊆ A}` is `hA` itself:               R3
-/
-- BEGIN SPEC
theorem lfp_least {α : Type} (f : Set α → Set α) (A : Set α) (hA : f A ⊆ A) : lfp f ⊆ A :=
-- END SPEC
  sorry

/- SKELETON · lfp_fixed   (uses lfp_least; prove that first)
  1. Fact first: `h1 : f (lfp f) ⊆ lfp f`, proof:
       a. below the intersection ← below every closed set:                      R5
       b. name the closed set and its closedness `hA : A ∈ {A | f A ⊆ A}`:      R6
       c. `f (lfp f) ⊆ f A` (monotonicity on `lfp_least f A hA`), then `⊆ A`:    R8, R7
  2. Split the equation into two inclusions:                                    R4
  3. `f (lfp f) ⊆ lfp f` is `h1`. `lfp f ⊆ f (lfp f)` is lfp_least at
     `A := f (lfp f)`; its hypothesis `f (f (lfp f)) ⊆ f (lfp f)` is monotonicity on `h1`: R8
-/
-- BEGIN SPEC
theorem lfp_fixed {α : Type} (f : Set α → Set α) (hf : Mono f) : f (lfp f) = lfp f :=
-- END SPEC
  sorry

/- SKELETON · gfp_greatest   (prove first: used by gfp_fixed, steps 1c and 3)
  1. Optional: see the union behind `gfp f`:                                    R1 (`unfold gfp`)
  2. `A` is one of the consistent sets united, so it is below the union:         R9
  3. The remaining membership `A ∈ {A | A ⊆ f A}` is `hA` itself:               R3
-/
-- BEGIN SPEC
theorem gfp_greatest {α : Type} (f : Set α → Set α) (A : Set α) (hA : A ⊆ f A) : A ⊆ gfp f :=
-- END SPEC
  sorry

/- SKELETON · gfp_fixed   (uses gfp_greatest; prove that first; the dual of lfp_fixed)
  1. Fact first: `h1 : gfp f ⊆ f (gfp f)`, proof:
       a. the union below `f (gfp f)` ← every consistent set below it:          R10
       b. name the consistent set and `hA : A ∈ {A | A ⊆ f A}`:                 R6
       c. `A ⊆ f A` (that is `hA`), then `f A ⊆ f (gfp f)` (monotonicity on
          `gfp_greatest f A hA`):                                               R7, R8
  2. Split the equation into two inclusions:                                    R4
  3. `f (gfp f) ⊆ gfp f` is gfp_greatest at `A := f (gfp f)`; its hypothesis
     `f (gfp f) ⊆ f (f (gfp f))` is monotonicity on `h1`. The other one is `h1`: R8
-/
-- BEGIN SPEC
theorem gfp_fixed {α : Type} (f : Set α → Set α) (hf : Mono f) : f (gfp f) = gfp f :=
-- END SPEC
  sorry

/- SKELETON · lfp_subset_gfp   (uses lfp_least and gfp_fixed)
  1. `apply lfp_least` (so `A := gfp f`): it remains to show `f (gfp f) ⊆ gfp f`.
  2. That inclusion is the equation gfp_fixed f hf read as `⊆`:                 R11
-/
-- BEGIN SPEC
theorem lfp_subset_gfp {α : Type} (f : Set α → Set α) (hf : Mono f) : lfp f ⊆ gfp f :=
-- END SPEC
  sorry

end H039

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `lfp_least` and `gfp_greatest` are one library lemma each (R2, R9): `hA` already says that `A` is in
    the family. For each fixed-point equation, prove one inclusion first as a `have`, then get the other
    from least/greatest applied to `f (lfp f)` (resp. `f (gfp f)`).
H2. `f (lfp f) ⊆ lfp f`: by `Set.subset_sInter` (R5) show `f (lfp f) ⊆ A` for every closed `A`; since
    `lfp f ⊆ A` (lfp_least), monotonicity gives `f (lfp f) ⊆ f A ⊆ A`. Monotonicity on that inclusion
    makes `f (lfp f)` closed, so lfp_least gives `lfp f ⊆ f (lfp f)`; `subset_antisymm` (R4) combines.
    Dually for gfp with `Set.sUnion_subset` (R10). `gfp f` is a fixed point, hence closed.
H3. `have h1 : f (lfp f) ⊆ lfp f := Set.subset_sInter (fun A hA => (hf _ _ (lfp_least f A hA)).trans hA)`
    then `subset_antisymm h1 (lfp_least f _ (hf _ _ h1))`. Dually for gfp. For lfp_subset_gfp the key
    fact is `(gfp_fixed f hf).le : f (gfp f) ⊆ gfp f` (R11).
-/
