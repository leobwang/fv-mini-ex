/- H040 | Schröder–Bernstein | 1.5-2 h | fixed points, injections, invFun, classical, mathlib
GOAL
  If there are injections `f : α → β` and `g : β → α`, there is a bijection `α → β`.
  Build it from a fixed point of `S ↦ (g '' (f '' S)ᶜ)ᶜ`: use `f` on the fixed point and `g⁻¹` off it.

BANNED: Function.Embedding.schroeder_bernstein, Function.Embedding.antisymm, Cardinal.mk_le_of_injective, Function.Embedding.total

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Function

namespace H040

-- MILESTONE (optional: change or delete)
def Mono {α : Type} (F : Set α → Set α) : Prop := ∀ A B, A ⊆ B → F A ⊆ F B

-- MILESTONE (optional: change or delete)
def lfp {α : Type} (F : Set α → Set α) : Set α := ⋂₀ {A | F A ⊆ A}

/- SKELETON · lfp_fixed   (milestone; prove it FIRST; schroeder_bernstein uses it for `hfix`)
  1. `lfp F` lies below every pre-fixed point. hA : F A ⊆ A is already
     `A ∈ {A | F A ⊆ A}` by definition:
       least : ∀ A, F A ⊆ A → lfp F ⊆ A                                              R2, R1
  2. h1 : F (lfp F) ⊆ lfp F. Reduce to one member `A` of the family (intro A hA);
     then F (lfp F) ⊆ F A by hF and `least A hA`, and F A ⊆ A is hA:                   R3, R4
  3. Both inclusions: h1, and lfp F ⊆ F (lfp F) by `least` at the set F (lfp F),
     which is pre-fixed by hF applied to h1:                                           R5
-/
-- MILESTONE (optional: change or delete)
theorem lfp_fixed {α : Type} (F : Set α → Set α) (hF : Mono F) : F (lfp F) = lfp F := by
  sorry

/- SKELETON · schroeder_bernstein
  0. Prove the milestone lfp_fixed first (used in step 4).
  1. Make every membership decidable, for the `if` in step 5:                          R6
  2. Split on whether β is empty:                                                      R7
     IsEmpty β: α is empty too, since `a : α` would give `f a : β`:  have : IsEmpty α  R8, R9
       then f itself: injective by hf, surjective since no `b : β` exists:            R10, R11
  3. Nonempty β. Name  F S = (g '' (f '' S)ᶜ)ᶜ:                                         R12
     hF : Mono F: intro A B hAB, then peel complement, image, complement, image:      R13 → R14 → R13 → R14
  4. set A := lfp F. The fixed point  hfix : (g '' (f '' A)ᶜ)ᶜ = A  is lfp_fixed:       R15
     its complement form  hcompl : Aᶜ = g '' (f '' A)ᶜ:                               R16, then rw [hfix]
  5. Witness  fun x => if x ∈ A then f x else invFun g x;  two goals:                  R10
  6. Injective. First the fact about points off A:
       key : ∀ x, x ∉ A → g (invFun g x) = x ∧ invFun g x ∉ f '' A
     intro x hx; turn hx into x ∈ g '' (f '' A)ᶜ with hcompl; unpack it as x = g y
     with hy : y ∈ (f '' A)ᶜ; cancel invFun g (g y):                                   R17, R18, R19
     Then intro x1 x2 h; four cases on x1 ∈ A, x2 ∈ A; evaluate the `if`s in h:        R20, R21, R22, R23
       both in A:   hf h                                                               R24
       mixed:       f x1 ∈ f '' A contradicts (key x2 h2).2 (and symmetrically)        R25, R26
       both off A:  rewrite x1, x2 backwards with (key _ _).1, then rw [h]
  7. Surjective. intro y; case split on y ∈ f '' A:                                    R27, R21
       y ∈ f '' A: unpack y = f x with x ∈ A; witness x; `simp` evaluates the `if`     R18
       y ∉ f '' A: hgy : g y ∉ A via hcompl; witness g y; `simp` with hgy and R19      R28, rw [hcompl], R25, R19
-/
-- BEGIN SPEC
theorem schroeder_bernstein {α β : Type} (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h :=
-- END SPEC
  sorry

end H040

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove `lfp_fixed` first: `lfp F` lies below every `A` with `F A ⊆ A` (R1, R2), so
    `F (lfp F) ⊆ lfp F` (R3, R4), and `least` gives the other inclusion (R5). Main theorem:
    `classical`, then split on `isEmpty_or_nonempty β` (R6, R7). Otherwise take `A := lfp F` with
    `F S = (g '' (f '' S)ᶜ)ᶜ`; `F` is monotone, so `Aᶜ = g '' (f '' A)ᶜ` (R12–R16).
H2. `h x = if x ∈ A then f x else invFun g x` (R10). Injective: four cases (R21–R23); the mixed cases
    clash because `invFun g x ∉ f '' A` when `x ∉ A` (R25, R26). Surjective: `y ∈ f '' A` is hit by
    `f`; otherwise `g y ∉ A` (R28) and `h (g y) = y` (R19).
H3. `have least : ∀ A, F A ⊆ A → lfp F ⊆ A := fun A hA => Set.sInter_subset_of_mem hA`.
    Key lemma inside the proof: `∀ x, x ∉ A → g (invFun g x) = x ∧ invFun g x ∉ f '' A`: get
    `x ∈ g '' (f '' A)ᶜ` as `hcompl ▸ hx`, unpack it as `⟨y, hy, rfl⟩`, `rw [leftInverse_invFun hg y]`.
    Cases: `by_cases h1 : x1 ∈ A <;> by_cases h2 : x2 ∈ A <;> simp only [h1, h2, if_true, if_false] at h`.
-/
