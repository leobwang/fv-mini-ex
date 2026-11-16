/- H040 | Schröder–Bernstein | 1.5-2 h | fixed points, injections, invFun, classical, mathlib
GOAL
  If there are injections `f : α → β` and `g : β → α`, there is a bijection `α → β`.
  Build it from a fixed point of `S ↦ (g '' (f '' S)ᶜ)ᶜ`: use `f` on the fixed point and `g⁻¹` off it.

REFERENCE
  #check Function.invFun            -- (f : α → β) [Nonempty α] : β → α   (a chosen inverse)
  #check Function.leftInverse_invFun -- Injective f → LeftInverse (invFun f) f, i.e. invFun f (f a) = a
  #check Set.image_mono             -- s ⊆ t → f '' s ⊆ f '' t
  #check Set.compl_subset_compl     -- sᶜ ⊆ tᶜ ↔ t ⊆ s
  #check isEmpty_or_nonempty        -- IsEmpty α ∨ Nonempty α
  -- `classical` (as the first tactic) lets you write `if x ∈ A then .. else ..` for any set A.
  -- With A = (g '' (f '' A)ᶜ)ᶜ: every x ∉ A is `g y` for some y ∉ f '' A.
BANNED: Function.Embedding.schroeder_bernstein, Function.Embedding.antisymm, Cardinal.mk_le_of_injective, Function.Embedding.total
-/
import Mathlib

open Function

namespace H040

-- MILESTONE (optional: change or delete)
def Mono {α : Type} (F : Set α → Set α) : Prop := ∀ A B, A ⊆ B → F A ⊆ F B

-- MILESTONE (optional: change or delete)
def lfp {α : Type} (F : Set α → Set α) : Set α := ⋂₀ {A | F A ⊆ A}

-- MILESTONE (optional: change or delete)
theorem lfp_fixed {α : Type} (F : Set α → Set α) (hF : Mono F) : F (lfp F) = lfp F := by
  have least : ∀ A, F A ⊆ A → lfp F ⊆ A := fun A hA => Set.sInter_subset_of_mem hA
  have h1 : F (lfp F) ⊆ lfp F := by
    apply Set.subset_sInter
    intro A hA
    exact (hF _ _ (least A hA)).trans hA
  exact subset_antisymm h1 (least _ (hF _ _ h1))

-- BEGIN SPEC
theorem schroeder_bernstein {α β : Type} (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : ∃ h : α → β, Bijective h :=
-- END SPEC
  by
    classical
    rcases isEmpty_or_nonempty β with hβ | hβ
    · have : IsEmpty α := ⟨fun a => hβ.false (f a)⟩
      exact ⟨f, hf, fun b => hβ.elim b⟩
    let F : Set α → Set α := fun S => (g '' (f '' S)ᶜ)ᶜ
    have hF : Mono F := by
      intro A B hAB
      apply Set.compl_subset_compl.mpr
      apply Set.image_mono
      apply Set.compl_subset_compl.mpr
      exact Set.image_mono hAB
    set A := lfp F with hA
    have hfix : (g '' (f '' A)ᶜ)ᶜ = A := lfp_fixed F hF
    have hcompl : Aᶜ = g '' (f '' A)ᶜ := by rw [← compl_compl (g '' (f '' A)ᶜ), hfix]
    refine ⟨fun x => if x ∈ A then f x else invFun g x, ?_, ?_⟩
    · have key : ∀ x, x ∉ A → g (invFun g x) = x ∧ invFun g x ∉ f '' A := by
        intro x hx
        have : x ∈ g '' (f '' A)ᶜ := hcompl ▸ hx
        obtain ⟨y, hy, rfl⟩ := this
        rw [leftInverse_invFun hg y]
        exact ⟨rfl, hy⟩
      intro x1 x2 h
      by_cases h1 : x1 ∈ A <;> by_cases h2 : x2 ∈ A <;> simp only [h1, h2, if_true, if_false] at h
      · exact hf h
      · exact absurd ⟨x1, h1, h⟩ (key x2 h2).2
      · exact absurd ⟨x2, h2, h.symm⟩ (key x1 h1).2
      · rw [← (key x1 h1).1, ← (key x2 h2).1, h]
    · intro y
      by_cases hy : y ∈ f '' A
      · obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, by simp [hx]⟩
      · have hgy : g y ∉ A := by
          rw [← Set.mem_compl_iff, hcompl]
          exact ⟨y, hy, rfl⟩
        exact ⟨g y, by simp [hgy, leftInverse_invFun hg y]⟩

end H040

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Handle `β` empty separately (then `α` is empty too). Otherwise take `A := lfp F` with `F S = (g '' (f '' S)ᶜ)ᶜ`; `F` is monotone, so `Aᶜ = g '' (f '' A)ᶜ`.
H2. `h x = if x ∈ A then f x else invFun g x`. Injective: four cases; the mixed cases clash because `invFun g x ∉ f '' A` when `x ∉ A`. Surjective: `y ∈ f '' A` is hit by `f`; otherwise `g y ∉ A` and `h (g y) = y`.
H3. Key lemma inside the proof: `∀ x ∉ A, g (invFun g x) = x ∧ invFun g x ∉ f '' A` (unpack `x ∈ g '' (f '' A)ᶜ` as `⟨y, hy, rfl⟩` and use `leftInverse_invFun hg y`).
-/
