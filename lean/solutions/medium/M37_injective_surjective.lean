/- M37 | Injective and surjective | 10 min | Function.Injective, Function.Surjective, composition, mathlib
GOAL
  Prove the composition laws for injective and surjective functions, and their partial converses.

REFERENCE
  -- Injective f : ∀ a b, f a = f b → a = b        Surjective f : ∀ b, ∃ a, f a = b
  example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ) (h : f a = f b) : a = b := hf h
  example (f : ℕ → ℕ) (hf : Function.Surjective f) : ∃ a, f a = 0 := hf 0
  example (f g : ℕ → ℕ) (x : ℕ) : (f ∘ g) x = f (g x) := rfl
  `intro a b h` on an Injective goal; `intro c` then `obtain ⟨b, rfl⟩ := hf c` on Surjective.
BANNED: Function.Injective.comp, Function.Surjective.comp, Function.Injective.of_comp, Function.Surjective.of_comp
-/
import Mathlib

open Function

namespace M37

variable {α β γ : Type}

-- BEGIN SPEC
theorem inj_comp {f : β → γ} {g : α → β} (hf : Injective f) (hg : Injective g) :
    Injective (f ∘ g) :=
-- END SPEC
  fun _ _ h => hg (hf h)

-- BEGIN SPEC
theorem surj_comp {f : β → γ} {g : α → β} (hf : Surjective f) (hg : Surjective g) :
    Surjective (f ∘ g) :=
-- END SPEC
  by
    intro c
    obtain ⟨b, rfl⟩ := hf c
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

-- BEGIN SPEC
theorem inj_of_comp {f : β → γ} {g : α → β} (h : Injective (f ∘ g)) : Injective g :=
-- END SPEC
  by
    intro a b hab
    apply h
    simp [hab]

-- BEGIN SPEC
theorem surj_of_comp {f : β → γ} {g : α → β} (h : Surjective (f ∘ g)) : Surjective f :=
-- END SPEC
  by
    intro c
    obtain ⟨a, ha⟩ := h c
    exact ⟨g a, ha⟩

end M37

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold the definitions: each proof is a few `intro`s and one application of a hypothesis.
H2. `inj_of_comp`: from `g a = g b` get `f (g a) = f (g b)`, then use `h`. `surj_of_comp`: the preimage of `c` under `f` is `g a`.
H3. `inj_comp`: `fun _ _ h => hg (hf h)`; `surj_comp`: `obtain ⟨b, rfl⟩ := hf c; obtain ⟨a, rfl⟩ := hg b; exact ⟨a, rfl⟩`.
-/
