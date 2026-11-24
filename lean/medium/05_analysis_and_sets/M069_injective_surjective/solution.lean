/- M069 | Injective and surjective | 10 min | Function.Injective, Function.Surjective, composition, mathlib
GOAL
  Prove the composition laws for injective and surjective functions, and their partial converses.
BANNED: Function.Injective.comp, Function.Surjective.comp, Function.Injective.of_comp, Function.Surjective.of_comp

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Function

namespace M069

variable {α β γ : Type}

/- SKELETON · inj_comp
  1. Introduce the two inputs and the equation of outputs:              R2
       h : (f ∘ g) a = (f ∘ g) b     (by definition f (g a) = f (g b): R4)
  2. Goal a = b: reduce it with hg, then with hf:                      R3 (hg), R3 (hf)
  3. The goal is now the hypothesis from step 1:                        exact
  Term-mode alternative: a `fun` of the three variables, with R3 in term form twice.
-/
-- BEGIN SPEC
theorem inj_comp {f : β → γ} {g : α → β} (hf : Injective f) (hg : Injective g) :
    Injective (f ∘ g) :=
-- END SPEC
  fun _ _ h => hg (hf h)

/- SKELETON · surj_comp
  1. Introduce the target point c : γ:                                  R6
  2. A preimage of c under f, substituting c := f b:                    R8 (on hf c)
  3. A preimage of b under g, substituting b := g a:                    R8 (on hg b)
  4. The witness is a; the equation then holds by definition:           R9 with rfl, R4
-/
-- BEGIN SPEC
theorem surj_comp {f : β → γ} {g : α → β} (hf : Surjective f) (hg : Surjective g) :
    Surjective (f ∘ g) :=
-- END SPEC
  by
    intro c
    obtain ⟨b, rfl⟩ := hf c
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

/- SKELETON · inj_of_comp
  1. Introduce a b and hab : g a = g b:                                 R2
  2. Goal a = b: reduce it with h to (f ∘ g) a = (f ∘ g) b:             R3 (h)
  3. Close it from hab (rw [hab] alone fails: cheatsheet Traps):       R10
-/
-- BEGIN SPEC
theorem inj_of_comp {f : β → γ} {g : α → β} (h : Injective (f ∘ g)) : Injective g :=
-- END SPEC
  by
    intro a b hab
    apply h
    simp [hab]

/- SKELETON · surj_of_comp
  1. Introduce the target point c : γ:                                  R6
  2. A preimage of c under f ∘ g:  a : α,  ha : (f ∘ g) a = c           R7 (on h c)
  3. The witness for f is g a; ha is its proof (it is f (g a) = c):     R9, R4
-/
-- BEGIN SPEC
theorem surj_of_comp {f : β → γ} {g : α → β} (h : Surjective (f ∘ g)) : Surjective f :=
-- END SPEC
  by
    intro c
    obtain ⟨a, ha⟩ := h c
    exact ⟨g a, ha⟩

end M069

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every proof only unfolds the definitions: `intro` what `Injective` / `Surjective` quantify over
    (R2, R6), then use the hypotheses (R3, R7, R8). `(f ∘ g) x` is `f (g x)` by definition (R4).
H2. `inj_comp`: reduce `a = b` to `g a = g b` with `hg`, then to `f (g a) = f (g b)` with `hf`.
    `surj_comp`: take a preimage of `c` under `f`, then a preimage of that under `g`.
    `inj_of_comp`: `apply h`, then push `hab : g a = g b` through `f`.
    `surj_of_comp`: a preimage `a` of `c` under `f ∘ g` makes `g a` a preimage under `f`.
H3. `inj_comp`: `fun _ _ h => hg (hf h)`.
    `surj_comp`: `obtain ⟨b, rfl⟩ := hf c; obtain ⟨a, rfl⟩ := hg b; exact ⟨a, rfl⟩`.
    `inj_of_comp`: after `apply h`, `simp [hab]` closes the goal.
    `surj_of_comp`: after `obtain ⟨a, ha⟩ := h c`, the answer is `⟨g a, ha⟩`.
-/
