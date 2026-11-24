/- H027 | Typed combinators are normalising (Tait) | 45-75 min | logical relations, reducibility, weak normalisation, combinatory logic, structural recursion on types
GOAL
  SK combinators: `K x y ⟶ x`, `S x y z ⟶ x z (y z)` (`⟶` is one `Step`, allowed anywhere in a term).
  Prove every simply typed term is weakly normalising (`WN t`: it reduces to a normal form) by Tait's
  method: `Red A t` by recursion on `A`, closed under backward steps, holds for every typed term.

REFERENCE
  example : H027.Step (.app (.app .K .S) .K) .S := .K                -- `K S K ⟶ S`
  example (t : H027.Tm) : H027.Star t t := .refl t                    -- `Star`: zero or more steps
  -- `Normal t` unfolds to `∀ t', ¬ Step t t'`: prove it with `intro t' h; cases h` (no rule fits),
  -- or `cases h with | appL h => .. | appR h => ..` when only the congruence rules fit.
  -- `obtain ⟨v, hv, nv⟩ := h` destructs `h : WN t`; `⟨v, hv, nv⟩` builds one.
  -- `Red (.arr A B) t` unfolds to `WN t ∧ ∀ u, Red A u → Red B (.app t u)`; `h.2 u hu` uses it.
  -- `induction A generalizing t t' with | base => .. | arr A B ihA ihB => ..` (recursion on types).
  -- `induction h with | refl => .. | step s _ ih => ..` on `h : Star t u`.
NOTE: Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file.
-/

namespace H027

-- BEGIN SPEC
inductive Ty where
  | base
  | arr (A B : Ty)

inductive Tm where
  | S
  | K
  | app (t u : Tm)

inductive HasTy : Tm → Ty → Prop
  | K {A B : Ty} : HasTy .K (.arr A (.arr B A))
  | S {A B C : Ty} : HasTy .S (.arr (.arr A (.arr B C)) (.arr (.arr A B) (.arr A C)))
  | app {t u : Tm} {A B : Ty} : HasTy t (.arr A B) → HasTy u A → HasTy (.app t u) B

inductive Step : Tm → Tm → Prop
  | K {x y : Tm} : Step (.app (.app .K x) y) x
  | S {x y z : Tm} : Step (.app (.app (.app .S x) y) z) (.app (.app x z) (.app y z))
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} : Step u u' → Step (.app t u) (.app t u')

inductive Star : Tm → Tm → Prop
  | refl (t : Tm) : Star t t
  | step {t u v : Tm} : Step t u → Star u v → Star t v

def Normal (t : Tm) : Prop := ∀ t', ¬ Step t t'

def WN (t : Tm) : Prop := ∃ v, Star t v ∧ Normal v
-- END SPEC

theorem star_trans {a b c : Tm} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

theorem star_appL {t t' u : Tm} (h : Star t t') : Star (.app t u) (.app t' u) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appL s) ih

theorem star_appR {t u u' : Tm} (h : Star u u') : Star (.app t u) (.app t u') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appR s) ih

theorem normal_K : Normal .K := by intro t' h; cases h

theorem normal_S : Normal .S := by intro t' h; cases h

theorem normal_Kx {x : Tm} (hx : Normal x) : Normal (.app .K x) := by
  intro t' h
  cases h with
  | appL h => cases h
  | appR h => exact hx _ h

theorem normal_Sx {x : Tm} (hx : Normal x) : Normal (.app .S x) := by
  intro t' h
  cases h with
  | appL h => cases h
  | appR h => exact hx _ h

theorem normal_Sxy {x y : Tm} (hx : Normal x) (hy : Normal y) : Normal (.app (.app .S x) y) := by
  intro t' h
  cases h with
  | appL h => exact normal_Sx hx _ h
  | appR h => exact hy _ h

-- MILESTONE (optional: change or delete)
/-- Reducibility (the logical relation): `WN` at the base type; at `A → B`, also maps
    reducible arguments to reducible results. -/
def Red : Ty → Tm → Prop
  | .base, t => WN t
  | .arr A B, t => WN t ∧ ∀ u, Red A u → Red B (.app t u)

theorem red_wn {A : Ty} {t : Tm} (h : Red A t) : WN t := by
  cases A with
  | base => exact h
  | arr A B => exact h.1

-- MILESTONE (optional: change or delete)
theorem red_back {A : Ty} {t t' : Tm} (s : Step t t') (h : Red A t') : Red A t := by
  induction A generalizing t t' with
  | base => obtain ⟨v, hv, nv⟩ := h; exact ⟨v, .step s hv, nv⟩
  | arr A B _ ihB =>
    obtain ⟨⟨v, hv, nv⟩, hf⟩ := h
    exact ⟨⟨v, .step s hv, nv⟩, fun u hu => ihB (.appL s) (hf u hu)⟩

-- MILESTONE (optional: change or delete)
theorem red_K {A B : Ty} : Red (.arr A (.arr B A)) .K := by
  refine ⟨⟨_, .refl _, normal_K⟩, fun x hx => ?_⟩
  obtain ⟨x', hx', nx'⟩ := red_wn hx
  exact ⟨⟨_, star_appR hx', normal_Kx nx'⟩, fun y _ => red_back .K hx⟩

-- MILESTONE (optional: change or delete)
theorem red_S {A B C : Ty} : Red (.arr (.arr A (.arr B C)) (.arr (.arr A B) (.arr A C))) .S := by
  refine ⟨⟨_, .refl _, normal_S⟩, fun x hx => ?_⟩
  obtain ⟨x', hx', nx'⟩ := red_wn hx
  refine ⟨⟨_, star_appR hx', normal_Sx nx'⟩, fun y hy => ?_⟩
  obtain ⟨y', hy', ny'⟩ := red_wn hy
  refine ⟨⟨_, star_trans (star_appL (star_appR hx')) (star_appR hy'), normal_Sxy nx' ny'⟩,
    fun z hz => ?_⟩
  -- WHY: `S x y z` is not normal; reduce one step and use that `x z (y z)` is reducible.
  apply red_back .S
  exact (hx.2 z hz).2 _ (hy.2 z hz)

theorem fundamental {t : Tm} {A : Ty} (h : HasTy t A) : Red A t := by
  induction h with
  | K => exact red_K
  | S => exact red_S
  | app _ _ ih1 ih2 => exact ih1.2 _ ih2

-- BEGIN SPEC
theorem weak_normalization {t : Tm} {A : Ty} (h : HasTy t A) : WN t :=
-- END SPEC
  red_wn (fundamental h)

end H027

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on typing fails directly: `WN t` and `WN u` say nothing about `WN (.app t u)`. `Red` strengthens the induction hypothesis so that the `app` case is just the arrow clause of `Red`. Every `Red A t` gives `WN t` (`cases A`).
H2. Small lemmas first: `Star` is transitive and is a congruence on both sides of `app`; `K`, `S`, `K x`, `S x`, `S x y` are normal when `x`, `y` are. `red_back`: induction on `A` generalizing the terms; the arrow case steps with `.appL s`. `red_K`/`red_S`: peel the arrows one argument at a time; only the fully applied case needs `red_back .K` / `red_back .S`.
H3. Saturated `S` case: `apply red_back .S; exact (hx.2 z hz).2 _ (hy.2 z hz)`. Then state `theorem fundamental (h : HasTy t A) : Red A t` and prove it by induction on `h`; the `app` case is `ih1.2 _ ih2`.
-/
