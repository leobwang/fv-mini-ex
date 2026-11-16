/- M049 | A type checker for STLC | 15-20 min | simply typed lambda calculus, Option, soundness and completeness
GOAL
  `typeOf Γ t` type-checks a simply typed lambda term (de Bruijn indices, typed binders) in the
  context `Γ` (a list: `Γ[n]` is the type of `var n`). Prove it is sound and complete for the
  typing relation `HasType Γ t A` ("`t` has type `A` in `Γ`").

REFERENCE
  example (A : Ty) (Γ : List Ty) : (A :: Γ)[0]? = some A := List.getElem?_cons_zero
  example (A : Ty) (Γ : List Ty) (n : Nat) : (A :: Γ)[n + 1]? = Γ[n]? := List.getElem?_cons_succ
  -- `split at h` on `h : (match typeOf (A :: Γ) t with ...) = some B` gives one goal per arm, with
  -- the scrutinee's value as a hypothesis (`heq : typeOf (A :: Γ) t = some B'`).
  example (A B : Ty) (h : (if A = B then some 1 else none) = some 1) : A = B := by
    split at h <;> simp_all     -- `deriving DecidableEq` is what makes `if A = B` legal
  example (A B : Ty) (h : some A = some B) : A = B := Option.some.inj h
  -- `subst h` replaces a variable everywhere using `h : x = e` or `h : e = x`;
  -- `subst_vars` does this for every such equation in the context at once.
BANNED: try?, grind
NOTE: `grind` is banned because `try?` prints `(induction h) <;> grind [= typeOf]` for the easy
  half, `typeOf_complete`. Do not leave `exact?`/`apply?` in the file.
-/

namespace M049

-- BEGIN SPEC
inductive Ty where
  | base
  | arr (A B : Ty)
  deriving DecidableEq

/-- Simply typed lambda calculus, de Bruijn indices, annotated binders. -/
inductive Tm where
  | var (n : Nat)
  | lam (A : Ty) (t : Tm)
  | app (t u : Tm)

/-- Γ[n] is the type of `var n`. -/
inductive HasType : List Ty → Tm → Ty → Prop
  | var {Γ : List Ty} {n : Nat} {A : Ty} : Γ[n]? = some A → HasType Γ (.var n) A
  | lam {Γ : List Ty} {A B : Ty} {t : Tm} : HasType (A :: Γ) t B → HasType Γ (.lam A t) (.arr A B)
  | app {Γ : List Ty} {A B : Ty} {t u : Tm} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (.app t u) B

def typeOf : List Ty → Tm → Option Ty
  | Γ, .var n => Γ[n]?
  | Γ, .lam A t =>
    match typeOf (A :: Γ) t with
    | some B => some (.arr A B)
    | none => none
  | Γ, .app t u =>
    match typeOf Γ t, typeOf Γ u with
    | some (.arr A B), some A' => if A = A' then some B else none
    | _, _ => none
-- END SPEC

-- BEGIN SPEC
theorem typeOf_sound {Γ : List Ty} {t : Tm} {A : Ty} (h : typeOf Γ t = some A) : HasType Γ t A :=
-- END SPEC
  by
    induction t generalizing Γ A with
    | var n => exact .var h
    | lam B t ih =>
      simp only [typeOf] at h
      split at h
      · cases h
        exact .lam (ih ‹_›)
      · simp at h
    | app t u iht ihu =>
      simp only [typeOf] at h
      split at h
      · split at h
        · cases h
          subst_vars
          exact .app (iht ‹_›) (ihu ‹_›)
        · simp at h
      · simp at h

-- BEGIN SPEC
theorem typeOf_complete {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Γ t A) : typeOf Γ t = some A :=
-- END SPEC
  by
    induction h with
    | var hn => simpa [typeOf] using hn
    | lam _ ih => simp [typeOf, ih]
    | app _ _ ih1 ih2 => simp [typeOf, ih1, ih2]

-- MILESTONE (optional: change or delete)
-- Types are unique: rewrite both `typeOf_complete` facts into one equation `some A = some B`,
-- then use `Option.some.inj`.
theorem type_unique {Γ : List Ty} {t : Tm} {A B : Ty} (hA : HasType Γ t A) (hB : HasType Γ t B) :
    A = B := by
  have h1 := typeOf_complete hA
  rw [typeOf_complete hB] at h1
  exact (Option.some.inj h1).symm

end M049

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Soundness: induct on the term `t` (keeping `Γ` and `A` general: `lam` extends the context). Completeness: induct on the derivation `h`.
H2. Soundness: in each case unfold one step of `typeOf` in `h` and `split at h` until `h` says `some _ = some A`; read off the pieces and rebuild with `HasType.lam`/`HasType.app`. Completeness: `simp [typeOf, ih]` in each case.
H3. `app` case of soundness: `simp only [typeOf] at h; split at h; · split at h; · cases h; subst_vars; exact .app (iht ‹_›) (ihu ‹_›); · simp at h; · simp at h`.
-/
