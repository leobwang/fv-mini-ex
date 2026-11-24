/- M049 | A type checker for STLC | 15-20 min | simply typed lambda calculus, Option, soundness and completeness
GOAL
  `typeOf Γ t` type-checks a simply typed lambda term (de Bruijn indices, typed binders) in the
  context `Γ` (a list: `Γ[n]` is the type of `var n`). Prove it is sound and complete for the
  typing relation `HasType Γ t A` ("`t` has type `A` in `Γ`").

BANNED: try?, grind
GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · typeOf_sound
  1. Induction on the term, keeping the context and the type general
     (the `lam` body is checked in `B :: Γ`):                               R1
  2. `var n`: `h` already is the premise of `HasType.var` (by definition):  R2
  3. `lam B t ih`: unfold one step of `typeOf` in `h`, split the `match`:   R3 → R4
       `some` branch: `h : some (B.arr B✝) = some A`; solve it for `A`,
       then apply the rule to the IH at `heq✝`:                             R5 → R2, R7, R6
       `none` branch: `h : none = some A`:                                  R8
  4. `app t u iht ihu`: unfold, split the two-scrutinee `match`:           R3 → R9
       first branch: split the `if`:                                        R10
         true:  solve `h : some B✝ = some A`, merge `A✝` and `A'✝`, apply
                the rule to both IHs:                                       R5 → R11 → R2, R7, R6
         false: `h : none = some A`:                                        R8
       catch-all branch: `h : none = some A`:                               R8
-/
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

/- SKELETON · typeOf_complete
  1. Induction on the derivation `h`, one alternative per rule:             R12
  2. `var hn`: unfold `typeOf`; the goal is then `hn`:                      R13
  3. `lam _ ih`: unfold `typeOf` and rewrite the inner call with `ih`:      R14
  4. `app _ _ ih1 ih2`: the same with `ih1`, `ih2`; the `if A = A` that
     appears is decided by the same `simp` call:                           R14, R15
-/
-- BEGIN SPEC
theorem typeOf_complete {Γ : List Ty} {t : Tm} {A : Ty} (h : HasType Γ t A) : typeOf Γ t = some A :=
-- END SPEC
  by
    induction h with
    | var hn => simpa [typeOf] using hn
    | lam _ ih => simp [typeOf, ih]
    | app _ _ ih1 ih2 => simp [typeOf, ih1, ih2]

-- MILESTONE (optional: change or delete)
/- SKELETON · type_unique
  1. `have h1 := typeOf_complete hA`             (h1 : typeOf Γ t = some A)
  2. rewrite `h1` with `typeOf_complete hB`:     R16    (h1 : some B = some A)
  3. strip the `some`s and flip the equation:     R17, R18
-/
theorem type_unique {Γ : List Ty} {t : Tm} {A B : Ty} (hA : HasType Γ t A) (hB : HasType Γ t B) :
    A = B := by
  have h1 := typeOf_complete hA
  rw [typeOf_complete hB] at h1
  exact (Option.some.inj h1).symm

end M049

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Soundness: induct on the term `t`, generalizing `Γ` and `A` (the `lam` body lives in `B :: Γ`).
    Completeness: induct on the derivation `h`; no generalizing needed.
H2. Soundness, each case: `simp only [typeOf] at h`, then `split at h` until `h` says `some _ = some A`
    (`app`: the two-scrutinee `match` first, then the `if`); `cases h`, and rebuild with
    `.lam`/`.app` applied to the IHs at the `heq✝` facts (`‹_›`). Every `none = some A` branch: `simp at h`.
    Completeness, each case: `simp [typeOf, ih]` (with both IHs for `app`); `var`: `simpa [typeOf] using hn`.
H3. `app` case of soundness: `simp only [typeOf] at h; split at h; · split at h; · cases h; subst_vars;
    exact .app (iht ‹_›) (ihu ‹_›); · simp at h; · simp at h`.
-/
