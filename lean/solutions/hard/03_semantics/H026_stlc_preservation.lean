/- H026 | STLC progress and preservation with de Bruijn substitutions | 1.5-2 h | simply typed lambda calculus, parallel substitution, renaming lemma, progress and preservation
GOAL
  Call-by-value STLC, de Bruijn indices (M048), contexts `Ctx := Nat → Option Ty` (not M049's lists).
  A renaming `ρ : Nat → Nat` sends free `var n` to `var (ρ n)`; a parallel substitution `σ : Nat → Tm`
  sends it to `σ n`. Prove preservation (`Step` keeps the type) and progress (a closed typed term is a value or steps).

REFERENCE
  example : H026.Ctx.cons .base (fun _ => none) 0 = some .base := rfl   -- contexts are functions
  example : H026.subst (H026.beta (.var 7)) (.app (.var 0) (.var 1)) = .app (.var 7) (.var 0) := rfl
  example : H026.rename Nat.succ (.lam .base (.var 1)) = .lam .base (.var 2) := rfl   -- `upRen` skips index 0
  -- The context changes under `lam`, so: `induction h generalizing Δ ρ with | var hn => .. | lam _ ih => ..`
  -- `intro n A hn; cases n with | zero => .. | succ n => ..` splits on index 0 vs n + 1.
  -- Named arguments fix an implicit: `rename_typing (ρ := Nat.succ) (fun _ _ h => h) ht`.
  -- Inversion: `cases h with | app h1 h2 => ..` on `h : HasType Γ (.app t u) A`.
  -- `induction h` needs variable indices: `generalize hΓ : (fun _ => none : Ctx) = Γ at h` first.
  -- `rcases h with hv | ⟨t', ht'⟩` splits `Value t ∨ ∃ t', Step t t'`.
NOTE: Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file.
-/

namespace H026

-- BEGIN SPEC
inductive Ty where
  | base
  | arr (A B : Ty)

inductive Tm where
  | var (n : Nat)
  | lam (A : Ty) (t : Tm)
  | app (t u : Tm)

/-- A context maps de Bruijn indices to types. -/
abbrev Ctx := Nat → Option Ty

/-- Extend a context with a new innermost variable `0 : A`. -/
def Ctx.cons (A : Ty) (Γ : Ctx) : Ctx
  | 0 => some A
  | n + 1 => Γ n

inductive HasType : Ctx → Tm → Ty → Prop
  | var {Γ : Ctx} {n : Nat} {A : Ty} : Γ n = some A → HasType Γ (.var n) A
  | lam {Γ : Ctx} {A B : Ty} {t : Tm} :
      HasType (Γ.cons A) t B → HasType Γ (.lam A t) (.arr A B)
  | app {Γ : Ctx} {A B : Ty} {t u : Tm} :
      HasType Γ t (.arr A B) → HasType Γ u A → HasType Γ (.app t u) B

/-- Lift a renaming under a binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

def rename (ρ : Nat → Nat) : Tm → Tm
  | .var n => .var (ρ n)
  | .lam A t => .lam A (rename (upRen ρ) t)
  | .app t u => .app (rename ρ t) (rename ρ u)

/-- Lift a parallel substitution under a binder. -/
def up (σ : Nat → Tm) : Nat → Tm
  | 0 => .var 0
  | n + 1 => rename Nat.succ (σ n)

def subst (σ : Nat → Tm) : Tm → Tm
  | .var n => σ n
  | .lam A t => .lam A (subst (up σ) t)
  | .app t u => .app (subst σ t) (subst σ u)

/-- The substitution for a beta step: `0 ↦ v`, `n + 1 ↦ n`. -/
def beta (v : Tm) : Nat → Tm
  | 0 => v
  | n + 1 => .var n

inductive Value : Tm → Prop
  | lam {A : Ty} {t : Tm} : Value (.lam A t)

/-- Call-by-value reduction. -/
inductive Step : Tm → Tm → Prop
  | beta {A : Ty} {t v : Tm} : Value v → Step (.app (.lam A t) v) (subst (beta v) t)
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {v u u' : Tm} : Value v → Step u u' → Step (.app v u) (.app v u')
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem rename_typing {Γ Δ : Ctx} {ρ : Nat → Nat} (hρ : ∀ n A, Γ n = some A → Δ (ρ n) = some A)
    {t : Tm} {A : Ty} (h : HasType Γ t A) : HasType Δ (rename ρ t) A := by
  induction h generalizing Δ ρ with
  | var hn => exact .var (hρ _ _ hn)
  | lam _ ih =>
    refine .lam (ih ?_)
    intro n A hn
    cases n with
    | zero => exact hn
    | succ n => exact hρ n A hn
  | app _ _ ih1 ih2 => exact .app (ih1 hρ) (ih2 hρ)

-- MILESTONE (optional: change or delete)
theorem subst_typing {Γ Δ : Ctx} {σ : Nat → Tm} (hσ : ∀ n A, Γ n = some A → HasType Δ (σ n) A)
    {t : Tm} {A : Ty} (h : HasType Γ t A) : HasType Δ (subst σ t) A := by
  induction h generalizing Δ σ with
  | var hn => exact hσ _ _ hn
  | lam _ ih =>
    refine .lam (ih ?_)
    intro n A hn
    cases n with
    | zero => exact .var hn
    -- WHY: `up σ (n + 1) = rename Nat.succ (σ n)`, so weakening is the renaming lemma.
    | succ n => exact rename_typing (ρ := Nat.succ) (fun _ _ h => h) (hσ n A hn)
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)

-- MILESTONE (optional: change or delete)
/-- Canonical forms: a value of arrow type is a `lam`. -/
theorem value_arr {Γ : Ctx} {v : Tm} {A B : Ty} (hv : Value v) (h : HasType Γ v (.arr A B)) :
    ∃ t, v = .lam A t := by
  cases hv with
  | lam => cases h; exact ⟨_, rfl⟩

-- BEGIN SPEC
theorem preservation {Γ : Ctx} {t t' : Tm} {A : Ty} (h : HasType Γ t A) (hs : Step t t') :
    HasType Γ t' A :=
-- END SPEC
  by
    induction hs generalizing A with
    | beta hv =>
      cases h with
      | app h1 h2 =>
        cases h1 with
        | lam hb =>
          refine subst_typing ?_ hb
          intro n B hn
          cases n with
          | zero => cases hn; exact h2
          | succ n => exact .var hn
    | appL _ ih => cases h with | app h1 h2 => exact .app (ih h1) h2
    | appR _ _ ih => cases h with | app h1 h2 => exact .app h1 (ih h2)

-- BEGIN SPEC
theorem progress {t : Tm} {A : Ty} (h : HasType (fun _ => none) t A) :
    Value t ∨ ∃ t', Step t t' :=
-- END SPEC
  by
    generalize hΓ : (fun _ => none : Ctx) = Γ at h
    induction h with
    | var hn => subst hΓ; cases hn
    | lam _ => exact .inl .lam
    | app h1 _ ih1 ih2 =>
      rcases ih1 hΓ with hv1 | ⟨t', ht'⟩
      · rcases ih2 hΓ with hv2 | ⟨u', hu'⟩
        · obtain ⟨_, rfl⟩ := value_arr hv1 h1
          exact .inr ⟨_, .beta hv2⟩
        · exact .inr ⟨_, .appR hv1 hu'⟩
      · exact .inr ⟨_, .appL ht'⟩

end H026

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Preservation's only real case is `beta`: the body `t` is typed in `Γ.cons A`, and `subst (beta v)` must turn that into a typing in `Γ`. That is a substitution lemma, and pushing a substitution under a `lam` (`up σ`) needs a renaming lemma for `rename Nat.succ`.
H2. Both lemmas: induction on the typing derivation, generalizing the target context and the renaming/substitution. In the `lam` case prove the lifted hypothesis by `cases n`. Preservation: induction on the step generalizing `A`, inverting the typing with `cases`. Progress: generalize the empty context, induction on typing; the `var` case is impossible.
H3. `subst_typing`, `lam` case, index `n + 1`: `rename_typing (ρ := Nat.succ) (fun _ _ h => h) (hσ n A hn)`. Preservation, `beta` case: `cases h with | app h1 h2 => cases h1 with | lam hb => exact subst_typing (fun n B hn => ..) hb` with `n = 0 ↦ h2`, `n + 1 ↦ .var hn`.
-/
