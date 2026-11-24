/- H026 | STLC progress and preservation with de Bruijn substitutions | 1.5-2 h | simply typed lambda calculus, parallel substitution, renaming lemma, progress and preservation
GOAL
  Call-by-value STLC, de Bruijn indices (M048), contexts `Ctx := Nat → Option Ty` (not M049's lists).
  A renaming `ρ : Nat → Nat` sends free `var n` to `var (ρ n)`; a parallel substitution `σ : Nat → Tm`
  sends it to `σ n`. Prove preservation (`Step` keeps the type) and progress (a closed typed term is a value or steps).

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · rename_typing   (milestone 1: prove first; subst_typing uses it with ρ := Nat.succ)
  1. Induct on the derivation `h`, generalizing the target context and the renaming,
     so the IH works under `lam` (where they are `Ctx.cons A Δ` and `upRen ρ`):
       induction h generalizing Δ ρ with | var hn => … | lam _ ih => … | app _ _ ih1 ih2 => …   R1
     Each goal shows `rename ρ (Tm.var n✝)` etc.; it computes to the rule's shape   R5
  2. var: the var rule applied to `hρ`                                             R2
  3. lam: the lam rule applied to the IH; the IH's premise (lifted `hρ`) is left   R3
       intro n A hn, then index 0 vs n + 1                                         R4
       both cases are `hn` / `hρ n A hn` once Ctx.cons and upRen compute           R5
  4. app: the app rule applied to both IHs, each fed `hρ`                          R2
-/
-- MILESTONE (optional: change or delete)
theorem rename_typing {Γ Δ : Ctx} {ρ : Nat → Nat} (hρ : ∀ n A, Γ n = some A → Δ (ρ n) = some A)
    {t : Tm} {A : Ty} (h : HasType Γ t A) : HasType Δ (rename ρ t) A := by
  sorry

/- SKELETON · subst_typing   (milestone 2: uses rename_typing; preservation uses it)
  1. The same induction as rename_typing, generalizing Δ σ                         R1
  2. var: `hσ` itself (`subst σ (Tm.var n)` computes to `σ n`)                    R5
  3. lam: the lam rule applied to the IH, the lifted `hσ` left as the goal         R3
       intro n A hn, then index 0 vs n + 1                                         R4
       index 0: the var rule on `hn` (`up σ 0` is `Tm.var 0`, `Ctx.cons A✝ _ 0`
       is `some A✝` in both contexts)                                            R2, R5
       index n + 1: `up σ (n + 1)` computes to `rename Nat.succ (σ n)`, so use
       rename_typing with ρ fixed to Nat.succ; its hypothesis is `fun _ _ h => h`  R5, R6
  4. app: the app rule on both IHs fed `hσ`                                        R2
-/
-- MILESTONE (optional: change or delete)
theorem subst_typing {Γ Δ : Ctx} {σ : Nat → Tm} (hσ : ∀ n A, Γ n = some A → HasType Δ (σ n) A)
    {t : Tm} {A : Ty} (h : HasType Γ t A) : HasType Δ (subst σ t) A := by
  sorry

/- SKELETON · value_arr   (milestone 3: canonical forms; progress uses it)
  1. Take `hv` apart: `v` becomes `Tm.lam _ _`                                     R7
  2. Invert `h`: only the lam rule fits, and it makes the binder type `A`         R8
  3. Close `∃ t, Tm.lam A t✝ = Tm.lam A t` with a witness and `rfl`               ⟨_, rfl⟩
-/
-- MILESTONE (optional: change or delete)
/-- Canonical forms: a value of arrow type is a `lam`. -/
theorem value_arr {Γ : Ctx} {v : Tm} {A B : Ty} (hv : Value v) (h : HasType Γ v (.arr A B)) :
    ∃ t, v = .lam A t := by
  sorry

/- SKELETON · preservation   (uses milestone subst_typing)
  1. Induct on the step `hs`, generalizing `A` (`h` is carried into each IH)       R1
  2. beta: invert `h` (app rule), then its function part (lam rule), to get
       hb : HasType (Ctx.cons A✝ Γ) t✝ A                                          R8, R8
     apply subst_typing to `hb`, leaving its hypothesis for `beta v✝` as the goal R3
     intro n B hn, then index 0 vs n + 1                                           R4
       index 0: `hn` computes to `some A✝ = some B`; unify, then `h2`              R9, R5
       index n + 1: the var rule on `hn`                                           R2, R5
  3. appL, appR: invert `h` (app rule), rebuild with the app rule and the IH       R8, R2
-/
-- BEGIN SPEC
theorem preservation {Γ : Ctx} {t t' : Tm} {A : Ty} (h : HasType Γ t A) (hs : Step t t') :
    HasType Γ t' A :=
-- END SPEC
  sorry

/- SKELETON · progress   (uses milestone value_arr)
  1. Make the empty context a variable:
       generalize hΓ : (fun _ => none : Ctx) = Γ at h                              R10
  2. Induct on `h`; every IH now needs `hΓ`                                        R11
  3. var: substitute `hΓ`; then `hn : (fun x => none) n✝ = some A✝` is impossible R12, R13
  4. lam: a value, `.inl .lam`                                                     R2
  5. app (name the function's typing, e.g. `| app h1 _ ih1 ih2`):
     split `ih1 hΓ` (value or step); if a value, split `ih2 hΓ`                   rcases
       both values: value_arr on `h1` turns the left part into a lam, then beta   R14, R2
       value, right part steps: appR;  left part steps: appL                      R2
-/
-- BEGIN SPEC
theorem progress {t : Tm} {A : Ty} (h : HasType (fun _ => none) t A) :
    Value t ∨ ∃ t', Step t t' :=
-- END SPEC
  sorry

end H026

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Preservation's only real case is `beta`: the body `t` is typed in `Ctx.cons A Γ`, and `subst (beta v)`
    must turn that into a typing in `Γ`. That is `subst_typing`; pushing a substitution under a `lam`
    (`up σ`) needs `rename_typing` for `rename Nat.succ`. Progress needs canonical forms (`value_arr`).
H2. Both milestone lemmas: `induction h generalizing Δ ρ` (resp. `Δ σ`); in the `lam` case
    `refine .lam (ih ?_)`, then `intro n A hn; cases n`. Preservation: `induction hs generalizing A`,
    invert `h` with `cases`. Progress: `generalize` the empty context, `induction h`; `var` is impossible.
H3. `subst_typing`, `lam`, index `n + 1`: `exact rename_typing (ρ := Nat.succ) (fun _ _ h => h) (hσ n A hn)`.
    Preservation, `beta`: `cases h with | app h1 h2 => cases h1 with | lam hb => refine subst_typing ?_ hb`,
    then index `0 ↦ cases hn; exact h2`, `n + 1 ↦ exact .var hn`.
    Progress: `generalize hΓ : (fun _ => none : Ctx) = Γ at h`; in `app`, `obtain ⟨_, rfl⟩ := value_arr hv1 h1`.
-/
