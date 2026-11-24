/- H009 | Intrinsically typed terms and a type checker | 1-1.5 h | intrinsic typing, Sigma types, dependent match, type erasure, split
GOAL
  `Expr t` holds only terms of type `t`, so `eval` returns a `t.denote` and cannot fail, and `fold`
  preserves types by its signature. Prove `fold` preserves meaning (warm-up), then that the checker
  from untyped syntax inverts erasure: `check e.erase = some ⟨t, e⟩`, and `check u = some ⟨t, e⟩ → e.erase = u`.

REFERENCE
  example : (Σ t, H009.Expr t) := ⟨.nat, .lit 3⟩   -- `Σ t, Expr t`: a pair of a type and a term of it
  example (t1 t2 : H009.Ty) (h : t1 = t2) (x : H009.Expr t1) : H009.Expr t2 := h ▸ x  -- cast along h
  -- `split` / `split at h`: one case per arm of the first `match`/`if` in the goal / in h, with the
  --   arm's equations as new (inaccessible) hypotheses; `rename_i a' b' ha hb` names them
  #check @Sigma.mk.inj      -- ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ → a₁ = a₂ ∧ b₁ ≍ b₂    (`simp at h` applies it)
  -- `x ≍ y` is `HEq x y`, equality of terms whose types may differ. After `obtain ⟨rfl, h⟩ := h` makes
  --   the types equal, `cases h` turns `h : x ≍ y` into an equation and substitutes it
  -- `cases h` on `h : (⟨t, e⟩ : Σ t, Expr t) = ⟨.nat, e'⟩` (t, e variables) does both steps at once
  -- `subst h` on `h : t1 = t2` replaces t2 by t1; then `h ▸ x'` is just `x'`
  -- `induction u generalizing t e with …`: the IH must hold for every typed result
BANNED: grind, import, exact?, apply?, try?
NOTE: No imports, no `grind`, no search tactics (`exact?`, `apply?`, `try?`): the point is the manual
  Σ/`≍` inversion, which `grind` would skip.
-/

namespace H009

-- BEGIN SPEC
inductive Ty where
  | nat
  | bool
  deriving DecidableEq

/-- The Lean type of values of each object type. -/
@[reducible] def Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

/-- Intrinsically typed terms: `Expr t` contains only well-typed terms of type `t`. -/
inductive Expr : Ty → Type where
  | lit (n : Nat) : Expr .nat
  | tt : Expr .bool
  | ff : Expr .bool
  | plus (a b : Expr .nat) : Expr .nat
  | le (a b : Expr .nat) : Expr .bool
  | ite {t : Ty} (c : Expr .bool) (x y : Expr t) : Expr t

def Expr.eval : {t : Ty} → Expr t → t.denote
  | _, .lit n => n
  | _, .tt => true
  | _, .ff => false
  | _, .plus a b => a.eval + b.eval
  | _, .le a b => decide (a.eval ≤ b.eval)
  | _, .ite c x y => if c.eval then x.eval else y.eval

/-- Untyped syntax, as a parser would produce it. -/
inductive UExpr where
  | lit (n : Nat)
  | tt
  | ff
  | plus (a b : UExpr)
  | le (a b : UExpr)
  | ite (c x y : UExpr)

/-- Type erasure: forget the index. -/
def Expr.erase : {t : Ty} → Expr t → UExpr
  | _, .lit n => .lit n
  | _, .tt => .tt
  | _, .ff => .ff
  | _, .plus a b => .plus a.erase b.erase
  | _, .le a b => .le a.erase b.erase
  | _, .ite c x y => .ite c.erase x.erase y.erase

/-- The type checker: infer a type and build the typed term, or fail. -/
def check : UExpr → Option (Σ t, Expr t)
  | .lit n => some ⟨.nat, .lit n⟩
  | .tt => some ⟨.bool, .tt⟩
  | .ff => some ⟨.bool, .ff⟩
  | .plus a b =>
    match check a, check b with
    | some ⟨.nat, a'⟩, some ⟨.nat, b'⟩ => some ⟨.nat, .plus a' b'⟩
    | _, _ => none
  | .le a b =>
    match check a, check b with
    | some ⟨.nat, a'⟩, some ⟨.nat, b'⟩ => some ⟨.bool, .le a' b'⟩
    | _, _ => none
  | .ite c x y =>
    match check c, check x, check y with
    | some ⟨.bool, c'⟩, some ⟨t1, x'⟩, some ⟨t2, y'⟩ =>
      if h : t1 = t2 then some ⟨t2, .ite c' (h ▸ x') y'⟩ else none
    | _, _, _ => none

/-- Constant folding on typed terms: its type already says it preserves types. -/
def Expr.fold : {t : Ty} → Expr t → Expr t
  | _, .plus a b =>
    match a.fold, b.fold with
    | .lit m, .lit n => .lit (m + n)
    | a', b' => .plus a' b'
  | _, .ite c x y =>
    match c.fold with
    | .tt => x.fold
    | .ff => y.fold
    | c' => .ite c' x.fold y.fold
  | _, .le a b => .le a.fold b.fold
  | _, e => e

theorem fold_eval {t : Ty} (e : Expr t) : e.fold.eval = e.eval :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem check_erase {t : Ty} (e : Expr t) : check e.erase = some ⟨t, e⟩ :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
-- Inversion for `plus`: stated as an equation of Σ-pairs, so no `≍` appears.
theorem check_plus_inv {a b : UExpr} {t : Ty} {e : Expr t} (h : check (.plus a b) = some ⟨t, e⟩) :
    ∃ a' b', check a = some ⟨.nat, a'⟩ ∧ check b = some ⟨.nat, b'⟩ ∧
      (⟨t, e⟩ : Σ t, Expr t) = ⟨.nat, .plus a' b'⟩ := by
  sorry

-- MILESTONE (optional: change or delete)
-- Inversion for `ite`: here the result type `t` is shared, so a plain equation `e = …` typechecks.
theorem check_ite_inv {c x y : UExpr} {t : Ty} {e : Expr t} (h : check (.ite c x y) = some ⟨t, e⟩) :
    ∃ c' x' y', check c = some ⟨.bool, c'⟩ ∧ check x = some ⟨t, x'⟩ ∧ check y = some ⟨t, y'⟩ ∧
      e = .ite c' x' y' := by
  sorry

-- BEGIN SPEC
theorem check_sound (u : UExpr) (t : Ty) (e : Expr t) (h : check u = some ⟨t, e⟩) :
    e.erase = u :=
-- END SPEC
  sorry

end H009

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three are inductions with one case per constructor. `fold_eval` and `check_erase` go by
    induction on the typed `e`; `check_sound` by induction on the untyped `u` (generalizing `t e`).
H2. Unfold the definition (`simp only [Expr.fold]` / `simp only [check] at h`) and `split` on the
    `match` it exposes; impossible arms close by `simp at h` (`none = some _`). In matching arms the
    hypotheses `check a = some ⟨.nat, a'⟩` feed the IHs. `ite` has an inner `split at h` on `t1 = t2`.
H3. `fold_eval` plus/ite case: `simp only [Expr.fold]; split <;> simp_all [Expr.eval]`.
    `check_erase`: `simp [Expr.erase, check, iha, ihb]` per case. `check_sound`, after inversion:
    `simp at h; obtain ⟨rfl, h⟩ := h; cases h`, then `simp [Expr.erase, iha _ _ ha, ihb _ _ hb]`.
-/
