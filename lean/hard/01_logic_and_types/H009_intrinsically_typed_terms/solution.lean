/- H009 | Intrinsically typed terms and a type checker | 1-1.5 h | intrinsic typing, Sigma types, dependent match, type erasure, split
GOAL
  `Expr t` holds only terms of type `t`, so `eval` returns a `t.denote` and cannot fail, and `fold`
  preserves types by its signature. Prove `fold` preserves meaning (warm-up), then that the checker
  from untyped syntax inverts erasure: `check e.erase = some ⟨t, e⟩`, and `check u = some ⟨t, e⟩ → e.erase = u`.

BANNED: grind, import, exact?, apply?, try?

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H009

/- SKELETON · fold_eval   (the last declaration of the spec block below, right after `Expr.fold`)
  1. Induction on the typed term `e`, one case per constructor of `Expr`:          R1
  2. `lit`, `tt`, `ff`: `fold` leaves them unchanged, both sides compute alike:     rfl
  3. `le`: `simp` with `Expr.fold`, `Expr.eval` and the two IHs:                    simp [d, ih]
  4. `plus`, `ite`: unfold `Expr.fold`; the goal shows its inner `match`:           R2
       one goal per arm of that `match`:                                            R3
       each arm: its `heq✝`, the IHs and `Expr.eval` finish it:                     R4
-/
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
  by
    induction e with
    | lit => rfl
    | tt => rfl
    | ff => rfl
    | plus a b iha ihb =>
      simp only [Expr.fold]
      split <;> simp_all [Expr.eval]
    | le a b iha ihb => simp [Expr.fold, Expr.eval, iha, ihb]
    | ite c x y ihc ihx ihy =>
      simp only [Expr.fold]
      split <;> simp_all [Expr.eval]

/- SKELETON · check_erase
  1. Induction on the typed term `e`:                                              R1
  2. `lit`, `tt`, `ff`: `check e.erase` computes to `some ⟨t, e⟩`:                 rfl
  3. `plus`, `le`: unfold `Expr.erase` and `check`, rewrite the recursive calls
     `check a.erase` with the IHs; the checker's `match` then picks its first arm:  R5
  4. `ite`: as in 3; the checker's `if h : t✝ = t✝` is decided by `rfl`:           R5, R6
     (3 and 4 are one `simp` call each, given the definitions and the IHs)
-/
-- BEGIN SPEC
theorem check_erase {t : Ty} (e : Expr t) : check e.erase = some ⟨t, e⟩ :=
-- END SPEC
  by
    induction e with
    | lit => rfl
    | tt => rfl
    | ff => rfl
    | plus a b iha ihb => simp [Expr.erase, check, iha, ihb]
    | le a b iha ihb => simp [Expr.erase, check, iha, ihb]
    -- WHY: in the `ite` case the checker's `if h : t = t` is discharged by `simp` (`dif_pos rfl`).
    | ite c x y ihc ihx ihy => simp [Expr.erase, check, ihc, ihx, ihy]

-- MILESTONE (optional: change or delete)
-- Inversion for `plus`: stated as an equation of Σ-pairs, so no `≍` appears.
/- SKELETON · check_plus_inv   (MILESTONE: prove before check_sound; used in its `plus` case)
  1. Unfold `check` in `h`: `h : (match check a, check b with …) = some ⟨t, e⟩`:    R7
  2. One goal per arm of that `match`:                                             R8
  3. Matching arm: name `a' b'` and the two `check … = some …` equations:          R9
     witnesses `a' b'`; the Σ-equation is `h` read through `some`, flipped:        R10
  4. Fallback arm: `h : none = some ⟨t, e⟩` is impossible:                         R11
-/
theorem check_plus_inv {a b : UExpr} {t : Ty} {e : Expr t} (h : check (.plus a b) = some ⟨t, e⟩) :
    ∃ a' b', check a = some ⟨.nat, a'⟩ ∧ check b = some ⟨.nat, b'⟩ ∧
      (⟨t, e⟩ : Σ t, Expr t) = ⟨.nat, .plus a' b'⟩ := by
  simp only [check] at h
  split at h
  · rename_i a' b' ha hb
    exact ⟨a', b', ha, hb, (Option.some.inj h).symm⟩
  · simp at h

-- MILESTONE (optional: change or delete)
-- Inversion for `ite`: here the result type `t` is shared, so a plain equation `e = …` typechecks.
/- SKELETON · check_ite_inv   (MILESTONE: prove before check_sound; used in its `ite` case)
  1. Unfold `check` in `h`, split the outer `match`; in the matching arm name
     `c' t1 x' t2 y' hc hx hy`:                                                    R7, R8, R9
  2. Split the inner `if h : t1 = t2`; the `isFalse` arm is `none = some _`:       R8, R11
  3. `isTrue` arm: name the equation and substitute it (`t2` becomes `t1`):        R9, R12
  4. `h : some ⟨t1, c'.ite (⋯ ▸ x') y'⟩ = some ⟨t, e⟩`: `simp at h` drops the cast
     and splits the pair into `t1 = t ∧ c'.ite x' y' ≍ e`:                         R13, R14
  5. Substitute the type equation, then the `≍`:                                   R15, R16
  6. Witnesses `c' x' y'`, equations `hc hx hy`, last conjunct by `rfl`:           exact ⟨…⟩
  7. Fallback arm of the outer `match`: impossible:                                R11
-/
theorem check_ite_inv {c x y : UExpr} {t : Ty} {e : Expr t} (h : check (.ite c x y) = some ⟨t, e⟩) :
    ∃ c' x' y', check c = some ⟨.bool, c'⟩ ∧ check x = some ⟨t, x'⟩ ∧ check y = some ⟨t, y'⟩ ∧
      e = .ite c' x' y' := by
  simp only [check] at h
  split at h
  · rename_i c' t1 x' t2 y' hc hx hy
    split at h
    · rename_i heq
      subst heq
      simp at h
      obtain ⟨rfl, h⟩ := h
      cases h
      exact ⟨c', x', y', hc, hx, hy, rfl⟩
    · simp at h
  · simp at h

/- SKELETON · check_sound   (prove the two MILESTONES above first)
  1. Induction on the UNTYPED `u`, generalizing `t e`, so each IH covers
     every typed result `⟨t, e⟩` of checking a subterm:                            R17
  2. `lit`, `tt`, `ff`: unfold `check` in `h` (`simp [check] at h`), which leaves
     `Ty.nat = t ∧ Expr.lit n ≍ e` (or `.bool`); substitute both; then `rfl`:      R14, R15, R16
  3. `plus`: destructure `check_plus_inv h` into `a' b' ha hb heq`:                R18
     substitute the Σ-equation `heq` (`t := .nat`, `e := .plus a' b'`):           R19
     unfold `Expr.erase`, rewrite with the IHs applied to `ha`, `hb`:              simp [d, iha _ _ ha]
  4. `le` (no milestone): check_plus_inv's inversion inline, then step 2's
     substitution in the matching arm:                                             R7, R8, R9, R11, R14, R15, R16
     then as in 3
  5. `ite`: destructure `check_ite_inv h`, with `rfl` for `e = …`:                 R18 (rfl pattern, R15)
     then as in 3, with three IHs
-/
-- BEGIN SPEC
theorem check_sound (u : UExpr) (t : Ty) (e : Expr t) (h : check u = some ⟨t, e⟩) :
    e.erase = u :=
-- END SPEC
  by
    induction u generalizing t e with
    | lit n => simp [check] at h; obtain ⟨rfl, h⟩ := h; cases h; rfl
    | tt => simp [check] at h; obtain ⟨rfl, h⟩ := h; cases h; rfl
    | ff => simp [check] at h; obtain ⟨rfl, h⟩ := h; cases h; rfl
    | plus a b iha ihb =>
      obtain ⟨a', b', ha, hb, heq⟩ := check_plus_inv h
      cases heq
      simp [Expr.erase, iha _ _ ha, ihb _ _ hb]
    | le a b iha ihb =>
      simp only [check] at h
      split at h
      · rename_i a' b' ha hb
        -- WHY: `simp` splits the Σ-equation into a type equation and an `≍`; `rfl` fixes the
        -- type first, and only then can `cases` use the `≍`.
        simp at h; obtain ⟨rfl, h⟩ := h; cases h
        simp [Expr.erase, iha _ _ ha, ihb _ _ hb]
      · simp at h
    | ite c x y ihc ihx ihy =>
      obtain ⟨c', x', y', hc, hx, hy, rfl⟩ := check_ite_inv h
      simp [Expr.erase, ihc _ _ hc, ihx _ _ hx, ihy _ _ hy]

end H009

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three are inductions with one case per constructor (R1, R17). `fold_eval` and `check_erase` go
    by induction on the typed `e`; `check_sound` by induction on the untyped `u`, generalizing `t e`,
    after proving the two MILESTONE inversion lemmas, which do the `match` work once.
H2. In each recursive case unfold the definition (`simp only [Expr.fold]`, `simp only [check] at h`:
    R2, R7) and split on the `match` it exposes (R3, R8); impossible arms close by `simp at h` (R11).
    In matching arms the hypotheses `check a = some ⟨.nat, a'⟩` feed the IHs. A Σ-equation
    `some ⟨t1, x⟩ = some ⟨t, e⟩` comes apart in three steps: `simp at h`, `obtain ⟨rfl, h⟩ := h`,
    `cases h` (R14 → R15 → R16). `ite` has an inner `split at h` on `t1 = t2`, then `subst` (R12).
H3. `fold_eval` plus/ite case: `simp only [Expr.fold]; split <;> simp_all [Expr.eval]`.
    `check_erase`: `simp [Expr.erase, check, iha, ihb]` per case. `check_sound` plus case:
    `obtain ⟨a', b', ha, hb, heq⟩ := check_plus_inv h; cases heq`, then
    `simp [Expr.erase, iha _ _ ha, ihb _ _ hb]`.
-/
