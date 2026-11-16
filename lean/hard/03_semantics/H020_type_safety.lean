/- H020 | Type safety | 1-1.5 h | inductive relations, progress, preservation, cases inversion
GOAL
  For a tiny language of numbers and booleans, prove type safety: a well-typed term is a value
  or can step (progress), stepping preserves types (preservation), and types are unique.

REFERENCE
  example : H020.HasType (.plus (.lit 1) (.lit 2)) .nat := .plus .lit .lit
  example : H020.Step (.ite .tt (.lit 1) (.lit 2)) (.lit 1) := .iteT
  -- Inversion: `cases h` on `h : HasType (.plus a b) T` leaves only the `plus` rule (T := .nat).
  -- `cases h` on `h : HasType .tt .nat` closes the goal (no rule matches).
  -- Canonical forms: a value of type nat is a literal; a value of type bool is tt or ff.
  -- progress: `induction h`; preservation: `induction hs generalizing T` then `cases h`.
-/

namespace H020

-- BEGIN SPEC
inductive Ty where
  | nat
  | bool

inductive Tm where
  | lit (n : Nat)
  | tt
  | ff
  | plus (a b : Tm)
  | ite (c t e : Tm)
  | isZero (t : Tm)

inductive HasType : Tm → Ty → Prop
  | lit {n : Nat} : HasType (.lit n) .nat
  | tt : HasType .tt .bool
  | ff : HasType .ff .bool
  | plus {a b : Tm} : HasType a .nat → HasType b .nat → HasType (.plus a b) .nat
  | ite {c t e : Tm} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | isZero {t : Tm} : HasType t .nat → HasType (.isZero t) .bool

inductive Value : Tm → Prop
  | lit {n : Nat} : Value (.lit n)
  | tt : Value .tt
  | ff : Value .ff

inductive Step : Tm → Tm → Prop
  | plusLit {n m : Nat} : Step (.plus (.lit n) (.lit m)) (.lit (n + m))
  | plusL {a a' b : Tm} : Step a a' → Step (.plus a b) (.plus a' b)
  | plusR {a b b' : Tm} : Value a → Step b b' → Step (.plus a b) (.plus a b')
  | iteT {t e : Tm} : Step (.ite .tt t e) t
  | iteF {t e : Tm} : Step (.ite .ff t e) e
  | iteC {c c' t e : Tm} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | isZeroZ : Step (.isZero (.lit 0)) .tt
  | isZeroS {n : Nat} : Step (.isZero (.lit (n + 1))) .ff
  | isZeroC {t t' : Tm} : Step t t' → Step (.isZero t) (.isZero t')
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem canonical_nat {v : Tm} (h : HasType v .nat) (hv : Value v) : ∃ n, v = .lit n := by
  sorry

-- MILESTONE (optional: change or delete)
theorem canonical_bool {v : Tm} (h : HasType v .bool) (hv : Value v) : v = .tt ∨ v = .ff := by
  sorry

-- BEGIN SPEC
theorem progress {t : Tm} {T : Ty} (h : HasType t T) : Value t ∨ ∃ t', Step t t' :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem preservation {t t' : Tm} {T : Ty} (h : HasType t T) (hs : Step t t') : HasType t' T :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem type_unique {t : Tm} {T1 T2 : Ty} (h1 : HasType t T1) (h2 : HasType t T2) : T1 = T2 :=
-- END SPEC
  sorry

end H020

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the two canonical-forms lemmas first (`cases hv` then `cases h`); progress uses them to turn a value of type nat/bool into a concrete constructor.
H2. Progress: `induction h`; in each compound case look at the IH of the leftmost subterm first. Preservation: `induction hs generalizing T`, then invert the typing derivation with `cases h`.
H3. Progress `plus` case: `rcases iha with va | ⟨a', sa⟩`, and if `a` is a value, `rcases ihb ...`; when both are values, `obtain ⟨n, rfl⟩ := canonical_nat ha va`. Preservation `plusL`: `cases h with | plus ha hb => exact .plus (ih ha) hb`.
-/
