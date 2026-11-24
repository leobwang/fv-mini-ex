/- H020 | Type safety | 1-1.5 h | inductive relations, progress, preservation, cases inversion
GOAL
  For a tiny language of numbers and booleans, prove type safety: a well-typed term is a value
  or can step (progress), stepping preserves types (preservation), and types are unique.

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · canonical_nat   (milestone 1: used in progress, cases plus and isZero)
  1. Split the value `hv`: three goals lit, tt, ff; `v` becomes each shape:            R1
  2. lit: the witness is the literal itself:                                            R2
  3. tt, ff: `h` now types `tt`/`ff` at `nat`, which no rule derives:                   R3
-/
-- MILESTONE (optional: change or delete)
theorem canonical_nat {v : Tm} (h : HasType v .nat) (hv : Value v) : ∃ n, v = .lit n := by
  cases hv with
  | lit => exact ⟨_, rfl⟩
  | tt => cases h
  | ff => cases h

/- SKELETON · canonical_bool   (milestone 2: used in progress, case ite)
  1. Split the value `hv`:                                                              R1
  2. lit: `h` types a literal at `bool`, impossible:                                    R3
  3. tt, ff: pick the side of `∨`, proved by `rfl`:                                     R4
-/
-- MILESTONE (optional: change or delete)
theorem canonical_bool {v : Tm} (h : HasType v .bool) (hv : Value v) : v = .tt ∨ v = .ff := by
  cases hv with
  | lit => cases h
  | tt => exact Or.inl rfl
  | ff => exact Or.inr rfl

/- SKELETON · progress
  Prove canonical_nat and canonical_bool first; steps 3–5 use them.
  1. Induction on the typing derivation `h`, naming premises and IHs; six goals:       R5
  2. lit, tt, ff: a value, by the matching `Value` rule:                                R4
  The split in R7 gives the value goal first, then the step goal.
  3. plus: go right, split the IH of `a`:                                               R6, R7
       `a` value, split the IH of `b`:                                                  R7
         `b` value          → canonical_nat on both, then `Step.plusLit`               R8, R8, R9
         `b` steps          → `Step.plusR` (needs the value of `a`)                     R9
       `a` steps            → `Step.plusL`                                              R9
  4. ite: go right, split the IH of `c`:                                                R6, R7
       `c` value            → canonical_bool, two goals, `Step.iteT` / `Step.iteF`     R10, R9
       `c` steps            → `Step.iteC`                                               R9
  5. isZero: go right, split the IH of `t`:                                             R6, R7
       `t` value            → canonical_nat, then split the literal into 0 / n + 1,
                              `Step.isZeroZ` / `Step.isZeroS`                          R8, R11, R9
       `t` steps            → `Step.isZeroC`                                            R9
-/
-- BEGIN SPEC
theorem progress {t : Tm} {T : Ty} (h : HasType t T) : Value t ∨ ∃ t', Step t t' :=
-- END SPEC
  by
    induction h with
    | lit => exact Or.inl .lit
    | tt => exact Or.inl .tt
    | ff => exact Or.inl .ff
    | plus ha hb iha ihb =>
      right
      rcases iha with va | ⟨a', sa⟩
      · rcases ihb with vb | ⟨b', sb⟩
        · obtain ⟨n, rfl⟩ := canonical_nat ha va
          obtain ⟨m, rfl⟩ := canonical_nat hb vb
          exact ⟨_, .plusLit⟩
        · exact ⟨_, .plusR va sb⟩
      · exact ⟨_, .plusL sa⟩
    | ite hc ht he ihc iht ihe =>
      right
      rcases ihc with vc | ⟨c', sc⟩
      · rcases canonical_bool hc vc with rfl | rfl
        · exact ⟨_, .iteT⟩
        · exact ⟨_, .iteF⟩
      · exact ⟨_, .iteC sc⟩
    | isZero ht iht =>
      right
      rcases iht with vt | ⟨t', st⟩
      · obtain ⟨n, rfl⟩ := canonical_nat ht vt
        cases n with
        | zero => exact ⟨_, .isZeroZ⟩
        | succ n => exact ⟨_, .isZeroS⟩
      · exact ⟨_, .isZeroC st⟩

/- SKELETON · preservation
  1. Induction on the STEP `hs`, generalizing `T` (IH: `∀ {T}, HasType a T → HasType a' T`): R12
     nine goals, one per `Step` rule; `h` types the left-hand side of that rule
  2. Computation rules (plusLit, isZeroZ, isZeroS): invert `h` (fixes `T` to nat / bool),
     then the premise-free rule `.lit` / `.tt` / `.ff` proves the goal:              R13, then
     `exact` as in the last line of R14
     iteT, iteF: invert `h`; the needed branch typing is one of its premises:          R13
  3. Congruence rules (plusL, plusR, iteC, isZeroC): invert `h`, rebuild the same rule
     with the IH on the subterm that stepped:                                          R13, R15
  Model: guide W3 (same shape on the toy language).
-/
-- BEGIN SPEC
theorem preservation {t t' : Tm} {T : Ty} (h : HasType t T) (hs : Step t t') : HasType t' T :=
-- END SPEC
  by
    induction hs generalizing T with
    | plusLit => cases h; exact .lit
    | plusL _ ih => cases h with | plus ha hb => exact .plus (ih ha) hb
    | plusR _ _ ih => cases h with | plus ha hb => exact .plus ha (ih hb)
    | iteT => cases h with | ite _ ht _ => exact ht
    | iteF => cases h with | ite _ _ he => exact he
    | iteC _ ih => cases h with | ite hc ht he => exact .ite (ih hc) ht he
    | isZeroZ => cases h; exact .tt
    | isZeroS => cases h; exact .ff
    | isZeroC _ ih => cases h with | isZero ht => exact .isZero (ih ht)

/- SKELETON · type_unique
  1. Induction on `h1`, generalizing `T2` (IHs: `∀ {T2}, HasType a T2 → T = T2`):       R5 with R12's generalizing
  2. lit, tt, ff, plus, isZero: invert `h2`, which fixes `T2`; the goal is then `rfl`:  R14, R13, rfl
  3. ite: invert `h2`; its then-branch typing at `T2` goes into the then-branch IH:     R13, R15
-/
-- BEGIN SPEC
theorem type_unique {t : Tm} {T1 T2 : Ty} (h1 : HasType t T1) (h2 : HasType t T2) : T1 = T2 :=
-- END SPEC
  by
    induction h1 generalizing T2 with
    | lit => cases h2; rfl
    | tt => cases h2; rfl
    | ff => cases h2; rfl
    | plus => cases h2; rfl
    | ite _ _ _ _ iht _ => cases h2 with | ite _ ht2 _ => exact iht ht2
    | isZero => cases h2; rfl

end H020

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the canonical-forms milestones first (R1, then R2/R3/R4): progress needs them to turn "a value of type nat/bool" into a concrete `lit n` / `tt` / `ff`, so that a computation rule such as `Step.plusLit` or `Step.iteT` matches. Preservation and type_unique need no milestone: they are inductions plus inversion (`cases h`).
H2. progress: `induction h` (R5); in each compound case go `right` and `rcases` the IH of the leftmost subterm (R6, R7): a step gives a congruence step, a value goes to the next subterm or to canonical forms (R8, R10, R11). preservation: `induction hs generalizing T` (R12) and invert `h` with `cases h` in each case (R13, R14). type_unique: `induction h1 generalizing T2`, then `cases h2` in each case.
H3. progress `plus` case: `rcases iha with va | ⟨a', sa⟩`; if `a` is a value, `rcases ihb …`; when both are values, `obtain ⟨n, rfl⟩ := canonical_nat ha va` (R8) twice, then `exact ⟨_, .plusLit⟩`. preservation `plusL`: `cases h with | plus ha hb => exact .plus (ih ha) hb` (R13, R15). type_unique `ite`: `cases h2 with | ite _ ht2 _ => exact iht ht2`.
-/
