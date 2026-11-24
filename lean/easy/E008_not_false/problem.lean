/- E008 | Not and False | 2-3 min | Not, False, absurd, contradiction, exfalso
GOAL
  Prove facts about negation. Remember `¬P` is defined as `P → False`.
BANNED: simp, simp_all, grind, not_or

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · not_and_not
  1. Open the `¬` and split the `∧` in one step; the goal becomes `False`:       R3
  2. Apply the negation in the context to the other hypothesis:                R2
     (or: let Lean find the clash itself:                                       R4)
-/
-- BEGIN SPEC
theorem not_and_not (P : Prop) : ¬(P ∧ ¬P) :=
-- END SPEC
  sorry

/- SKELETON · contrapositive
  1. Three arrows, the third hidden inside `¬P`: introduce three names;
     the goal becomes `False`:                                                  R5
  2. Chain the two functions, inside out, into `False`:                         R6
-/
-- BEGIN SPEC
theorem contrapositive (P Q : Prop) : (P → Q) → ¬Q → ¬P :=
-- END SPEC
  sorry

/- SKELETON · from_clash
  1. `Q` is unrelated to `P`: switch the goal to `False`:                        R7
  2. `h hp : ¬P`; apply it to `hp` once more to get `False`:                    R2, R6
     (or, instead of 1–2, one step with the `¬P` given by `h hp`:               R8)
  `contradiction` (R4) fails here: no `¬P` sits in the context.
-/
-- BEGIN SPEC
theorem from_clash (P Q : Prop) (hp : P) (h : P → ¬P) : Q :=
-- END SPEC
  sorry

/- SKELETON · not_or_iff
  1. Split the `↔` into `mp` (→) and `mpr` (←), focus each with `·`:              R9
  2. → : introduce `h : ¬(P ∨ Q)` (plain `intro`, E003), then give the pair:      R12
       each component is a lambda (R10) that feeds `h` an `∨` (R11):            R10 → R11
  3. ← : one `rintro` with the `∧` pattern of R3 followed by the `∨` pattern
     of R13; it leaves two `False` goals, focus each with `·`:                    R3, R13
       in each, apply the matching negation:                                    R2
-/
-- BEGIN SPEC
theorem not_or_iff (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A goal `¬X` is the function goal `X → False`: `intro hx` (or `rintro` with a pattern) and aim for
    `False`. A hypothesis `hn : ¬X` is used by applying it: `hn hx : False`.
H2. `not_and_not`: `rintro ⟨hp, hn⟩`. `contrapositive`: three names with `intro`, then `hnq (hpq hp)`.
    `from_clash`: `exfalso`, then `h hp : ¬P` applied to `hp`. `not_or_iff`: `constructor`; → is a
    pair of lambdas, ← is a `rintro` that splits the `∧` and then the `∨`.
H3. `from_clash`: `exact h hp hp` after `exfalso` (or `exact absurd hp (h hp)`). `not_or_iff` →:
    `intro h; exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩`; ←: `rintro ⟨hnp, hnq⟩ (hp | hq)`.
-/
