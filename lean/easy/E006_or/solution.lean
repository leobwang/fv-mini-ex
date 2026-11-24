/- E006 | Or | 2-3 min | cases, rcases, left, right, Or
GOAL
  Prove that `∨` is commutative and that `∧` distributes over `∨`.
BANNED: simp, simp_all, grind, or_comm, and_or_left

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · or_swap
  1. Move the premise into the context:                                         intro h
  2. Split `h : P ∨ Q` into its two cases, BEFORE choosing a side of the goal:   R1 (or R2)
  3. In each case pick the side of `Q ∨ P` where the proof you have fits:
       case `hp : P`: the right side                                             R3, then exact
       case `hq : Q`: the left side                                              R4, then exact
     (or in one step: R6 / R5)
-/
-- BEGIN SPEC
theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P :=
-- END SPEC
  by
    intro h
    cases h with
    | inl hp => right; exact hp
    | inr hq => left; exact hq

/- SKELETON · and_or_distrib
  1. Split the `↔`, one `·` block per direction:                                 constructor, ·  (E005 R1, R2)
  2. Direction `→`: intro and split `P ∧ (Q ∨ R)` in one nested pattern:          R7
     two goals; in each, choose the side of `P ∧ Q ∨ P ∧ R` and build the pair:  R4 / R3, then exact ⟨_, _⟩
  3. Direction `←`: the premise `P ∧ Q ∨ P ∧ R` is an `∨` of two `∧`s:            R8 (parentheses!)
     two goals; in each, build `P ∧ (Q ∨ R)` with the matching side of the `∨`:  R9 (Or.inl / Or.inr)
-/
-- BEGIN SPEC
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
-- END SPEC
  by
    constructor
    · rintro ⟨hp, hq | hr⟩
      · left; exact ⟨hp, hq⟩
      · right; exact ⟨hp, hr⟩
    · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
      · exact ⟨hp, Or.inl hq⟩
      · exact ⟨hp, Or.inr hr⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. To use `h : A ∨ B`, split it into its two cases (R1, R2); to prove `A ∨ B`, choose a side (R3–R6).
    Split first, choose second: the right choice is different in each case.
H2. `or_swap`: `intro h`, then `cases h with | inl hp => … | inr hq => …`; the `P` case goes right, the `Q`
    case left. `and_or_distrib`: `constructor`, then in each direction one `rintro` with a nested pattern
    takes the premise apart into two cases (R7, R8).
H3. `rintro ⟨hp, hq | hr⟩` for →; each of its two goals `P ∧ Q ∨ P ∧ R` needs a side (R4 / R3) before the pair.
    `rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)` for ← (parentheses needed); each goal `P ∧ (Q ∨ R)` is one pair (R9).
-/
