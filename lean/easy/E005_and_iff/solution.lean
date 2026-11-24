/- E005 | And and Iff | 2-3 min | constructor, obtain, rintro, Iff
GOAL
  Prove that `∧` is commutative and associative (as `↔`), and use an `↔` in both directions.
BANNED: simp, simp_all, grind, and_comm, and_assoc

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · and_comm_iff
  1. Split the `↔` into its two implications:                                    R1
  2. Focus each direction in its own `·` block:                                   R2
  3. In each block: intro the conjunction and name its halves,                   R3 (or intro, R4)
     then build the swapped pair:                                                 R5 (or R6)
-/
-- BEGIN SPEC
theorem and_comm_iff (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
-- END SPEC
  by
    constructor
    · rintro ⟨hp, hq⟩
      exact ⟨hq, hp⟩
    · rintro ⟨hq, hp⟩
      exact ⟨hp, hq⟩

/- SKELETON · and_assoc_iff
  1. Split the `↔`, one `·` block per direction:                                 R1, R2
  2. Direction `→`: the premise is grouped on the left, so the pattern needs
     inner brackets; the goal is grouped on the right (flat brackets):           R8, R9
  3. Direction `←`: the reverse (flat pattern, inner brackets in the pair):       R7, R10
-/
-- BEGIN SPEC
theorem and_assoc_iff (P Q R : Prop) : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
-- END SPEC
  by
    constructor
    · rintro ⟨⟨hp, hq⟩, hr⟩
      exact ⟨hp, hq, hr⟩
    · rintro ⟨hp, hq, hr⟩
      exact ⟨⟨hp, hq⟩, hr⟩

/- SKELETON · iff_both_ways
  1. Goal `False`: work backwards through the hypothesis that concludes `False`:  R13
  2. Goal `Q`: get it from `hp : P` through the left-to-right half of `h`:        R11
     (or in one step: `exact` `hq'` applied to a proof of `Q` built from `hp`   R11, E004 R8)
-/
-- BEGIN SPEC
theorem iff_both_ways (P Q : Prop) (h : P ↔ Q) (hp : P) (hq' : Q → False) : False :=
-- END SPEC
  by
    exact hq' (h.mp hp)

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An `↔` goal is two implications: `constructor` produces both goals (R1); handle each in a `·` block (R2).
    `iff_both_ways` has no `↔` goal: its goal is `False`, so look for the hypothesis that ends in `False`.
H2. In each direction, `rintro ⟨...⟩` takes the conjunction apart (R3, R7, R8), then `exact ⟨...⟩` rebuilds it
    in the new order or grouping (R5, R9, R10). `iff_both_ways`: `apply hq'` turns `False` into `Q` (R13), and
    `h.mp : P → Q` (R11) turns `hp` into a proof of `Q`.
H3. `and_assoc_iff`, direction `→`: `rintro ⟨⟨hp, hq⟩, hr⟩` then `exact ⟨hp, hq, hr⟩` (⟨a, b, c⟩ nests to the
    right). `iff_both_ways`: the proof of `Q` you need is `h.mp hp : Q`.
-/
