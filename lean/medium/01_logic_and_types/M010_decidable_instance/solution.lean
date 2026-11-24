/- M010 | Decidable instance | 10-15 min | Decidable, DecidablePred, decidable_of_iff, decide
GOAL
  `IsSquare n` quantifies over all `k`, so Lean cannot decide it. Provide a `DecidablePred`
  instance by reducing it to a bounded search, then let `decide` settle concrete cases.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M010

-- BEGIN SPEC
def IsSquare (n : Nat) : Prop := ∃ k, k * k = n
-- END SPEC

/- SKELETON · decIsSquare
  1. Take the number:                                                        R1
  2. Decide the bounded search instead; it is decidable by R3:              R2
       q := ∃ k, k ≤ n ∧ k * k = n
     The `↔` proof goes in `(by …)` (or in a helper theorem placed above).
  3. Inside it, split the two directions:                                    R4
  4. → (bounded ⇒ IsSquare): take the witness apart, rebuild without the
     bound:                                                                  R5 → R6
  5. ← (IsSquare ⇒ bounded): take `⟨k, hk⟩` apart, rebuild with the bound
     left open, then prove `k ≤ n`:                                         R5 → R6 → R7 → R8
-/
-- BEGIN SPEC
instance decIsSquare : DecidablePred IsSquare :=
-- END SPEC
  fun n => decidable_of_iff (∃ k, k ≤ n ∧ k * k = n) (by
    constructor
    · rintro ⟨k, _, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; exact Nat.le_mul_self k, hk⟩)

/- SKELETON · square_49
  1. A closed goal: `decide` evaluates your instance `decIsSquare`:          R9
-/
-- BEGIN SPEC
theorem square_49 : IsSquare 49 :=
-- END SPEC
  by decide

/- SKELETON · not_square_50
  1. The negation of a decidable statement is decidable; evaluate it:       R9
-/
-- BEGIN SPEC
theorem not_square_50 : ¬ IsSquare 50 :=
-- END SPEC
  by decide

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. If `k * k = n` then `k ≤ k * k = n`, so it is enough to search `k ≤ n`: a bounded `∃` that core Lean
    already decides (R3). Once the instance exists, both theorems are a single tactic (R9).
H2. `fun n => decidable_of_iff (∃ k, k ≤ n ∧ k * k = n) (by …)` (R1, R2). Prove the `↔` with
    `constructor` (R4); each direction is `rintro` then an anonymous constructor (R5, R6). The `←`
    direction also needs the bound `k ≤ n`: rewrite `n` back to `k * k` (R7) and use R8.
H3. ←: `rintro ⟨k, hk⟩; exact ⟨k, by rw [← hk]; exact Nat.le_mul_self k, hk⟩`.
    Then `square_49` and `not_square_50` are both `by decide`.
-/
