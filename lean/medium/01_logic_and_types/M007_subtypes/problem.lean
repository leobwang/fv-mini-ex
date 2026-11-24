/- M007 | Subtypes | 10 min | Subtype, val, property, Subtype.ext
GOAL
  Work with even naturals as a subtype: build values with proofs, and prove facts about them.

GUIDE
  Entries R1–R6: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M007

-- BEGIN SPEC
abbrev EvenNat := {n : Nat // n % 2 = 0}

def half (a : EvenNat) : Nat := a.val / 2
-- END SPEC

/- SKELETON · addE
  1. Give the number `a.val + b.val`; the proof obligation is left:          R1
  2. In the `by` block: bring in the evenness of `a` and of `b`:             R2, R2
  3. Finish the arithmetic with `%`:                                         R3
-/
-- BEGIN SPEC
def addE (a b : EvenNat) : EvenNat :=
-- END SPEC
  sorry

/- SKELETON · ofHalf
  1. Give the number `2 * k`; the proof obligation is left:                  R1
  2. It is arithmetic with no hypothesis needed:                             R3
-/
-- BEGIN SPEC
def ofHalf (k : Nat) : EvenNat :=
-- END SPEC
  sorry

/- SKELETON · addE_val
  1. Both sides compute to the same number once `addE` unfolds:              R4
-/
-- BEGIN SPEC
theorem addE_val (a b : EvenNat) : (addE a b).val = a.val + b.val :=
-- END SPEC
  sorry

/- SKELETON · ofHalf_val
  1. Same as `addE_val`:                                                     R4
-/
-- BEGIN SPEC
theorem ofHalf_val (k : Nat) : (ofHalf k).val = 2 * k :=
-- END SPEC
  sorry

/- SKELETON · half_addE
  1. Bring in the evenness of `a` and of `b` (`/ 2` needs it to split):     R2, R2
  2. Unfold `half` and `addE`; `⟨_, _⟩.val` reduces in the same step:        R5
  3. The goal is now `/ 2` arithmetic about `a.val` and `b.val`:             R3
-/
-- BEGIN SPEC
theorem half_addE (a b : EvenNat) : half (addE a b) = half a + half b :=
-- END SPEC
  sorry

/- SKELETON · ofHalf_half
  1. Equation of `EvenNat` values → equation of their `.val`s:               R6
  2. Bring in the evenness of `a`:                                           R2
  3. Unfold `ofHalf` and `half`:                                             R5
  4. Finish `2 * (a.val / 2) = a.val` with the evenness fact:                R3
-/
-- BEGIN SPEC
theorem ofHalf_half (a : EvenNat) : ofHalf (half a) = a :=
-- END SPEC
  sorry

end M007

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An `EvenNat` is a pair `⟨number, proof that it is even⟩`. Build one with `⟨v, by …⟩` (R1); read it with
    `.val` and `.property` (R2). Every proof here ends in `Nat` arithmetic for `omega` (R3).
H2. Definitions: `⟨a.val + b.val, by …⟩` and `⟨2 * k, by omega⟩`. The two `_val` theorems hold by `rfl` (R4).
    `half_addE`: `have` both properties, `simp only [half, addE]`, `omega`. `ofHalf_half`: first
    `apply Subtype.ext` (R6), then the same pattern.
H3. `⟨a.val + b.val, by have := a.property; have := b.property; omega⟩`;
    `ofHalf_half`: `apply Subtype.ext; have := a.property; simp only [ofHalf, half]; omega`.
-/
