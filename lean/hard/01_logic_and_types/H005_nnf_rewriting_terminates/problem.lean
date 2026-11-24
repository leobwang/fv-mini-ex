/- H005 | NNF rewriting terminates | 1-1.5 h | termination of rewriting, weight function into Nat, Subrelation.wf, InvImage, Nat.pow
GOAL
  `Rw a b` pushes one negation inward (¬¬a → a, De Morgan) anywhere inside a formula. Prove each
  step preserves meaning, the rewriting terminates (no infinite `Rw` chain: find a weight that
  every step lowers), and the normal forms (no step possible) are exactly the negation normal forms.
BANNED: try?

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H005

-- BEGIN SPEC
inductive F where
  | atom (n : Nat)
  | neg (a : F)
  | and (a b : F)
  | or (a b : F)

/-- One rewrite step towards negation normal form, anywhere inside a formula. -/
inductive Rw : F → F → Prop
  | negNeg {a : F} : Rw (.neg (.neg a)) a
  | negAnd {a b : F} : Rw (.neg (.and a b)) (.or (.neg a) (.neg b))
  | negOr {a b : F} : Rw (.neg (.or a b)) (.and (.neg a) (.neg b))
  | neg {a a' : F} : Rw a a' → Rw (.neg a) (.neg a')
  | andL {a a' b : F} : Rw a a' → Rw (.and a b) (.and a' b)
  | andR {a b b' : F} : Rw b b' → Rw (.and a b) (.and a b')
  | orL {a a' b : F} : Rw a a' → Rw (.or a b) (.or a' b)
  | orR {a b b' : F} : Rw b b' → Rw (.or a b) (.or a b')

/-- Negation normal form: `neg` only directly on atoms. -/
def IsNNF : F → Prop
  | .atom _ => True
  | .neg (.atom _) => True
  | .neg _ => False
  | .and a b => IsNNF a ∧ IsNNF b
  | .or a b => IsNNF a ∧ IsNNF b

/-- Truth value under the assignment `v` of atoms. -/
def eval (v : Nat → Bool) : F → Bool
  | .atom n => v n
  | .neg a => !eval v a
  | .and a b => eval v a && eval v b
  | .or a b => eval v a || eval v b
-- END SPEC

/- SKELETON · rw_sound
  1. Induct on the step `h` (not on a formula): eight goals, one per constructor of `Rw`;
     the five congruence constructors (neg, andL, andR, orL, orR) also get an IH:      R1, R2
  2. negNeg: unfold `eval`; `!!x = x` finishes it:                                     R3, R4
  3. negAnd: unfold `eval`, push `!` through `&&`:                                     R3, R5
     negOr:  unfold `eval`, push `!` through `||`:                                     R3, R6
  4. The five congruence cases, as ONE shared alternative `| c₁ _ ih | … =>`:
     unfold `eval` and rewrite with the IH:                                            R2, R3, R7
-/
-- BEGIN SPEC
theorem rw_sound {a b : F} (h : Rw a b) (v : Nat → Bool) : eval v b = eval v a :=
-- END SPEC
  sorry

/- SKELETON · weight   (milestone; used by everything up to rw_terminates)
  1. One clause per constructor of `F`, recursing on the children:                     R8
  2. It must drop under EVERY rule. Size fails for De Morgan (cheatsheet Part 2):
     the `neg` clause must grow faster than the and/or clauses. Check candidates with
     `rfl` on small formulas before proving anything:                                  R8
-/
-- MILESTONE (optional: change or delete): a weight that every step lowers.
def weight : F → Nat := sorry

/- SKELETON · demorgan_bound   (milestone; used by weight_decreases, negAnd and negOr)
  1. Two facts first: `2 ≤ 2 ^ x` from hx, `2 ≤ 2 ^ y` from hy:                         R9 → R10 (twice)
  2. Rewrite `2 ^ (x + y + 1)` into `2 ^ x * 2 ^ y * 2`:                                R11, R12
  3. `omega` sees `2 ^ x`, `2 ^ y`, `2 ^ x * 2 ^ y` as unrelated atoms: first `have`
     the two bounds that link them (`2 * 2 ^ y ≤ …`, `2 ^ x * 2 ≤ …`), then close:      R13, R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem demorgan_bound (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2 ^ x + 2 ^ y + 1 < 2 ^ (x + y + 1) := by
  sorry

/- SKELETON · weight_pos   (milestone; used by weight_decreases, negAnd and negOr)
  1. Case on `a` (no IH needed) and unfold `weight` in every goal:                     R16, R3
  2. The `neg` goal is `1 ≤ 2 ^ _`:                                                    R2, R17
  3. The other goals are linear:                                                      all_goals R15
-/
-- MILESTONE (optional: change or delete)
theorem weight_pos (a : F) : 1 ≤ weight a := by
  sorry

/- SKELETON · weight_decreases   (milestone; used by rw_terminates)
  1. Induct on the step `h`:                                                          R1, R2
  2. negNeg: the goal `weight a < weight a.neg.neg` is by definition
     `weight a < 2 ^ 2 ^ weight a`; chain two `n < 2 ^ n` (`exact` and `apply` see
     through `weight`, no unfolding needed):                                          R19, R18
  3. negAnd, negOr (one shared alternative `| negAnd | negOr =>`): after unfolding
     `weight` (R3) the goal is literally the milestone `demorgan_bound`; its two side
     conditions come from the milestone `weight_pos`
  4. neg: the IH under `2 ^ _`; side goal `1 < 2` by omega:                           R20
  5. andL, andR, orL, orR (one shared alternative): unfold `weight`, then omega
     with the IH:                                                                     R3, R15
-/
-- MILESTONE (optional: change or delete)
theorem weight_decreases {a b : F} (h : Rw a b) : weight b < weight a := by
  sorry

/- SKELETON · rw_terminates
  0. Prove the MILESTONES above first, in order: weight, demorgan_bound, weight_pos,
     weight_decreases. Only weight_decreases is used here.
  1. `<` on Nat is well-founded; pull it back along `weight`:                          R21, R22
  2. The converse step relation `fun b a => Rw a b` is contained in that pullback:
     a step `y → x` gives `weight x < weight y` by weight_decreases:                   R24
  3. Combine 2 and 1:                                                                  R23
     (Steps 1–3 fit in one term; see W2.)
-/
-- BEGIN SPEC
theorem rw_terminates : WellFounded (fun b a => Rw a b) :=
-- END SPEC
  sorry

/- SKELETON · normal_iff_nnf
  1. Induct on the formula `a`: four goals; `and`/`or` get two IHs, each an `↔`:        R25, R2
  2. atom: split the ↔:                                                               R26
       → `intro _` first (`trivial` does not introduce), then `IsNNF (.atom n)` is True: R27
       ← `intro _ b hb`; no step starts at an atom:                                   R30, R28
  3. neg a: the IH is not needed; case on `a`, and split the ↔ in each case:          R16, R26
       atom:          → `intro _`, then True (R27);
                      ← `intro _ b hb`; every step out of `.neg (.atom n)` is
                      `Rw.neg` of a step out of an atom:                              R30, R29, R28
       neg, and, or:  → a step exists (negNeg / negAnd / negOr), contradiction:       R31
                      ← `IsNNF` of it reduces to False:                               R28
  4. and a b (or a b is the same): split the ↔:                                      R26
       → `IsNNF (a.and b)` unfolds to `IsNNF a ∧ IsNNF b`: split it (`constructor`);
         each child is normal, because a child's step lifts by `.andL` / `.andR`:     R32, R30, R31
       ← destructure `IsNNF`, case on the step (andL / andR); `iha.mpr ha` says no
         step leaves the child, so apply it to the child's step:                      R33, R29, R32
-/
-- BEGIN SPEC
theorem normal_iff_nnf (a : F) : (∀ b, ¬ Rw a b) ↔ IsNNF a :=
-- END SPEC
  sorry

end H005

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Soundness is an induction on the step `h` with `simp [eval, …]` (R1–R7). Termination: map formulas to
    `Nat` by a weight that every step lowers, pull back `<` with `InvImage.wf`, finish with
    `Subrelation.wf` (R21–R24). Normal forms: induction on `a`, and `nomatch` for impossible steps.
H2. Size does not work: De Morgan turns one `neg` into two. Make `neg` exponential so that `¬(a ∧ b)`
    outweighs `¬a ∨ ¬b`; you then need `2^x + 2^y + 1 < 2^(x+y+1)` for `x, y ≥ 1` (demorgan_bound).
    For `normal_iff_nnf`, in the `neg` case, `cases` on the argument and either exhibit a step
    (`absurd .negNeg (h _)`) or rule all steps out with `nomatch`.
H3. `weight`: atom ↦ 1, `neg a` ↦ `2 ^ weight a`, `and`/`or a b` ↦ `weight a + weight b + 1`.
    `weight_decreases`: `negNeg` by `Nat.lt_trans Nat.lt_two_pow_self Nat.lt_two_pow_self`, De Morgan by
    `demorgan_bound _ _ (weight_pos _) (weight_pos _)`, `neg` by `Nat.pow_lt_pow_right (by omega) ih`,
    the rest by `simp only [weight]; omega`. `rw_terminates` is a single term: `Subrelation.wf` applied
    to `fun h => weight_decreases h` and to `InvImage.wf weight` of the fact from R21.
-/
