/- H005 | NNF rewriting terminates | 1-1.5 h | termination of rewriting, weight function into Nat, Subrelation.wf, InvImage, Nat.pow
GOAL
  `Rw a b` pushes one negation inward (¬¬a → a, De Morgan) anywhere inside a formula. Prove each
  step preserves meaning, the rewriting terminates (no infinite `Rw` chain: find a weight that
  every step lowers), and the normal forms (no step possible) are exactly the negation normal forms.

REFERENCE
  example (w : Nat → Nat) : WellFounded (fun a b => w a < w b) := InvImage.wf w Nat.lt_wfRel.wf
  example (r q : Nat → Nat → Prop) (h : ∀ {a b}, q a b → r a b) (hr : WellFounded r) :
      WellFounded q := Subrelation.wf h hr                 -- q ⊆ r and r well-founded
  example (x y : Nat) (h : x < y) : 2 ^ x < 2 ^ y := Nat.pow_lt_pow_right (by omega) h
  example (x : Nat) : x < 2 ^ x := Nat.lt_two_pow_self
  example (x : Nat) (h : 1 ≤ x) : 2 ≤ 2 ^ x := by simpa using Nat.pow_le_pow_right (n := 2) (by omega) h
  example (x y : Nat) : 2 ^ (x + y + 1) = 2 ^ x * 2 ^ y * 2 := by rw [Nat.pow_succ, Nat.pow_add]
  example (a b k : Nat) (h : a ≤ b) : k * a ≤ k * b := Nat.mul_le_mul_left k h   -- `_right`: a * k ≤ b * k
  -- `omega` treats `2 ^ x` and `2 ^ x * 2 ^ y` as opaque atoms: give it the needed facts with `have`.
  example (x y : Bool) : (!(x && y)) = (!x || !y) := Bool.not_and x y      -- also `Bool.not_or`
  -- `nomatch h` closes a goal when no constructor of `Rw` can produce `h` (e.g. `h : Rw (.atom n) b`).
BANNED: try?
NOTE: `fun b a => Rw a b` is the converse relation: well-founded means no infinite chain a₀ → a₁ → ….
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

-- BEGIN SPEC
theorem rw_sound {a b : F} (h : Rw a b) (v : Nat → Bool) : eval v b = eval v a :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete): a weight that every step lowers.
def weight : F → Nat := sorry

-- MILESTONE (optional: change or delete)
theorem demorgan_bound (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    2 ^ x + 2 ^ y + 1 < 2 ^ (x + y + 1) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem weight_pos (a : F) : 1 ≤ weight a := by
  sorry

-- MILESTONE (optional: change or delete)
theorem weight_decreases {a b : F} (h : Rw a b) : weight b < weight a := by
  sorry

-- BEGIN SPEC
theorem rw_terminates : WellFounded (fun b a => Rw a b) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem normal_iff_nnf (a : F) : (∀ b, ¬ Rw a b) ↔ IsNNF a :=
-- END SPEC
  sorry

end H005

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Soundness is an induction on the step with `simp [eval, …]`. Termination: map formulas to `Nat` with a weight that every step lowers, then pull back `<` with `InvImage.wf` and finish with `Subrelation.wf`.
H2. Size does not work: De Morgan turns one `neg` into two. Make `neg` exponential so that `¬(a ∧ b)` outweighs `¬a ∨ ¬b`; you then need `2^x + 2^y + 1 < 2^(x+y+1)` for `x, y ≥ 1`. For `normal_iff_nnf`, induct on `a`; in the `neg` case, `cases` on the argument and either exhibit a step or rule all steps out with `nomatch`.
H3. `weight`: atom ↦ 1, `neg a` ↦ `2 ^ weight a`, `and`/`or a b` ↦ `weight a + weight b + 1`. `weight_decreases` is an induction on the step: `negNeg` by `Nat.lt_two_pow_self` twice, De Morgan by `demorgan_bound` with `weight_pos`, congruence by the IH (`Nat.pow_lt_pow_right` under `neg`, `omega` elsewhere).
-/
