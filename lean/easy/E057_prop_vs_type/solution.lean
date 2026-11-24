/- E057 | Prop vs Type | 2-3 min | proof irrelevance, Subtype, Sigma, Exists
GOAL
  See what separates proofs from data: any two proofs of a `Prop` are equal, a subtype `{ x // p x }`
  packs a value with a proof, and a Σ-pair `(n : Nat) × T n` (unlike `∃`) lets a function return its witness.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E057

-- BEGIN SPEC
def firstOf (s : (n : Nat) × Fin (n + 1)) : Nat := s.1
-- END SPEC

/- SKELETON · double (definition body)
  1. The result is a pair ⟨value, proof⟩: give the value `2 * n`:                 R1
  2. The proof obligation is now `2 * n = 2 * n`: close it by definition:          rfl
-/
-- BEGIN SPEC
def double (n : Nat) : { m : Nat // m = 2 * n } :=
-- END SPEC
  ⟨2 * n, rfl⟩

/- SKELETON · proof_irrel
  1. Two proofs of one `Prop` are the same term to Lean: close it in one step:      R2
-/
-- BEGIN SPEC
theorem proof_irrel (P : Prop) (h1 h2 : P) : h1 = h2 :=
-- END SPEC
  rfl

/- SKELETON · subtype_eq
  1. Equality of subtype values → equality of their `.val`s:                      R3
  2. That is exactly `h`:                                                         exact h
     (R3 as a term does both steps at once.)
-/
-- BEGIN SPEC
theorem subtype_eq (a b : { n : Nat // n % 2 = 0 }) (h : a.val = b.val) : a = b :=
-- END SPEC
  Subtype.ext h

/- SKELETON · secondOf (definition body)
  1. Take the second component, `s.2 : Fin (s.1 + 1)`:                            R4
  2. Return the `Nat` inside that `Fin`:                                          R5
-/
-- BEGIN SPEC
def secondOf (s : (n : Nat) × Fin (n + 1)) : Nat :=
-- END SPEC
  s.2.val

/- SKELETON · secondOf_mk
  1. Unfolding `secondOf` and reducing `⟨n, i⟩.snd` to `i` makes both sides equal:  R7
     (by hand: R8 with `secondOf`, then R6)
-/
-- BEGIN SPEC
theorem secondOf_mk (n : Nat) (i : Fin (n + 1)) : secondOf ⟨n, i⟩ = i.val :=
-- END SPEC
  rfl

/- SKELETON · secondOf_le
  1. The bound lives in the type of `s.2 : Fin (s.1 + 1)`:
       h : ↑s.snd < s.fst + 1                                                     R9
  2. Turn `x < n + 1` into `x ≤ n`:                                               R10
  3. The result is about `↑s.snd` and `s.fst`, the goal about `secondOf s` and
     `firstOf s`; `exact` accepts it after unfolding:                             R11
     (Alternative: R8 on both definitions, then `omega`.)
-/
-- BEGIN SPEC
theorem secondOf_le (s : (n : Nat) × Fin (n + 1)) : secondOf s ≤ firstOf s :=
-- END SPEC
  Nat.le_of_lt_succ s.2.isLt

end E057

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `double n` must be a pair `⟨value, proof⟩` (R1); `secondOf` returns the number inside the second
    component (R4, R5). `proof_irrel` and `secondOf_mk` hold by definition (R2, R7).
H2. `subtype_eq` is subtype extensionality (R3): equal values, and the proofs agree by proof irrelevance.
    For `secondOf_le`, the bound comes from the `Fin` type of `s.2` (R9), turned from `<` into `≤` (R10).
H3. `double n := ⟨2 * n, rfl⟩`; `secondOf s := s.2.val`; `subtype_eq` is `Subtype.ext h`;
    `secondOf_le` is `Nat.le_of_lt_succ s.2.isLt`.
-/
