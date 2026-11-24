/- M007 | Subtypes | 10 min | Subtype, val, property, Subtype.ext
GOAL
  Work with even naturals as a subtype: build values with proofs, and prove facts about them.

REFERENCE
  abbrev Pos := {n : Nat // 0 < n}                -- value + proof, like Fin
  example : Pos := ⟨5, by decide⟩
  example (p : Pos) : p.val ≠ 0 := by have := p.property; omega   -- `.property : 0 < p.val`
  example (p q : Pos) (h : p.val = q.val) : p = q := Subtype.ext h
  def double (p : Pos) : Pos := ⟨2 * p.val, by have := p.property; omega⟩
  `omega` does not look inside `p.property` by itself: bring it into context with `have`.
-/

namespace M007

-- BEGIN SPEC
abbrev EvenNat := {n : Nat // n % 2 = 0}

def half (a : EvenNat) : Nat := a.val / 2
-- END SPEC

-- BEGIN SPEC
def addE (a b : EvenNat) : EvenNat :=
-- END SPEC
  sorry

-- BEGIN SPEC
def ofHalf (k : Nat) : EvenNat :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem addE_val (a b : EvenNat) : (addE a b).val = a.val + b.val :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem ofHalf_val (k : Nat) : (ofHalf k).val = 2 * k :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem half_addE (a b : EvenNat) : half (addE a b) = half a + half b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem ofHalf_half (a : EvenNat) : ofHalf (half a) = a :=
-- END SPEC
  sorry

end M007

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. To build an `EvenNat` you give a number and a proof that it is even.
H2. For the theorems: bring `a.property` into context, unfold `half`/`addE`/`ofHalf`, then `omega`.
H3. `⟨a.val + b.val, by have := a.property; have := b.property; omega⟩`; `ofHalf_half`: `apply Subtype.ext; have := a.property; simp only [ofHalf, half]; omega`.
-/
