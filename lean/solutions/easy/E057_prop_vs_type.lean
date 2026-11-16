/- E057 | Prop vs Type | 2-3 min | proof irrelevance, Subtype, Sigma, Exists
GOAL
  See what separates proofs from data: any two proofs of a `Prop` are equal, a subtype `{ x // p x }`
  packs a value with a proof, and a Σ-pair `(n : Nat) × T n` (unlike `∃`) lets a function return its witness.

REFERENCE
  example (h1 h2 : 2 < 5) : h1 = h2 := rfl          -- proof irrelevance: two proofs of one Prop are equal
  example : { n : Nat // n > 2 } := ⟨5, by decide⟩       -- subtype value = ⟨value, proof⟩
  example (x : { n : Nat // n > 2 }) : x.val > 2 := x.property   -- `.val` (data), `.property` (proof)
  #check @Subtype.ext   -- a1.val = a2.val → a1 = a2   (the proofs don't matter)
  example : (n : Nat) × Fin (n + 1) := ⟨3, 2⟩            -- Σ-pair: 2nd component's type depends on the 1st
  example (s : (n : Nat) × Fin (n + 1)) : Fin (s.1 + 1) := s.2   -- `.1` / `.2` project
  #check @Fin.isLt      -- (i : Fin n) : ↑i < n      (`↑i`, also `i.val`, is the number inside `i`)
  #check @Nat.le_of_lt_succ   -- m < n.succ → m ≤ n   (`n.succ` is `n + 1`)
NOTE: `def f (h : ∃ n, p n) : Nat := match h with | ⟨n, _⟩ => n` is rejected: an `∃` only eliminates into `Prop`.
-/

namespace E057

-- BEGIN SPEC
def firstOf (s : (n : Nat) × Fin (n + 1)) : Nat := s.1
-- END SPEC

-- BEGIN SPEC
def double (n : Nat) : { m : Nat // m = 2 * n } :=
-- END SPEC
  ⟨2 * n, rfl⟩

-- BEGIN SPEC
theorem proof_irrel (P : Prop) (h1 h2 : P) : h1 = h2 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem subtype_eq (a b : { n : Nat // n % 2 = 0 }) (h : a.val = b.val) : a = b :=
-- END SPEC
  Subtype.ext h

-- BEGIN SPEC
def secondOf (s : (n : Nat) × Fin (n + 1)) : Nat :=
-- END SPEC
  s.2.val

-- BEGIN SPEC
theorem secondOf_mk (n : Nat) (i : Fin (n + 1)) : secondOf ⟨n, i⟩ = i.val :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem secondOf_le (s : (n : Nat) × Fin (n + 1)) : secondOf s ≤ firstOf s :=
-- END SPEC
  Nat.le_of_lt_succ s.2.isLt

end E057

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `double n` must be a pair `⟨value, proof⟩`; `secondOf` returns the number inside the second component.
H2. `proof_irrel` and `secondOf_mk` hold by definition. `subtype_eq` is the card's extensionality lemma.
    For `secondOf_le`, the bound comes from the `Fin` type of `s.2`.
H3. `double n := ⟨2 * n, rfl⟩`; `secondOf s := s.2.val`; `secondOf_le`: `Nat.le_of_lt_succ s.2.isLt`.
-/
