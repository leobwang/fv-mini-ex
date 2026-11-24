/- E019 | Add instance | 3 min | instance, Add, type classes, ext
GOAL
  Give 2D integer vectors an `Add` instance so `p + q` works, then prove `+` is commutative.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
@[ext] structure V2 where
  x : Int
  y : Int
-- END SPEC

/- SKELETON · instAddV2 (instance body)
  1. An `Add V2` value is one function `V2 → V2 → V2` (the class field `add`):       R1
  2. Write it as an anonymous constructor around a `fun p q => …`:                   R2
  3. The result is a `V2` built field by field, `x` then `y`; `add_fields` says
     each field is the `Int` sum of the corresponding fields of `p` and `q`.
-/
-- BEGIN SPEC
instance instAddV2 : Add V2 :=
-- END SPEC
  sorry

/- SKELETON · add_fields
  1. Split the `∧`: the term `⟨_, _⟩` (E004 R2), or the tactic `constructor`
     (TACTIC_STATES "Structure").
  2. Each half holds by definition: `+` unfolds to your instance, its body to a
     `V2` value whose projection reduces (R3 → R4); `rfl` does all of it:            R5
-/
-- BEGIN SPEC
theorem add_fields (p q : V2) : (p + q).x = p.x + q.x ∧ (p + q).y = p.y + q.y :=
-- END SPEC
  sorry

/- SKELETON · add_comm_v2
  1. Equality of two `V2`s → one goal per field (`case x`, `case y`):                 R6
  2. Each field goal unfolds (R3 → R4) to an `Int` commutativity statement;
     `exact` accepts the lemma for that unfolded form directly (W1):                  R7
-/
-- BEGIN SPEC
theorem add_comm_v2 (p q : V2) : p + q = q + p :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `add_fields` fixes the instance: the sum is computed coordinate-wise. Once the instance says so,
    both of its halves hold by definition, and commutativity reduces to commutativity of `Int`.
H2. Instance: an anonymous constructor around a two-argument function returning a `V2` (R1, R2).
    `add_fields`: a pair of definitional proofs (R5). `add_comm_v2`: split into fields with the
    `@[ext]` lemma (R6), then the `Int` lemma on each field (R7).
H3. `instance instAddV2 : Add V2 := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩`; `add_fields` is `⟨rfl, rfl⟩`;
    `add_comm_v2`: `apply V2.ext`, then `exact Int.add_comm p.x q.x` and `exact Int.add_comm p.y q.y`.
-/
