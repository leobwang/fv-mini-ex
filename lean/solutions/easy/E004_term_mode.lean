/- E004 | Term-mode proofs | 2-3 min | fun, anonymous constructor, term mode
GOAL
  Prove the statements as terms (no `by`): proofs are functions and pairs.

REFERENCE
  example (P : Prop) : P → P := fun hp => hp          -- a proof of P → Q is a function
  example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩  -- anonymous constructor
  example (P Q : Prop) (h : P ∧ Q) : Q := h.2         -- projections `.1` / `.2`
  example (P Q : Prop) : P ∧ Q → P := fun ⟨hp, _⟩ => hp   -- pattern-matching lambda
  example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := h.1 hp -- `↔` is a pair of functions too
BANNED: by
NOTE: `by` is banned here on purpose: write every proof as a term.
-/

-- BEGIN SPEC
theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
-- END SPEC
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

-- BEGIN SPEC
theorem curry_and (P Q R : Prop) : (P ∧ Q → R) → P → Q → R :=
-- END SPEC
  fun h hp hq => h ⟨hp, hq⟩

-- BEGIN SPEC
theorem uncurry_and (P Q R : Prop) : (P → Q → R) → P ∧ Q → R :=
-- END SPEC
  fun h hpq => h hpq.1 hpq.2

-- BEGIN SPEC
theorem and_imp_iff (P Q R : Prop) (h : P ↔ Q) (hr : Q → R) : P → R ∧ Q :=
-- END SPEC
  fun hp => ⟨hr (h.1 hp), h.1 hp⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read each `→` as "takes an argument" and each `∧` as "build a pair".
H2. Start every term with `fun ... =>` binding the premises, then assemble the result with `⟨_, _⟩`.
H3. `and_swap`: `fun ⟨hp, hq⟩ => ⟨hq, hp⟩`; `uncurry_and`: `fun h hpq => h hpq.1 hpq.2`.
-/
