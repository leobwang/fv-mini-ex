/- E029 | Constructor injectivity | 2-3 min | injection, nomatch, nofun, noConfusion
GOAL
  Use the facts that constructors are injective and that different constructors never coincide.

REFERENCE
  inductive T where | leaf | node (a b : Nat)
  example (a b c d : Nat) (h : T.node a b = T.node c d) : a = c ∧ b = d := by
    injection h with h1 h2; exact ⟨h1, h2⟩   -- equal constructors ⇒ equal arguments
  example (a b : Nat) : T.leaf ≠ T.node a b := by intro h; nomatch h   -- distinct ctors
  example (a b : Nat) : T.leaf ≠ T.node a b := nofun   -- same, as a term
  example (a b : Nat) (h : some a = some b) : a = b := by simp at h; exact h  -- simp knows too
-/

-- BEGIN SPEC
inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
-- END SPEC

-- BEGIN SPEC
theorem circle_inj (a b : Nat) (h : Shape.circle a = Shape.circle b) : a = b :=
-- END SPEC
  by injection h

-- BEGIN SPEC
theorem rect_inj (a b c d : Nat) (h : Shape.rect a b = Shape.rect c d) : a = c ∧ b = d :=
-- END SPEC
  by
    injection h with h1 h2
    exact ⟨h1, h2⟩

-- BEGIN SPEC
theorem circle_ne_rect (r w h : Nat) : Shape.circle r ≠ Shape.rect w h :=
-- END SPEC
  nofun

-- BEGIN SPEC
theorem cons_inj_head (x y : Nat) (xs ys : List Nat) (h : x :: xs = y :: ys) : x = y ∧ xs = ys :=
-- END SPEC
  by
    injection h with h1 h2
    exact ⟨h1, h2⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Equal constructor applications have equal arguments; different constructors are never equal.
H2. `injection h with h1 h2` names the argument equations; `nofun` (or `intro h; nomatch h`) refutes a clash.
H3. `injection h`, `injection h with h1 h2; exact ⟨h1, h2⟩`, `nofun`, same as rect for `::`.
-/
