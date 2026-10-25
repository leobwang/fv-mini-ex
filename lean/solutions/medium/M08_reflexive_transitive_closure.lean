/- M08 | Reflexive-transitive closure | 15-20 min | inductive Prop, parameters, induction on derivations
GOAL
  `Star R a b` means b is reachable from a in zero or more `R`-steps. Prove it is transitive,
  and that for the successor relation on Nat it is exactly `≤`.

REFERENCE
  -- Induction on `h : Star R a b` works when a, b are variables; generalise other facts first.
  example {α : Type} (R : α → α → Prop) (a : α) : M08.Star R a a := .refl a
  example {α : Type} (R : α → α → Prop) (a b c : α) (h : R a b) (h2 : M08.Star R b c) :
      M08.Star R a c := .step h h2
  example (a b : Nat) (h : a ≤ b + 1) (h2 : a ≠ b + 1) : a ≤ b := by omega
  -- For ← of the Nat statement, induct on `b`, and use `Nat.le_succ_iff`-style case splits by omega.
-/

namespace M08

-- BEGIN SPEC
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c
-- END SPEC

-- BEGIN SPEC
theorem star_single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
-- END SPEC
  .step h (.refl b)

-- BEGIN SPEC
theorem star_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : Star R b c) : Star R a c :=
-- END SPEC
  by
    induction h1 with
    | refl _ => exact h2
    | step hab _ ih => exact .step hab (ih h2)

-- BEGIN SPEC
theorem star_succ_iff (a b : Nat) : Star (fun n m => m = n + 1) a b ↔ a ≤ b :=
-- END SPEC
  by
    constructor
    · intro h
      induction h with
      | refl _ => omega
      | step hab _ ih => omega
    · intro h
      induction b with
      | zero =>
        have : a = 0 := by omega
        subst this
        exact .refl 0
      | succ b ih =>
        by_cases hab : a = b + 1
        · subst hab
          exact .refl _
        · exact star_trans (ih (by omega)) (star_single rfl)

end M08

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `star_trans`: induct on the first derivation; the second one just comes along.
H2. Nat →: induction on the derivation, each step adds one. Nat ←: induction on `b`; either `a = b + 1` or `a ≤ b`.
H3. `star_trans` step case: `exact .step hab (ih h2)`. Nat ← succ case: `exact star_trans (ih (by omega)) (star_single rfl)`.
-/
