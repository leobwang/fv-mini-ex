/- E081 | Quotients | 3 min | Setoid, Quotient.mk, Quotient.lift, Quotient.sound, Quotient.exact
GOAL
  `Parity` is ℕ modulo "same remainder mod 2". Define `Parity.isEven` with `Quotient.lift` (proving it
  respects the relation), then show when two classes are equal.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E081

-- BEGIN SPEC
def parityRel : Setoid Nat where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

def Parity : Type := Quotient parityRel

def Parity.mk (n : Nat) : Parity := Quotient.mk parityRel n
-- END SPEC

/- SKELETON · Parity.isEven
  1. Lift the function on representatives `fun n => n % 2 == 0`; what is left
     is its obligation  ∀ (a b : Nat), a ≈ b → (a % 2 == 0) = (b % 2 == 0):   R1
  2. Bind `a`, `b` and the hypothesis, ascribed in its unfolded form
       h : a % 2 = b % 2                                                       R2
  3. Close the obligation by rewriting with `h`:                              R3
  The body is a term: `Quotient.lift f (fun a b (h : …) => by …)`.
-/
-- BEGIN SPEC
def Parity.isEven : Parity → Bool :=
-- END SPEC
  sorry

/- SKELETON · isEven_mk
  1. Every name on the left is a definition: `Parity.mk` unfolds to
     `Quotient.mk parityRel n`, `Parity.isEven` to your `Quotient.lift …`:     R5
  2. The lift on a `Quotient.mk` computes to the function on `n`:             R4
  3. Both sides are now the same `Bool` expression: one `rfl` does 1–3.
-/
-- BEGIN SPEC
theorem isEven_mk (n : Nat) : (Parity.mk n).isEven = (n % 2 == 0) :=
-- END SPEC
  sorry

/- SKELETON · mk_three_seven
  1. Equal classes from related representatives; the goal becomes `3 ≈ 7`:   R6
  2. `3 ≈ 7` unfolds to `3 % 2 = 7 % 2`, and both sides compute to `1`:       R7, rfl
-/
-- BEGIN SPEC
theorem mk_three_seven : Parity.mk 3 = Parity.mk 7 :=
-- END SPEC
  sorry

/- SKELETON · mk_eq_iff
  1. Split the `↔` into two implications, each with its `h`:                   R8
  2. → : `h : Parity.mk a = Parity.mk b` gives `a ≈ b`, which is the goal:     R9
  3. ← : `h : a % 2 = b % 2` is `a ≈ b`, so the classes are equal:             R6
  As a term, pass `h` explicitly in each direction (`fun h => … h`; Traps).
-/
-- BEGIN SPEC
theorem mk_eq_iff (a b : Nat) : Parity.mk a = Parity.mk b ↔ a % 2 = b % 2 :=
-- END SPEC
  sorry

end E081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A function out of a quotient is a function on representatives plus a proof that related
    representatives give the same answer (R1). Equal classes ↔ related representatives:
    `Quotient.sound` builds an equation of classes (R6), `Quotient.exact` uses one (R9).
H2. `isEven`: lift `fun n => n % 2 == 0`; bind the obligation's hypothesis as `(h : a % 2 = b % 2)` (R2)
    and close `(a % 2 == 0) = (b % 2 == 0)` with `simp [h]` (R3). `isEven_mk` then computes: `rfl`.
    `mk_three_seven`: `Quotient.sound` applied to a proof of `3 % 2 = 7 % 2` (R7).
H3. `Quotient.lift (fun n => n % 2 == 0) (fun a b (h : a % 2 = b % 2) => by simp [h])`;
    `mk_three_seven` is `Quotient.sound` applied to `rfl`; `mk_eq_iff` pairs `Quotient.exact` and
    `Quotient.sound` in `⟨…, …⟩`, each wrapped as `fun h => … h` so Lean can infer the setoid.
-/
