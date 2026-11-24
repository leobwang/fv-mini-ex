/- H007 | Integers as a quotient of Nat × Nat | 1-1.5 h | Quotient, Setoid, Quotient.lift₂, well-definedness, grind
GOAL
  Build ℤ as pairs `(a, b)` (read: a − b) modulo `(a, b) ~ (c, d) ↔ a + d = c + b`. Prove `~` is an
  equivalence; define `add`, `neg`, `mul`, `toInt` on the quotient (each must respect `~`); prove
  `x + (−x) = 0`, distributivity, and that `toInt` is a bijection that preserves multiplication.

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H007

/- SKELETON · R_equiv
  1. Split `Equivalence R` into its three fields (refl, symm, trans):         R1
  2. refl: introduce the pair; `R x x` is `x.1 + x.2 = x.1 + x.2` by definition: R2, rfl
  3. symm: introduce `x y h`; `h : R x y` is an equation, flip it:             R2, R5
  4. trans: introduce `x y z h1 h2`, unfold `R` everywhere, close:             R2, R3 → R4
  (Term form works too: `⟨fun x => …, fun h => …, fun h1 h2 => …⟩`.)
-/
-- BEGIN SPEC
/-- `(a, b)` represents the integer `a - b`. -/
def R (x y : Nat × Nat) : Prop := x.1 + y.2 = y.1 + x.2

theorem R_equiv : Equivalence R :=
-- END SPEC
  sorry

-- BEGIN SPEC
instance intSetoid : Setoid (Nat × Nat) := ⟨R, R_equiv⟩

def MyInt : Type := Quotient intSetoid

def MyInt.mk (a b : Nat) : MyInt := Quotient.mk intSetoid (a, b)
-- END SPEC

/- SKELETON · exists_mk   (MILESTONE: prove it first; used by add_neg, mul_add, toInt_injective, toInt_mul)
  1. Replace `x` by the class `Quotient.mk intSetoid p` of a pair `p`:              R6
  2. Witnesses `p.1`, `p.2`; the equation holds by definition:                      R7
-/
-- MILESTONE (optional: change or delete)
theorem exists_mk (x : MyInt) : ∃ a b, x = MyInt.mk a b := by
  sorry

/- SKELETON · mul_wd   (MILESTONE: prove it before `MyInt.mul`, whose obligation it is)
  1. A Nat identity with products of variables and two hypotheses: one call         R8
-/
-- MILESTONE (optional: change or delete)
-- Well-definedness of `mul` as a plain Nat fact: (a - b)(c - d) = (a' - b')(c' - d').
theorem mul_wd (a b a' b' c d c' d' : Nat) (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c) := by
  sorry

/- SKELETON · MyInt.add   (read the function on pairs off `add_mk` below)
  1. Body: `Quotient.lift₂ f (by …)` with `f x y := MyInt.mk (…) (…)`, using `x.1`, `x.2`:  R9
  2. Inside `by`: name the four pairs (order: x₁ y₁ x₂ y₂) and state the two
     relations as Nat equations, `h1 : a + b' = a' + b`, `h2 : c + d' = c' + d`:   R10, R11
  3. Equal classes ← related pairs:                                                R12
  4. Restate the goal without `≈` and `(a, b).fst`, then linear arithmetic:       R13 → R4
-/
-- BEGIN SPEC
def MyInt.add : MyInt → MyInt → MyInt :=
-- END SPEC
  sorry

/- SKELETON · MyInt.neg   (read the function on pairs off `neg_mk`)
  1. Body: `Quotient.lift g (by …)` with `g x := MyInt.mk (…) (…)`:                R14
  2. Name the two pairs and state the relation as a Nat equation:                 R10, R11
  3. Equal classes ← related pairs; restate; close:                               R12 → R13 → R4
-/
-- BEGIN SPEC
def MyInt.neg : MyInt → MyInt :=
-- END SPEC
  sorry

/- SKELETON · MyInt.mul   (read the function on pairs off `mul_mk`)
  Prove the MILESTONE `mul_wd` first: it is exactly this definition's obligation.
  1. Body: `Quotient.lift₂ f (by …)`:                                              R9
  2. Name the four pairs and `h1 h2` (no restatement needed, `≈` is `R`):         R10
  3. One line: `Quotient.sound` (term form of R12) applied to `mul_wd … h1 h2`.
-/
-- BEGIN SPEC
def MyInt.mul : MyInt → MyInt → MyInt :=
-- END SPEC
  sorry

/- SKELETON · MyInt.toInt   (read the function on pairs off `toInt_mk`)
  1. Body: `Quotient.lift g (by …)` with `g x : Int` built from `(x.1 : Int)`, `(x.2 : Int)`:  R14
  2. Name the two pairs and state the relation as a Nat equation:                 R10, R11
  3. Arithmetic over Int (`omega` reduces `(a, b).fst` to `a` itself; restating
     the goal with `show` first is optional, for readability):                    (R13 →) R15
-/
-- BEGIN SPEC
def MyInt.toInt : MyInt → Int :=
-- END SPEC
  sorry

/- SKELETON · add_mk
  1. Computation rule of `Quotient.lift₂`: closes by definition if your `add` matches:  R16
-/
-- BEGIN SPEC
theorem add_mk (a b c d : Nat) : (MyInt.mk a b).add (MyInt.mk c d) = MyInt.mk (a + c) (b + d) :=
-- END SPEC
  sorry

/- SKELETON · neg_mk
  1. Computation rule of `Quotient.lift`:                                          R16
-/
-- BEGIN SPEC
theorem neg_mk (a b : Nat) : (MyInt.mk a b).neg = MyInt.mk b a :=
-- END SPEC
  sorry

/- SKELETON · mul_mk
  1. Computation rule of `Quotient.lift₂`:                                         R16
-/
-- BEGIN SPEC
theorem mul_mk (a b c d : Nat) :
    (MyInt.mk a b).mul (MyInt.mk c d) = MyInt.mk (a * c + b * d) (a * d + b * c) :=
-- END SPEC
  sorry

/- SKELETON · toInt_mk
  1. Computation rule of `Quotient.lift`:                                          R16
-/
-- BEGIN SPEC
theorem toInt_mk (a b : Nat) : (MyInt.mk a b).toInt = (a : Int) - (b : Int) :=
-- END SPEC
  sorry

/- SKELETON · mk_eq_mk
  1. Split the `↔`:                                                                R17
  2. (→) `intro h`; equal classes → related pairs; `(a, b) ≈ (c, d)` is the goal
     by definition, so the result closes it:                                       R18
  3. (←) `intro h`; related pairs → equal classes:                                 R12
  (Term form: `⟨…, fun h => …⟩`.)
-/
-- BEGIN SPEC
theorem mk_eq_mk (a b c d : Nat) : MyInt.mk a b = MyInt.mk c d ↔ a + d = c + b :=
-- END SPEC
  sorry

/- SKELETON · add_neg   (uses the MILESTONE `exists_mk`)
  1. Replace `x` by `MyInt.mk a b`:                                                R19 with `exists_mk x`
  2. Compute: `rw` with `neg_mk`, then `add_mk`; then MyInt equation → Nat:       rw, R20 (`mk_eq_mk`)
  3. Linear Nat arithmetic:                                                        R4
-/
-- BEGIN SPEC
theorem add_neg (x : MyInt) : x.add x.neg = MyInt.mk 0 0 :=
-- END SPEC
  sorry

/- SKELETON · mul_add   (uses the MILESTONE `exists_mk`)
  1. Replace `x`, `y`, `z` by `MyInt.mk a b`, `MyInt.mk c d`, `MyInt.mk e f`:      R19 (three times)
  2. Compute inside out: `add_mk` (the inner sum), the three `mul_mk`, the outer
     `add_mk`; then MyInt equation → Nat:                                          rw, R20 (`mk_eq_mk`)
  3. The Nat identity has products of variables:                                   R8
-/
-- BEGIN SPEC
theorem mul_add (x y z : MyInt) : x.mul (y.add z) = (x.mul y).add (x.mul z) :=
-- END SPEC
  sorry

/- SKELETON · toInt_injective   (uses the MILESTONE `exists_mk`)
  1. Replace `x` and `y` by `MyInt.mk a b`, `MyInt.mk c d`:                         R19 (twice)
  2. Compute both sides of `h` with `toInt_mk`:                                    R21
  3. Goal → Nat equation:                                                          R20 (`mk_eq_mk`)
  4. `h` is over Int, the goal over Nat; `omega` handles both:                     R15
-/
-- BEGIN SPEC
theorem toInt_injective (x y : MyInt) (h : x.toInt = y.toInt) : x = y :=
-- END SPEC
  sorry

/- SKELETON · toInt_surjective
  1. Give a witness `MyInt.mk p q` with `p, q : Nat` and `↑p - ↑q = n`;
     `Int.toNat` of `n` and of `-n` are the natural choices:              refine ⟨MyInt.mk p q, ?_⟩, R22
  2. Compute with `toInt_mk`, then close:                                          rw, R22
-/
-- BEGIN SPEC
theorem toInt_surjective (n : Int) : ∃ x : MyInt, x.toInt = n :=
-- END SPEC
  sorry

/- SKELETON · toInt_mul   (uses the MILESTONE `exists_mk`)
  1. Replace `x` and `y` by `MyInt.mk a b`, `MyInt.mk c d`:                         R19 (twice)
  2. Compute: `mul_mk`, then `toInt_mk` (three times):                             rw
  3. An Int identity with Nat casts and products:                                  R23
-/
-- BEGIN SPEC
theorem toInt_mul (x y : MyInt) : (x.mul y).toInt = x.toInt * y.toInt :=
-- END SPEC
  sorry

end H007

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A function out of `MyInt` is `Quotient.lift`/`lift₂` of a function on pairs plus a proof that
    related pairs give equal results (R9, R14); the `_mk` theorems tell you which function on pairs.
    An equation between `MyInt`s becomes a Nat equation via `mk_eq_mk` (R20).
H2. Order: `R_equiv`, the milestones `exists_mk` (R6, R7) and `mul_wd` (R8), the four definitions,
    the `_mk` theorems (`rfl`), `mk_eq_mk`. Then every theorem about arbitrary `x : MyInt`:
    `obtain ⟨a, b, rfl⟩ := exists_mk x` per variable, `rw` with the `_mk` lemmas and `mk_eq_mk`,
    finish with `omega` (linear) or `grind` (products).
H3. Well-definedness: `intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ (h1 : a + b' = a' + b) (h2 : c + d' = c' + d)`,
    then `apply Quotient.sound; show …; omega`; for `mul`, `exact Quotient.sound (mul_wd a b a' b' c d c' d' h1 h2)`.
    `mk_eq_mk := ⟨Quotient.exact, fun h => Quotient.sound h⟩`. `toInt_surjective`: witness
    `MyInt.mk n.toNat (-n).toNat`. `toInt_mul`: after the rewrites, `grind`.
-/
