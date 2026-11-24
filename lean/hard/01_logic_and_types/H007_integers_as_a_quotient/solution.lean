/- H007 | Integers as a quotient of Nat × Nat | 1-1.5 h | Quotient, Setoid, Quotient.lift₂, well-definedness, grind
GOAL
  Build ℤ as pairs `(a, b)` (read: a − b) modulo `(a, b) ~ (c, d) ↔ a + d = c + b`. Prove `~` is an
  equivalence; define `add`, `neg`, `mul`, `toInt` on the quotient (each must respect `~`); prove
  `x + (−x) = 0`, distributivity, and that `toInt` is a bijection that preserves multiplication.

REFERENCE
  example {α : Type} (r : α → α → Prop) (h : Equivalence r) : Setoid α := ⟨r, h⟩  -- `a ≈ b` means `r a b`
  #check @Equivalence.mk    -- fields refl, symm, trans: build one with ⟨fun _ => _, fun h => _, fun h1 h2 => _⟩
  example {α β : Type} (s : Setoid α) (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) : Quotient s → β := Quotient.lift f h
  #check @Quotient.lift₂    -- two arguments: needs `∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂`
  #check @Quotient.sound    -- a ≈ b → Quotient.mk s a = Quotient.mk s b
  #check @Quotient.exact    -- Quotient.mk s a = Quotient.mk s b → a ≈ b
  -- `induction x using Quotient.inductionOn with | h p => …` replaces `x : MyInt` by `Quotient.mk _ p`
  -- `intro ⟨a, b⟩ ⟨c, d⟩ (h : a + d = c + b)` splits pairs and restates `(a, b) ≈ (c, d)` (definitional)
  -- `show a + d = c + b` does the same for a goal `(a, b) ≈ (c, d)`; `x.1`, `x.2` are a pair's parts
  #check Int.toNat_sub_toNat_neg  -- (n.toNat : Int) - ((-n).toNat : Int) = n
  -- `omega` closes linear Nat/Int goals; `grind` also closes the product identities (see `mul_wd`)
NOTE: the four `_mk` theorems pin down your definitions; with the intended ones they are `rfl`.
-/

namespace H007

-- BEGIN SPEC
/-- `(a, b)` represents the integer `a - b`. -/
def R (x y : Nat × Nat) : Prop := x.1 + y.2 = y.1 + x.2

theorem R_equiv : Equivalence R :=
-- END SPEC
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => by unfold R at *; omega⟩

-- BEGIN SPEC
instance intSetoid : Setoid (Nat × Nat) := ⟨R, R_equiv⟩

def MyInt : Type := Quotient intSetoid

def MyInt.mk (a b : Nat) : MyInt := Quotient.mk intSetoid (a, b)
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem exists_mk (x : MyInt) : ∃ a b, x = MyInt.mk a b := by
  induction x using Quotient.inductionOn with
  | h p => exact ⟨p.1, p.2, rfl⟩

-- MILESTONE (optional: change or delete)
-- Well-definedness of `mul` as a plain Nat fact: (a - b)(c - d) = (a' - b')(c' - d').
theorem mul_wd (a b a' b' c d c' d' : Nat) (h1 : a + b' = a' + b) (h2 : c + d' = c' + d) :
    (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c) := by
  grind

-- BEGIN SPEC
def MyInt.add : MyInt → MyInt → MyInt :=
-- END SPEC
  Quotient.lift₂ (fun x y => MyInt.mk (x.1 + y.1) (x.2 + y.2)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ (h1 : a + b' = a' + b) (h2 : c + d' = c' + d)
    apply Quotient.sound
    show a + c + (b' + d') = a' + c' + (b + d)
    omega)

-- BEGIN SPEC
def MyInt.neg : MyInt → MyInt :=
-- END SPEC
  Quotient.lift (fun x => MyInt.mk x.2 x.1) (by
    intro ⟨a, b⟩ ⟨a', b'⟩ (h : a + b' = a' + b)
    apply Quotient.sound
    show b + a' = b' + a
    omega)

-- BEGIN SPEC
def MyInt.mul : MyInt → MyInt → MyInt :=
-- END SPEC
  Quotient.lift₂ (fun x y => MyInt.mk (x.1 * y.1 + x.2 * y.2) (x.1 * y.2 + x.2 * y.1)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2
    exact Quotient.sound (mul_wd a b a' b' c d c' d' h1 h2))

-- BEGIN SPEC
def MyInt.toInt : MyInt → Int :=
-- END SPEC
  Quotient.lift (fun x => (x.1 : Int) - x.2) (by
    intro ⟨a, b⟩ ⟨c, d⟩ (h : a + d = c + b)
    show (a : Int) - b = c - d
    omega)

-- BEGIN SPEC
theorem add_mk (a b c d : Nat) : (MyInt.mk a b).add (MyInt.mk c d) = MyInt.mk (a + c) (b + d) :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem neg_mk (a b : Nat) : (MyInt.mk a b).neg = MyInt.mk b a :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem mul_mk (a b c d : Nat) :
    (MyInt.mk a b).mul (MyInt.mk c d) = MyInt.mk (a * c + b * d) (a * d + b * c) :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem toInt_mk (a b : Nat) : (MyInt.mk a b).toInt = (a : Int) - (b : Int) :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem mk_eq_mk (a b c d : Nat) : MyInt.mk a b = MyInt.mk c d ↔ a + d = c + b :=
-- END SPEC
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

-- BEGIN SPEC
theorem add_neg (x : MyInt) : x.add x.neg = MyInt.mk 0 0 :=
-- END SPEC
  by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    rw [neg_mk, add_mk, mk_eq_mk]
    omega

-- BEGIN SPEC
theorem mul_add (x y z : MyInt) : x.mul (y.add z) = (x.mul y).add (x.mul z) :=
-- END SPEC
  by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    obtain ⟨e, f, rfl⟩ := exists_mk z
    rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk, mk_eq_mk]
    grind

-- BEGIN SPEC
theorem toInt_injective (x y : MyInt) (h : x.toInt = y.toInt) : x = y :=
-- END SPEC
  by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    rw [toInt_mk, toInt_mk] at h
    rw [mk_eq_mk]
    omega

-- BEGIN SPEC
theorem toInt_surjective (n : Int) : ∃ x : MyInt, x.toInt = n :=
-- END SPEC
  ⟨MyInt.mk n.toNat (-n).toNat, by rw [toInt_mk]; omega⟩

-- BEGIN SPEC
theorem toInt_mul (x y : MyInt) : (x.mul y).toInt = x.toInt * y.toInt :=
-- END SPEC
  by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    rw [mul_mk, toInt_mk, toInt_mk, toInt_mk]
    -- WHY: `grind` normalises the Nat→Int casts itself, so the ring identity over Int closes directly.
    grind

end H007

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A function out of `MyInt` is `Quotient.lift`/`lift₂` of a function on pairs plus a proof that
    related pairs give equal results. An equation between `MyInt`s becomes a Nat equation via `mk_eq_mk`.
H2. Define `add := Quotient.lift₂ (fun x y => MyInt.mk (x.1 + y.1) (x.2 + y.2)) (by …)`; then `add_mk` is
    `rfl`. For theorems about arbitrary `x : MyInt`: prove `exists_mk` once, then
    `obtain ⟨a, b, rfl⟩ := exists_mk x` per variable, `rw` with the `_mk` lemmas, finish with `omega`/`grind`.
H3. `mk_eq_mk := ⟨Quotient.exact, fun h => Quotient.sound h⟩`. Inside `mul`'s proof:
    `intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2; exact Quotient.sound (mul_wd a b a' b' c d c' d' h1 h2)`.
    `toInt_surjective`: witness `MyInt.mk n.toNat (-n).toNat`. `toInt_mul`: after the rewrites, `grind`.
-/
