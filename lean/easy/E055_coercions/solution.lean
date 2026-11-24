/- E055 | Coercions | 2-3 min | Coe, @[coe], ↑, coercion unfolding
GOAL
  `Pos` is a natural number packed with a proof that it is positive. Its coercion to `Nat` (given) lets a
  `Pos` stand wherever a `Nat` is expected. Write the function behind it, define addition, and prove
  the coercion respects both.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E055

-- BEGIN SPEC
structure Pos where
  val : Nat
  pos : 0 < val

def one : Pos := ⟨1, Nat.one_pos⟩
-- END SPEC

/- SKELETON · Pos.toNat (definition body)
  1. `coe_mk` says `↑⟨n, h⟩ = n`: return the number stored in `p` (a data field):    R1
-/
-- BEGIN SPEC
@[coe] def Pos.toNat (p : Pos) : Nat :=
-- END SPEC
  p.val

-- BEGIN SPEC
instance instCoePosNat : Coe Pos Nat := ⟨Pos.toNat⟩
-- END SPEC

/- SKELETON · Pos.add (definition body)
  1. A `Pos` is a value AND a proof: give the value `a.val + b.val` first:          R2
  2. The proof field is now `0 < a.val + b.val`. Take `a`'s proof field:           R3
     and widen `0 < a.val` to the sum:                                             R4
-/
-- BEGIN SPEC
def Pos.add (a b : Pos) : Pos :=
-- END SPEC
  ⟨a.val + b.val, Nat.add_pos_left a.pos b.val⟩

/- SKELETON · coe_mk
  1. `↑⟨n, h⟩` is `Pos.toNat ⟨n, h⟩`, which is the field `⟨n, h⟩.val`, which is `n`:
     both sides agree after unfolding. Close it in one step.                        R7
     (To watch the unfolding: R5 with `Pos.toNat`, then R6.)
-/
-- BEGIN SPEC
theorem coe_mk (n : Nat) (h : 0 < n) : ((⟨n, h⟩ : Pos) : Nat) = n :=
-- END SPEC
  rfl

/- SKELETON · coe_one
  1. Unfolding `one`, the coercion and the field gives `1` on both sides:             R7
     (by hand: R5 with `one Pos.toNat`, then R6)
-/
-- BEGIN SPEC
theorem coe_one : ((one : Pos) : Nat) = 1 :=
-- END SPEC
  rfl

/- SKELETON · coe_add
  1. Both sides unfold to `a.val + b.val`, provided `Pos.add` stores exactly that:    R7
-/
-- BEGIN SPEC
theorem coe_add (a b : Pos) : ((a.add b : Pos) : Nat) = (a : Nat) + (b : Nat) :=
-- END SPEC
  rfl

/- SKELETON · coe_ne_zero
  1. The fact you have is `a`'s proof field `0 < a.val`:                             R3
  2. Change its shape from `0 < x` to `x ≠ 0`:                                       R8
  3. It is about `a.val`, the goal about `↑a`; `exact` accepts it across `↑`:         R9
-/
-- BEGIN SPEC
theorem coe_ne_zero (a : Pos) : (a : Nat) ≠ 0 :=
-- END SPEC
  Nat.pos_iff_ne_zero.mp a.pos

end E055

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `coe_mk` tells you what `Pos.toNat` must return. `Pos.add` must build a value *and* a proof that it is
    positive. `↑a` in a goal is just `Pos.toNat a`: `rfl` and `exact` see through it, `omega` does not.
H2. With `toNat p := p.val`, `coe_mk`, `coe_one` and `coe_add` hold by definition (`rfl`, R7). For `coe_ne_zero`,
    the proof field `a.pos : 0 < a.val` is the fact you need, turned from `0 < x` into `x ≠ 0` (R8).
H3. `Pos.add a b := ⟨a.val + b.val, Nat.add_pos_left a.pos b.val⟩`; `coe_ne_zero` is `Nat.pos_iff_ne_zero.mp a.pos`.
-/
