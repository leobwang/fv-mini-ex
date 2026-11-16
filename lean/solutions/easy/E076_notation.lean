/- E076 | Notation | 2-3 min | infixl, infixr, notation, precedence, associativity
GOAL
  Fix the two notation lines below so that `a ⊖ b` is subtraction that groups and binds exactly like `-`,
  and `‖a‖²` means `dot a a`. Each frozen proof restates its goal in your notation and falls back to
  `sorry` until your notation gives it the right meaning. Then prove `dot_comm`.

REFERENCE
  infixl:65 " +' " => Nat.add   -- left-assoc: `a +' b +' c` parses as `(a +' b) +' c`
  infixr:75 " ^' " => Nat.pow   -- right-assoc: `a ^' b ^' c` parses as `a ^' (b ^' c)`
  notation "⟪" a ", " b "⟫" => dot a b   -- mixfix: any tokens around the arguments
  Higher numbers bind tighter: `+` and `-` are 65, `*` and `/` are 70, so `a - b * c` is `a - (b * c)`.
  set_option pp.notation false in #check 2 + 3 * 4   -- shows the plain terms behind the notation
  Notation is only syntax: `simp [dot]` or `unfold dot` sees straight through `⬝`.
BANNED: macro_rules, macro, syntax, elab, elab_rules, import
NOTE: edit the existing `⊖` / `‖‖²` lines; a second declaration of the same token makes every use ambiguous.
NOTE: the bans stop a tactic macro from redefining the `sorry` fallback; this problem is about term notation.
-/

namespace E076

-- BEGIN SPEC
def dot (a b : Nat × Nat) : Nat := a.1 * b.1 + a.2 * b.2
infixl:70 " ⬝ " => dot
-- END SPEC

-- Your notation (fix these two lines):
infixl:65 " ⊖ " => Nat.sub
notation "‖" a "‖²" => dot a a

-- BEGIN SPEC
theorem sub_left : 10 - 3 - 2 = 5 := by
  first | exact (by decide : 10 ⊖ 3 ⊖ 2 = 5) | sorry
-- END SPEC

-- BEGIN SPEC
theorem sub_prec : 10 - 2 * 3 = 4 := by
  first | exact (by decide : 10 ⊖ 2 * 3 = 4) | sorry
-- END SPEC

-- BEGIN SPEC
theorem sub_add_mix : 10 - 2 + 3 = 11 := by
  first | exact (by decide : 10 ⊖ 2 + 3 = 11) | sorry
-- END SPEC

-- BEGIN SPEC
theorem add_sub_mix : 10 + 2 - 3 = 9 := by
  first | exact (by decide : 10 + 2 ⊖ 3 = 9) | sorry
-- END SPEC

-- BEGIN SPEC
theorem sub_sub_eq (a b c : Nat) : a - b - c = a - (b + c) := by
  first | exact (Nat.sub_sub a b c : a ⊖ b ⊖ c = a - (b + c)) | sorry
-- END SPEC

-- BEGIN SPEC
theorem norm_sq_ex : dot (3, 4) (3, 4) = 25 := by
  first | exact (by decide : ‖(3, 4)‖² = 25) | sorry
-- END SPEC

-- BEGIN SPEC
theorem norm_sq_eq (a : Nat × Nat) : dot a a = a.1 * a.1 + a.2 * a.2 := by
  first | exact (rfl : ‖a‖² = a.1 * a.1 + a.2 * a.2) | sorry
-- END SPEC

-- BEGIN SPEC
theorem dot_comm (a b : Nat × Nat) : a ⬝ b = b ⬝ a :=
-- END SPEC
  by simp [dot, Nat.mul_comm]

end E076

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With the stub's line, `10 ⊖ 3 ⊖ 2` parses as `10 ⊖ (3 ⊖ 2)` and `10 ⊖ 2 * 3` as `(10 ⊖ 2) * 3`.
    `10 ⊖ 2 + 3` and `10 + 2 ⊖ 3` test that `⊖` sits at exactly the same level as `+`.
    `#eval 10 ⊖ 3 ⊖ 2` shows what your current notation computes.
H2. `⊖` needs left associativity and the precedence of `-`. The mixfix must use its argument `a` on
    both sides of `dot`. `dot_comm`: unfold `dot`, then commute the products.
H3. `infixl:65 " ⊖ " => Nat.sub`; `notation "‖" a "‖²" => dot a a`; `dot_comm`: `simp [dot, Nat.mul_comm]`.
-/
