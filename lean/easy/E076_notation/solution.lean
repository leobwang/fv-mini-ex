/- E076 | Notation | 2-3 min | infixl, infixr, notation, precedence, associativity
GOAL
  Fix the two notation lines below so that `a ⊖ b` is subtraction that groups and binds exactly like `-`,
  and `‖a‖²` means `dot a a`. Each frozen proof restates its goal in your notation and falls back to
  `sorry` until your notation gives it the right meaning. Then prove `dot_comm`.
BANNED: macro_rules, macro, syntax, elab, elab_rules, import

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E076

-- BEGIN SPEC
def dot (a b : Nat × Nat) : Nat := a.1 * b.1 + a.2 * b.2
infixl:70 " ⬝ " => dot
-- END SPEC

/- SKELETON · the two notation lines (the holes every frozen proof below depends on)
  1. `⊖`: pick the associativity and level of `-`:                         R1 (not R2), R3, R4
       see how a test term parses / what it computes:                      R5, `#eval`
  2. `‖a‖²`: a mixfix whose right-hand side uses its argument twice:       R6
-/
-- Your notation (fix these two lines):
infixl:65 " ⊖ " => Nat.sub
notation "‖" a "‖²" => dot a a

/- SKELETON · sub_left
  Nothing to write here: the frozen proof checks `10 ⊖ 3 ⊖ 2 = 5` by `decide`.
  1. It passes once `⊖` groups to the left, `(10 ⊖ 3) ⊖ 2`:                 R1 (the stub groups right, R2)
-/
-- BEGIN SPEC
theorem sub_left : 10 - 3 - 2 = 5 := by
  first | exact (by decide : 10 ⊖ 3 ⊖ 2 = 5) | sorry
-- END SPEC

/- SKELETON · sub_prec
  Nothing to write here: the frozen proof checks `10 ⊖ 2 * 3 = 4` by `decide`.
  1. It passes once `*` binds tighter than `⊖`, `10 ⊖ (2 * 3)`: a level below 70   R3
-/
-- BEGIN SPEC
theorem sub_prec : 10 - 2 * 3 = 4 := by
  first | exact (by decide : 10 ⊖ 2 * 3 = 4) | sorry
-- END SPEC

/- SKELETON · sub_add_mix
  Nothing to write here: the frozen proof checks `10 ⊖ 2 + 3 = 11` by `decide`.
  1. It passes once `10 ⊖ 2 + 3` is `(10 ⊖ 2) + 3`: `infixl` at level 65 or above   R1, R4 (W1: what `infixr:65` does)
-/
-- BEGIN SPEC
theorem sub_add_mix : 10 - 2 + 3 = 11 := by
  first | exact (by decide : 10 ⊖ 2 + 3 = 11) | sorry
-- END SPEC

/- SKELETON · add_sub_mix
  Nothing to write here: the frozen proof checks `10 + 2 ⊖ 3 = 9` by `decide`.
  1. It passes once `10 + 2 ⊖ 3` is `(10 + 2) ⊖ 3`: together with sub_add_mix this
     forces exactly level 65, the level of `+`                               R4
-/
-- BEGIN SPEC
theorem add_sub_mix : 10 + 2 - 3 = 9 := by
  first | exact (by decide : 10 + 2 ⊖ 3 = 9) | sorry
-- END SPEC

/- SKELETON · sub_sub_eq
  Nothing to write here: the frozen proof ascribes `Nat.sub_sub a b c : a - b - c = a - (b + c)`
  the type `a ⊖ b ⊖ c = a - (b + c)`.
  1. It passes once `a ⊖ b ⊖ c` is the term `Nat.sub (Nat.sub a b) c`:      R1, check with R5
-/
-- BEGIN SPEC
theorem sub_sub_eq (a b c : Nat) : a - b - c = a - (b + c) := by
  first | exact (Nat.sub_sub a b c : a ⊖ b ⊖ c = a - (b + c)) | sorry
-- END SPEC

/- SKELETON · norm_sq_ex
  Nothing to write here: the frozen proof checks `‖(3, 4)‖² = 25` by `decide`.
  1. It passes once `‖x‖²` expands to `dot x x`:                            R6
-/
-- BEGIN SPEC
theorem norm_sq_ex : dot (3, 4) (3, 4) = 25 := by
  first | exact (by decide : ‖(3, 4)‖² = 25) | sorry
-- END SPEC

/- SKELETON · norm_sq_eq
  Nothing to write here: the frozen proof is `rfl` at type `‖a‖² = a.1 * a.1 + a.2 * a.2`.
  1. It passes once `‖a‖²` is the term `dot a a` (the infoview prints it as `a ⬝ a`):   R6
-/
-- BEGIN SPEC
theorem norm_sq_eq (a : Nat × Nat) : dot a a = a.1 * a.1 + a.2 * a.2 := by
  first | exact (rfl : ‖a‖² = a.1 * a.1 + a.2 * a.2) | sorry
-- END SPEC

/- SKELETON · dot_comm
  1. Unfold `dot`; the infix `⬝` goes with it, leaving products of components:   R7
  2. Commute the products so both sides agree:                                  R8
  Both steps fit in one `simp` call that is given `dot` and the lemma (W2).
-/
-- BEGIN SPEC
theorem dot_comm (a b : Nat × Nat) : a ⬝ b = b ⬝ a :=
-- END SPEC
  by simp [dot, Nat.mul_comm]

end E076

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With the stub's `infixr:75`, `10 ⊖ 3 ⊖ 2` parses as `10 ⊖ (3 ⊖ 2)` (R2) and `10 ⊖ 2 * 3` as
    `(10 ⊖ 2) * 3` (R3). `10 ⊖ 2 + 3` and `10 + 2 ⊖ 3` test that `⊖` sits at exactly the level of `+` (R4).
    `#eval 10 ⊖ 3 ⊖ 2` or `set_option pp.notation false` (R5) shows what your current line does.
H2. `⊖` needs `infixl` (R1) at level 65, the level of `+` and `-` (R4). The mixfix's right-hand side must use
    its argument `a` on both sides of `dot` (R6). `dot_comm`: unfold `dot` (R7), then commute the
    products with `Nat.mul_comm` (R8).
H3. `infixl:65 " ⊖ " => Nat.sub`; `notation "‖" a "‖²" => dot a a`; `dot_comm`: `simp [dot, Nat.mul_comm]`.
-/
