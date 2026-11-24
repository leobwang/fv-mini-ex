/- E047 | match in proofs | 2-3 min | match, tactic-mode match, term-mode match
GOAL
  Split on a natural number, an `∃` and an `∨` with `match`, both inside `by` and as a term.

BANNED: cases, rcases, obtain, rintro, induction, grind, fun_cases, fun_induction, simp_all, split, symm, elim, casesOn, rec, recOn, casesAuxOn, imp, imp_left, imp_right, if, ite, dite, byCases, by_cases, omega, Or.comm, or_comm, and_comm, And.comm, eq_zero_or_eq_succ_pred, eq_zero_or_pos, exists_eq_add_one_of_ne_zero, exists_eq_succ_of_ne_zero, exists_eq_add_of_lt, solve_by_elim, exact?, apply?, try?

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E047

-- BEGIN SPEC
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false
-- END SPEC

/- SKELETON · zero_or_succ
  1. Inside `by`, split `n` into `0` and `k + 1` (tactic `match`):            R1
  2. Branch `0`: the left side `0 = 0`, proved by `rfl`:                       R2, rfl
  3. Branch `k + 1`: the right side, witness `k`, then `k + 1 = k + 1`:        R3, R4, rfl
-/
-- BEGIN SPEC
theorem zero_or_succ (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 :=
-- END SPEC
  sorry

/- SKELETON · exists_swap
  1. Term mode (no `by`): take `h` apart with one nested pattern
       w : Nat, hp : p w, hq : q w                                            R5, R6
  2. Answer with one anonymous constructor, pieces in the new order:          R7
-/
-- BEGIN SPEC
theorem exists_swap (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n ∧ p n :=
-- END SPEC
  sorry

/- SKELETON · or_swap
  1. Term mode: two branches on `h`, with `hp : P` / `hq : Q`:                R8
  2. Each branch puts its proof on the other side of `Q ∨ P`:                 R9 (or R2, R3)
-/
-- BEGIN SPEC
theorem or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P :=
-- END SPEC
  sorry

/- SKELETON · isZero_iff
  1. Inside `by`, split `n` into `0` and `k + 1`:                             R1
  2. In each branch one `simp [isZero]`, which
       unfolds `isZero 0` / `isZero (k + 1)`                                  R10
       (branch `k + 1`) turns `false = true` and `k + 1 = 0` into `False`     R11, R12
       closes the `↔` once both sides agree                                   R13
-/
-- BEGIN SPEC
theorem isZero_iff (n : Nat) : isZero n = true ↔ n = 0 :=
-- END SPEC
  sorry

end E047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `match` has one branch per constructor: `0` / `k + 1` for `Nat` (R1), `⟨w, hw⟩` for `∃` (R5),
    `.inl` / `.inr` for `∨` (R8). Nested patterns such as `⟨n, hp, hq⟩` work too (R6).
H2. `zero_or_succ` and `isZero_iff`: `by match n with | 0 => … | k + 1 => …`; in each branch the goal
    mentions `0` or `k + 1`, so `rfl` and `isZero` compute. `exists_swap` and `or_swap`: a term-mode
    `match h with` and an anonymous constructor or `.inl` / `.inr` on the right of each `=>`.
H3. `or_swap`: `match h with | .inl hp => .inr hp | .inr hq => .inl hq`;
    `zero_or_succ`, second branch: `exact Or.inr ⟨k, rfl⟩`; `isZero_iff` branches: `simp [isZero]`.
-/
