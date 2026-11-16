/- E047 | match in proofs | 2-3 min | match, tactic-mode match, term-mode match
GOAL
  Split on a natural number, an `∃` and an `∨` with `match`, both inside `by` and as a term.

REFERENCE
  example (n : Nat) (h : n ≠ 0) : (n - 1) + 1 = n := by
    match n with
    | 0 => contradiction    -- tactic mode: `h` and the goal now mention `0` / `k + 1`, not `n`
    | k + 1 => rfl          -- `(k + 1 - 1) + 1 = k + 1` computes; plain `rfl` on `n` would not
  example (h : ∃ n : Nat, n > 0) : ∃ m : Nat, m + 1 > 1 :=
    match h with
    | ⟨n, hn⟩ => ⟨n, Nat.succ_lt_succ hn⟩   -- term mode: take an `∃` apart
  example (P : Prop) (h : P ∨ P) : P :=
    match h with
    | .inl hp => hp
    | .inr hp => hp         -- `.inl` = `Or.inl` (the expected type supplies the namespace)
BANNED: cases, rcases, obtain, rintro, induction, grind, fun_cases, fun_induction, simp_all, split, symm, elim, casesOn, rec, recOn, casesAuxOn, imp, imp_left, imp_right, if, ite, dite, byCases, by_cases, omega, Or.comm, or_comm, and_comm, And.comm, eq_zero_or_eq_succ_pred, eq_zero_or_pos, exists_eq_add_one_of_ne_zero, exists_eq_succ_of_ne_zero, exists_eq_add_of_lt, solve_by_elim, exact?, apply?, try?
NOTE: case-splitting tactics, recursors and `if` are banned so every split is a `match` (`let ⟨..⟩ := h` is a one-branch `match` and is fine).
-/

namespace E047

-- BEGIN SPEC
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false
-- END SPEC

-- BEGIN SPEC
theorem zero_or_succ (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 :=
-- END SPEC
  by
    match n with
    | 0 => exact Or.inl rfl
    | k + 1 => exact Or.inr ⟨k, rfl⟩

-- BEGIN SPEC
theorem exists_swap (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n ∧ p n :=
-- END SPEC
  match h with
  | ⟨n, hp, hq⟩ => ⟨n, hq, hp⟩

-- BEGIN SPEC
theorem or_swap (P Q : Prop) (h : P ∨ Q) : Q ∨ P :=
-- END SPEC
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

-- BEGIN SPEC
theorem isZero_iff (n : Nat) : isZero n = true ↔ n = 0 :=
-- END SPEC
  by
    match n with
    | 0 => simp [isZero]
    | k + 1 => simp [isZero]

end E047

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `match` has one branch per constructor: `0` / `k + 1` for `Nat`, `⟨w, h⟩` for `∃`,
    `.inl` / `.inr` for `∨`. Nested patterns such as `⟨n, hp, hq⟩` work too.
H2. `zero_or_succ` and `isZero_iff`: `by match n with | 0 => … | k + 1 => …`; in each branch
    `isZero` then computes. `exists_swap` and `or_swap`: a term-mode `match h with`.
H3. `or_swap`: `match h with | .inl hp => .inr hp | .inr hq => .inl hq`;
    `zero_or_succ`, second branch: `exact Or.inr ⟨k, rfl⟩`; `isZero_iff` branches: `simp [isZero]`.
-/
